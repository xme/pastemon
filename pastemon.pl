#!/usr/bin/perl
#
# pastemon.pl 
#
# This script runs in the background as a daemon and monitors pastebin.com for
# interesting content (based on regular expressions). Found information is sent
# to syslog
#
# This script is based on the Python script written by Xavier Garcia
# (http://www.shellguardians.com/2011/07/monitoring-pastebin-leaks.html)
#
# Copyright (c) 2012 Xavier Mertens
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
# notice, this list of conditions and the following disclaimer in the
# documentation and/or other materials provided with the distribution.
# 3. Neither the name of copyright holders nor the names of its
# contributors may be used to endorse or promote products derived
# from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
# TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
# PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDERS OR CONTRIBUTORS
# BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.
#
# History
# -------
# See README file

use strict;
use threads;
use threads::shared;
use File::Path; 
use Getopt::Long;
use IO::Socket;
use LWP::UserAgent;
use HTML::Entities;
use Sys::Syslog;
use Encode;
use XML::XPath;
use XML::XPath::XMLParser;
use Net::SMTP;
use POSIX qw(setsid);

# Optional modules
my $haveWordPressXMLRMC = eval "use WordPress::XMLRPC; 1";
my $haveTextJaroWinkler = eval "use Text::JaroWinkler qw(strcmp95); 1";
my $haveIOCompressGzip	= eval "use IO::Compress::Gzip; 1";

use constant PROCESS_URL	=> 1;
use constant PASTEBIN 		=> 0;	# Supported websites
use constant PASTIE 		=> 1;
use constant NOPASTE		=> 2;
use constant PASTESITE		=> 3;

my $program = "pastemon.pl";
my $version = "v1.11";
my $debug;
my $help;
my $ignoreCase;		# By default respect case in strings search
my $cefDestination;	# Send CEF events to this destination:port
my $cefPort = 514;
my $cefSeverity = 3;
my $caught = 0;
my $httpTimeout = 10;	# Default HTTP timeout
my @pasties;
my @seenPasties;
my $maxPasties = 500;
my @regexList;		# List of interesting regex (with the data)
my $pidFile 	= "/var/run/pastemon.pid";
my $configFile	= "/etc/pastemon.conf";		# Main XML configuration file
my $regexFile;		# Regular expressions definitions
my $wpConfigFile;
my $proxyFile;
my @proxies;

my $wpSite;		# Wordpress settings
my $wpUser;
my $wpPass;
my $wpCategory;

my $smtpServer;		# SMTP settings
my $smtpFrom;
my $smtpRecipient;
my $smtpSubject;

my $distanceMin;
my $distanceMaxSize;

my $followUrls;		# Follow URLs found in pastie
my $followMatching;

my $checkPastebin;	# Websites to monitor
my $checkPastie;
my $checkNopaste;
my $checkPastesite;

my $delayPastebin	= 300;	# Delays between pasties fetches
my $delayPastie		= 300;
my $delayNopaste	= 300;
my $delayPastesite	= 300;

my $syslogFacility = "daemon";
my $dumpDir;
my $dumpAll;
my $compressDump;
my $sampleSize;
my %matches;

# Process arguments
my $result = GetOptions(
	"debug"			=> \$debug,
	"help"			=> \$help,
	"config=s"		=> \$configFile,
);

if ($help) {
	print <<__HELP__;
Usage: $0 --config=filepath [--debug] [--help]
Where:
--config : Specify the XML configuration file
--debug  : Enable debug mode (verbose - do not detach)
--help   : What you're reading now.
__HELP__
	exit 0;
}

parseXMLConfigFile($configFile);

($debug) && print STDERR "+++ Running in foreground.\n";

($cefDestination) && syslogOutput("Sending CEF events to $cefDestination:$cefPort (severity $cefSeverity)");

# Do not allow multiple running instances!
if (-r $pidFile) {
	open(PIDH, "<$pidFile") || die "Cannot read pid file!";
	my $currentpid = <PIDH>;
	close(PIDH);
	die "$program already running (PID $currentpid)";
}

loadRegexFromFile($regexFile) || die "Cannot load regex from file $regexFile";

if (!$debug) {
	my $pid = fork;
	die "Cannot fork" unless defined($pid);
	exit(0) if $pid;

	# We are the child
	(POSIX::setsid != -1) or die "setsid failed";
	chdir("/") || die "Cannot changed working directory to /";
	close(STDOUT);
	close(STDOUT);
	close(STDIN);
}

syslogOutput("Running with PID $$");
open(PIDH, ">$pidFile") || die "Cannot write PID file $pidFile: $!";
print PIDH "$$";
close(PIDH);

# Notify if HTTP proxy settings detected
if ($ENV{'HTTP_PROXY'}) {
	($proxyFile) && die "The HTTP_PROXY environment variable conflicts with the use of a proxies list";
	syslogOutput("Using detected HTTP proxy: " . $ENV{'HTTP_PROXY'});
}

my @threads;
my @webSites;
($checkPastebin) && push(@webSites, PASTEBIN);
($checkPastie) && push(@webSites, PASTIE);
($checkNopaste) && push(@webSites, NOPASTE);
($checkPastesite) && push(@webSites, PASTESITE);

# Launch threads based on the number of webistes to monitor
for my $webSite (@webSites) {
	my $t = threads->new(\&mainLoop, $webSite);
	push(@threads, $t);
}

$SIG{'TERM'}	= \&sigHandler;
$SIG{'INT'}	= \&sigHandler;
$SIG{'KILL'}	= \&sigHandler;
$SIG{'USR1'}	= sub {
			foreach my $t (@threads) {
				$t->kill('SIGUSR1');
			}
		      };

# Parent process just waiting for a signal
while(1) {
	sleep(1);
	if ($caught) {
		syslogOutput("Killing my threads");
		foreach my $t (@threads) {
			$t->kill('SIGKILL');
		}
	}
}

exit 0;

# ---------
# Main loop
# ---------
sub mainLoop {
	$SIG{'USR1'}	= \&sigReload; # Handle config reload
	$SIG{'KILL'}    = \&sigHandler;
	my $webSite = shift;
	while(1) {
		my $pastie;
		if (!&fetchLastPasties($webSite)) {
			foreach $pastie (@pasties) {
				exit 0 if ($caught == 1);
				analyzePastie($pastie, PROCESS_URL);
			}
			exit 0 if ($caught == 1);
		}
		purgeOldPasties($maxPasties);

		# Wait some seconds (depending on the website)
		DELAY: {
			$webSite == PASTEBIN	&& do { 
							($debug) && print STDERR "Sleeping $delayPastebin\n"; 
							sleep($delayPastebin); last DELAY; };
			$webSite == PASTIE	&& do {
							($debug) && print STDERR "Sleeping $delayPastie\n";
							sleep($delayPastie); last DELAY; };
			$webSite == NOPASTE	&& do {
							($debug) && print STDERR "Sleeping $delayNopaste\n";
							sleep($delayNopaste); last DELAY; };
			$webSite == PASTESITE	&& do {
							($debug) && print STDERR "Sleeping $delayPastesite\n";
							sleep($delayPastesite); last DELAY; };
		}
	}
}

#
# analyzePastie
#
sub analyzePastie {
	my $pastie = shift or return;
	my $processUrl = shift;
	my $regex;
	if (!grep /$pastie/, @seenPasties) {
		my $content = fetchPastie($pastie);
		if ($content) {
			# If we receive a "slow down" message, follow Pastebin recommandation!
			if ($content =~ /Please slow down/) {
				($debug) &&  print STDERR "+++ Slow down message received. Paused 5 seconds\n";
				sleep(5);
			}
			else {
				undef(%matches);	# Reset the matches regex/counters
				my $i = 0;
				my $regexSearch;
				my $regexInclude;
				my $regexExclude;
				my $regexDesc;
				my $regexCount;
				foreach $regex (@regexList) {
					$regexSearch	= @$regex[0];
					$regexInclude	= @$regex[1];
					$regexExclude	= @$regex[2];
					$regexDesc	= @$regex[3];
					$regexCount	= @$regex[4];
					my $sampleData;
					my ($startPos, $endPos);
					my $preCount = 0;
					if ($ignoreCase) {
						$preCount += () = $content =~ /$regexSearch/mgi;
						$startPos = $-[0];
						$endPos = $+[0];
					}
					else {
						$preCount += () = $content =~ /$regexSearch/mg;
						$startPos = $-[0];
						$endPos = $+[0];
					}
					if ($preCount >= $regexCount) {	
						if ($sampleSize) {
							# Optional: extract a sample of the data
							$startPos = (($startPos - $sampleSize) < 0) ? 0 : ($startPos - $sampleSize);
							$sampleData = encode('UTF8', substr($content, $startPos, ($endPos - $startPos) + $sampleSize));
						}
						# Process "include" regex defined
						if ($regexInclude ne "") {
							my $postCount = 0;
							if ($ignoreCase) {
								$postCount += () = $content =~ /$regexInclude/mgi;
							} else {
								$postCount += () = $content =~ /$regexInclude/mg;
							}
							if ($postCount) {
								# Matches for include $regex
								$matches{$i} = [ ( $regexSearch, $preCount, $sampleData ) ];
								$i++;
							}
						}
						elsif ($regexExclude ne "") {
							my $postCount = 0;
							if ($ignoreCase) {
								$postCount += () = $content =~ /$regexExclude/mgi;
							} else {
								$postCount += () = $content =~ /$regexExclude/mg;
							}
							if (! $postCount) {
								# Matches for exclude $regex
								$matches{$i} = [ ( $regexSearch, $preCount, $sampleData ) ];
								$i++;
							}
						}
						else {
							$matches{$i} = [ ( $regexSearch, $preCount, $sampleData ) ];
							$i++;
						}
					}
				}
				if ($followUrls && $processUrl) {
					$i += processUrls($content);
				}
				if ($i) {
					# Try to find a corresponding pastie?
					if (!FuzzyMatch($content))
					{
						# Generate the results based on matches
						my $buffer = "Found in " . $pastie . " : ";
						my $key;
						for $key (keys %matches) {
							$buffer = $buffer . $matches{$key}[0] . " (" . $matches{$key}[1] . " times) ";
						}
						if ($sampleSize) {
							# Optional: Add sample of data
							my $safeData = $matches{0}[2];
							# Sanitize the data
							$safeData =~ s///g;
							$safeData =~ s/\n/\\n/g;
							$safeData =~ s/\t/\\t/g;
							$buffer = $buffer . "| Sample: " . $safeData;
						}
						syslogOutput($buffer);

						# Generating CEF event (if configured)
						($cefDestination) && sendCEFEvent($pastie);
	
						# Generating blog post (if configured)
						($wpSite) && createBlogPost($pastie);

						# Send SMTP notification (if configured)
						if ($smtpServer) {
							my $smtp = Net::SMTP->new($smtpServer) or die "Cannot create SMTP connection to $smtpServer: $?";
							$smtp->mail($smtpFrom);
							$smtp->to($smtpRecipient);
							$smtp->data();
							my $smtpBody = "To: $smtpRecipient\nSubject: $smtpSubject\n\n";
							for $key (keys %matches) {
								$smtpBody = $smtpBody . "Matched: " . $matches{$key}[0] . " (" . $matches{$key}[1] . " time(s))\n";
							}
							$smtpBody = $smtpBody . "\nSource: " . $pastie . "\n\n" . $content;
							$smtp->datasend($smtpBody);
							$smtp->dataend();
							$smtp->quit();
						}

						# Save pastie content in the dump directory (if configured)
						if ($dumpDir) {
							my $tempPastie = getPastieID($pastie);
							my $tempDir = validateDumpDir($dumpDir); # Generate and create dump directory
							(-d $tempDir) or die "Cannot validate directory $dumpDir: $!";
							open(DUMP, ">:encoding(UTF-8)", "$tempDir/$tempPastie.raw") or die "Cannot write to $tempDir/$tempPastie.raw : $!";
							for $key (keys %matches) {
								print DUMP "Matched: " . $matches{$key}[0] . " (" . $matches{$key}[1] . " time(s))\n";
							}
							print DUMP "\n$content";
							close(DUMP);
							if ($compressDump) { # Compress pastie
								my $in  = "$tempDir/$tempPastie.raw";
								my $out = "$tempDir/$tempPastie.gz";
								use IO::Compress::Gzip qw(gzip);
								if (gzip $in => $out) {
									unlink("$tempDir/$tempPastie.raw");
								}
								else {
									syslogOutput("Cannot compress $tempDir/$tempPastie.raw: $!");
								}
							}
						}

					}
				}
				elsif ($dumpAll && $dumpDir) {
					# Mirroring mode - dump the pastie in all cases
					my $tempPastie = getPastieID($pastie);
					my $tempDir = validateDumpDir($dumpDir);
					(-d $tempDir) or die "Cannot validate directory $tempDir: $!";
					open(DUMP, ">:encoding(UTF-8)", "$tempDir/$tempPastie.raw") or die "Cannot write to $tempDir/$tempPastie.raw : $!";
					print DUMP "\n$content";
					close(DUMP);
					if ($compressDump) { # Compress pastie
						my $in  = "$tempDir/$tempPastie.raw";
						my $out = "$tempDir/$tempPastie.gz";
						use IO::Compress::Gzip qw(gzip);
						if (gzip $in => $out) {
							unlink("$tempDir/$tempPastie.raw");
						}
						else { 
							syslogOutput("Cannot compress $tempDir/$tempPastie.raw: $!");
						}
					}
				}

				# Flag this pastie as "seen"
				push(@seenPasties, $pastie);

				# Wait a random number of seconds to not mess with pastebin.com webmasters
				sleep(int(rand(5)));
			}
		}
	}
}

#
# Search for interesting data in URLs found inside the pastie
#
sub processUrls {
	my $pastie = shift || return 0;
	while ($pastie =~ m,(http.*?://([^\s)\"](?!ttp:))+),g) { # "
		my $url = $&;
		if ($url =~ /$followMatching/gi) { #Process only URLs matching our regex!
                	($debug) && print "+++ Following URL: $url\n";
			my $ua = LWP::UserAgent->new;
			$ua->agent(getRandomUA());
			my $r = $ua->head("$url");
			if ($r->is_success && substr($r->header('Content-Type'), 0, 5) eq "text/") {	# Only process "text"
				analyzePastie($url);
			}
        	}
	}
	return 0;
}

# 
# Load the configuration from provided XML file
#
sub parseXMLConfigFile {
	my $configFile = shift;
	(-r $configFile) || die "Cannot load XML file $configFile: $!";

	($debug) && print STDERR "+++ Loading XML file $configFile.\n";
	my $xml = XML::XPath->new(filename => "$configFile");
	my $buff;

	# Reset settings
	undef $pidFile;
	undef $sampleSize;
	undef $dumpDir;
	undef $dumpAll;
	undef $compressDump;
	undef $proxyFile;
	undef $cefDestination;
	undef $cefPort;
	undef $cefSeverity;
	undef $smtpServer;
	undef $smtpFrom;
	undef $smtpRecipient;
	undef $smtpSubject;
	undef $wpSite;
	undef $wpUser;
	undef $wpPass;
	undef $wpCategory;
	undef $distanceMin;
	undef $distanceMaxSize;
	undef $checkPastebin;
	undef $checkPastie;
	undef $checkNopaste;
        undef $checkPastesite;
	undef $followUrls;
	undef $followMatching;

	# Core Parameters
	my $nodes = $xml->find('/pastemon/core');
	foreach my $node ($nodes->get_nodelist) {
		$buff			= $node->find('ignore-case')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$ignoreCase++;
			($debug) && print STDERR "+++ Non-sensitive search enabled.\n";
		}
		$buff			= $node->find('dump-all')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$dumpAll++;
			($debug) && print STDERR "+++ Dumping all pasties (mirror mode).\n";
		}
		$buff			= $node->find('compress-pasties')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$compressDump++;
			($debug) && print STDERR "+++ Compressing all pasties (mirror mode).\n";
		}
		$pidFile		= $node->find('pid-file')->string_value;
		$regexFile		= $node->find('regex-file')->string_value;
		$sampleSize		= $node->find('sample-size')->string_value;
		$dumpDir		= $node->find('dump-directory')->string_value;
		$proxyFile		= $node->find('proxy-config')->string_value;
		$httpTimeout		= $node->find('http-timeout')->string_value;
		$distanceMin		= $node->find('distance-min')->string_value;
		$distanceMaxSize	= $node->find('distance-max-size')->string_value;
	}

	# Monitored websites
	my $nodes = $xml->find('/pastemon/websites');
	foreach my $node ($nodes->get_nodelist) {
		$buff			= $node->find('pastebin')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$checkPastebin++;
			($debug) && print STDERR "+++ pastebin.com monitoring activated.\n";
		}
		$buff                   = $node->find('pastie')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$checkPastie++;
			($debug) && print STDERR "+++ pastie.com monitoring activated.\n";
		}
		$buff                   = $node->find('nopaste')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$checkNopaste++;
			($debug) && print STDERR "+++ nopaste.me monitoring activated.\n";
		}
		$buff			= $node->find('pastesite')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$checkPastesite++;
			($debug) && print STDERR "+++ pastesite.com monitoring activated.\n";
		}
		$delayPastebin	= $node->find('pastebin-delay')->string_value;
		$delayPastie	= $node->find('pastie-delay')->string_value;
		$delayNopaste	= $node->find('nopaste-delay')->string_value;
		$delayPastesite	= $node->find('pastesite-delay')->string_value;
	}

	# Follow URLs
	my $nodes = $xml->find('/pastemon/urls');
	foreach my $node ($nodes->get_nodelist) {
		$buff			= $node->find('follow')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$followUrls++;
			($debug) && print STDERR "+++ Follow URLs feature activated.\n";
		}
		$followMatching		= $node->find('matching')->string_value;
	}

	# CEF Parameters
	my $nodes = $xml->find('/pastemon/cef-output');
	foreach my $node ($nodes->get_nodelist) {
		$cefDestination		= $node->find('destination')->string_value;
		$cefPort		= $node->find('port')->string_value;
		$cefSeverity		= $node->find('severity')->string_value;
	}

	# Syslog Parameters
	my $nodes = $xml->find('/pastemon/syslog-output');
	foreach my $node ($nodes->get_nodelist) {
		$syslogFacility		= $node->find('facility')->string_value;
	}

	# Wordpress Parameters
	my $nodes = $xml->find('/pastemon/wordpress-output');
	foreach my $node ($nodes->get_nodelist) {
		$wpSite			= $node->find('site')->string_value;
		$wpUser			= $node->find('user')->string_value;
		$wpPass			= $node->find('password')->string_value;
		$wpCategory		= $node->find('category')->string_value;
	}

	# SMTP Parameters
	my $nodes = $xml->find('/pastemon/smtp-output');
	foreach my $node ($nodes->get_nodelist) {
		$smtpServer		= $node->find('smtp-server')->string_value;
		$smtpFrom		= $node->find('from')->string_value;
		$smtpRecipient		= $node->find('recipient')->string_value;
		$smtpSubject		= $node->find('subject')->string_value;
	}

	# ---------------------
	# Parameters validation
	# ---------------------

	# Check if the provided dump directory is writable to us
	if ($dumpDir) {
		# (-w $dumpDir) or die "Directory $dumpDir is not writable: $!";
		syslogOutput("Using $dumpDir as dump directory");
	}

	# Compress dumped pasties?
	if ($compressDump) {
		if ($haveIOCompressGzip) { # Module IO::Compress::Gzip installed?
			if (!$dumpDir) {
				syslogOutput("Option compress-pasties disabled: No dump directory defined");
				undef $compressDump
			}
		}
		else {
			syslogOutput("Option compress-pasties disabled: IO::Compress:Gzip not installed");
			undef $compressDump;
		}
	}

	# Dumping all pasties requires a dump directory
	if ($dumpAll && !$dumpDir) {
		syslogOutput("No dump directory specified");
	}

	# Verifiy sampleSize format if specified
	if ($sampleSize) {
		die "Sample buffer length must be an integer!" if not $sampleSize =~ /\d+/;
		syslogOutput("Dumping $sampleSize bytes samples");
	}

	# Verify the HTTP timeout if specified
	if ($httpTimeout) {
		die "HTTP timeout must be an integer!" if not $httpTimeout =~ /\d+/;
		syslogOutput("HTTP timeout: $httpTimeout seconds");
	}

	# Verify Wordpress config
	if ($wpSite) {
		if ($haveWordPressXMLRMC) { # Module WordPress::XMLRPC installed?
			(!$wpSite || !$wpUser || !$wpPass || !$wpCategory) && die "Incomplete Wordpress configuration";
			($sampleSize) || die "A sample buffer length must be given with Wordpress output";
			syslogOutput("Dumping data to $wpSite/xmlrpc.php");
		} 
		else {
			syslogOutput("Wordpress configuration disabled: Wordpress::XMLRPC not installed");
			undef $wpSite;
		}
	}

	# Verify SMTP config
	if ($smtpServer) {
		(!$smtpServer || !$smtpFrom || !$smtpRecipient || !$smtpSubject) && die "Incomplete SMTP configuration";
		my $smtp = Net::SMTP->new($smtpServer) or die "Cannot use SMTP server $smtpServer: $?";
		$smtp->quit();
		syslogOutput("Sending SMTP notifications to <".$smtpRecipient.">");
	}

	# Load proxies
	if ($proxyFile) {
		(-r $proxyFile) or die "Cannot read proxy configuration file $proxyFile: $!";
		loadProxyFromFile($proxyFile) || die "Cannot load proxies from file $proxyFile";
	}

	# Distance
	if ($distanceMin) {
		if ($haveTextJaroWinkler) { # Module Text::JaroWinkler installed?
			(!$dumpDir) && die "A dump directory must be configured to use the distance check";
			($distanceMin > 0 && $distanceMin < 1) or die "Minimum distance must be between 0 and 1";
			if ($distanceMaxSize) {
				die "Distance max size must be an integer!" if not $distanceMaxSize =~ /\d+/;
				syslogOutput("Enabled duplicate detection with distance of $distanceMin (size limit: $distanceMaxSize bytes)");
			} else {
				syslogOutput("Enabled duplicate detection with distance of $distanceMin");
			}
		}
		else {
			syslogOutput("Distance configuration disabled: Text::JaroWinkler not installed");
			undef $distanceMin;
		}
	}

	# Follow URL
	if ($followUrls && !$followMatching) {
		syslogOutput("Warning: No regex defined to match URLs");
		$followMatching = ".*";	# Match everything
	}

	return;
}

#
# Download the latest pasties and load them in a Perl array
# (http://pastebin.com/archive)
#
sub fetchLastPasties {
	my $webSite = shift;
	my $tempProxy;
	my $ua = LWP::UserAgent->new;
	$ua->timeout($httpTimeout);
	if (@proxies) {
		$tempProxy = selectRandomProxy();
		$ua->proxy('http', $tempProxy);
	}
	else {
		($ENV{'HTTP_PROXY'}) && $ua->env_proxy;
	}
	$ua->agent(getRandomUA());

	undef @pasties;	# Reset the array first!

	# www.pastebin.com
	if ($webSite == PASTEBIN) {
		($debug) && print STDERR "Loading new pasties from pastebin.com.\n";
		my $response = $ua->get("http://pastebin.com/archive");
		if ($response->is_success) {
			# Load the pasties into an array
			# @pasties = $response->decoded_content =~ /<td class=\"icon\"><a href=\"\/(\w+)\">.+<\/a><\/td>/g;
			# New format (2012/02/19):
			my @tempPasties = $response->decoded_content =~ /<a href=\"\/(\w{8})\">.+<\/a><\/td>/g;
			# Append the complete URL
			foreach my $p (@tempPasties) {
				$p = 'http://pastebin.com/raw.php?i=' . $p;
			}
			push(@pasties, @tempPasties);
		}
		else {
			syslogOutput("Cannot fetch www.pastebin.com: " . $response->status_line);
			# If cannot fetch pastie and we use proxies, disable the current one!
			(@proxies) && disableProxy($tempProxy);
			return 1;
		}
	}
	elsif ($webSite == PASTIE) {
		#($debug) && print STDERR "Loading new pasties from pastie.org.\n";
		my $response = $ua->get("http://pastie.org/pastes");
		if ($response->is_success) {
			my @tempPasties = $response->decoded_content =~ /<a href=\"(http:\/\/pastie.org\/pastes\/\d{7})\">/g;
			# Append the complete URL
			foreach my $p (@tempPasties) {
				$p = $p . '/download';
			}
			push(@pasties, @tempPasties);
		}
		else {
			syslogOutput("Cannot fetch www.pastie.org: " . $response->status_line);
			# If cannot fetch pastie and we use proxies, disable the current one!
			(@proxies) && disableProxy($tempProxy);
			return 1;
		}
	}
	elsif ($webSite == NOPASTE) {
		#($debug) && print STDERR "Loading new pasties from nopaste.me.\n";
		my $response = $ua->get("http://nopaste.me/recent");
		if ($response->is_success) {
			my @tempPasties = $response->decoded_content =~ /<a href=\"http:\/\/nopaste.me\/paste\/([a-z0-9]+)\">/ig;
			# Append the complete URL
			foreach my $p (@tempPasties) {
				$p = 'http://nopaste.me/raw/' . $p . '.txt';
			}
			push(@pasties, @tempPasties);
		}
		else {
			syslogOutput("Cannot fetch nopaste.me: " . $response->status_line);
			# If cannot fetch pastie and we use proxies, disable the current one!
			(@proxies) && disableProxy($tempProxy);
			return 1;
		}
	}
	elsif ($webSite == PASTESITE) {
		($debug) && print STDERR "Loading new pasties from pastesite.com.\n";
		my $response = $ua->get("http://pastesite.com/recent");
		if ($response->is_success) {
			my @tempPasties = $response->decoded_content =~ /<a href=\"(\d+)\" title=\"View this Paste/ig;
			# Append the complete URL
			foreach my $p (@tempPasties) {
				$p = 'http://pastesite.com/' . $p;
			}
			push(@pasties, @tempPasties);
		}
		else {
			syslogOutput("Cannot fetch pastesite.com: " . $response->status_line);
			# If cannot fetch pastie and we use proxies, disable the current one!
			(@proxies) && disableProxy($tempProxy);
			return 1;
		}
	}
 	else {
		die "Unknown website constant: $webSite";
	}

	# DEBUG
	#foreach my $p (@pasties) {
	#	print "DEBUG: $p\n";
	#}
	return 0;
}

#
# Fetch the raw content of a pastie and return its content
#
sub fetchPastie {
	my $tempProxy;
	my $pastie = shift;
	my $ua = LWP::UserAgent->new;
	$ua->timeout($httpTimeout);
	if (@proxies) {
		$tempProxy = selectRandomProxy();
		$ua->proxy('http', $tempProxy);
	}
	else {
		($ENV{'HTTP_PROXY'}) && $ua->env_proxy;
	}
	$ua->agent(getRandomUA());
	my $response = $ua->get("$pastie");
	if ($response->is_success) {
		# Hack for pastesite.com: Extract data from the <textarea> </textarea>
		# (To bypass the <continue> button)
		if ($pastie =~ /http:\/\/pastesite.com/) {
			if ($response->decoded_content =~ /\<textarea .*\>(.*)\<\/textarea\>/igs) {
				my $pastesiteContent = $1;
				return $pastesiteContent;
			}
		}
		else {
			return $response->decoded_content;
		}
	}
	($debug) &&  print STDERR "+++ Cannot fetch pastie $pastie: " . $response->status_line . "\n";

	# If cannot fetch pastie and we use proxies, disable the current one!
	(@proxies) && disableProxy($tempProxy);
	return "";
}

#
# Load the regular expressions from the configuration file to a Perl array
#
sub loadRegexFromFile {
	my $file = shift;
	die "A configuration file is required" unless defined($file);
	undef @regexList; # Clean up array (if reloaded via SIGUSR1
	( -r "$file") || die "Cannot open file $file: $!";
	my $xp = XML::XPath->new( filename => "$file");
	my $ns = $xp->find('/config/regex');
	foreach my $n ($ns->get_nodelist) {
		my @r;
		push(@r,	$n->find('search')->string_value);
		push(@r,	$n->find('include')->string_value);
		push(@r,	$n->find('exclude')->string_value);
		push(@r,	$n->find('description')->string_value);
		if ($n->find('count')->string_value ne "") {
			push(@r,$n->find('count')->string_value);
		} else {
			push(@r, "1");
		}
		push(@regexList, [ @r ]);
	}
	syslogOutput("Loaded " . @regexList . " regular expressions from " . $file);
	return(1);
}

#
# Load proxies from the configuration file
#
sub loadProxyFromFile {
	my $file = shift;
	return(1) unless defined($file);
	open(PROXY_FD, "$file") || die "Cannot open file $file : $!";
	while(<PROXY_FD>) {
		chomp;
		(length > 0) && push(@proxies, 'http://'.$_);
	}
	close(PROXY_FD);
	(@proxies) || die "No proxies read from $file";
	syslogOutput("Loaded " . @proxies . " proxies from " . $file);
	return(1);
}

#
# Return a random proxy from the loaded list
#
sub selectRandomProxy {
	my $randomIdx = rand($#proxies);
	($debug) && print STDERR "+++ Using proxy: " . $proxies[$randomIdx] . "\n";
	return $proxies[$randomIdx];
}

#
# Remove a faulty proxy from the proxies array
#
sub disableProxy {
	my $badProxy = shift;
	return unless defined($badProxy);
	my $p;
	my $i = 0;
	foreach $p (@proxies) {
		$i++;
		if ($p eq $badProxy) { last; }
	}
	# delete $proxies[$i]; -- DEPRECATED
	splice @proxies, $i, 1;
	syslogOutput("Disabled unreliable proxy " . $badProxy . " (" . @proxies . ' active proxies)');
}

sub purgeOldPasties {
	my $max = shift;
	while (@seenPasties > $max) {
		#delete $seenPasties[0]; -- DEPRECATED
		splice @seenPasties, 0, 1;
	}	
	return;
}

#
# Handle a proper process cleanup when a signal is received
#
sub sigHandler {
	syslogOutput("Received signal. Exiting.");
	unlink($pidFile) if (-r $pidFile);
	$caught = 1;
}

#
# Reload configuration files
#
sub sigReload {
	syslogOutput("Reloading config files (Thread ID " . threads->tid() . ")");
	parseXMLConfigFile($configFile);
	loadRegexFromFile($regexFile);
	(@proxies) && loadProxyFromFile($proxyFile);
	return;
}

#
# Send Syslog message using the defined facility
#
sub syslogOutput {
        my $msg = shift or return(0);
	if ($debug) {
		print STDERR "+++ $msg\n";
	}
	else {
		openlog($program, 'pid', $syslogFacility);
		syslog('info', '%s', $msg);
		closelog();
	}
}

#
# Send a CEF syslog packet to an ArcSight device/application
#
sub sendCEFEvent {
	my $pastie = shift;
	# Syslog data format must be "Jul 10 10:11:23"
	my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime(time);
	my @months = ("Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec");
	my $timeStamp = sprintf("%3s %2d %02d:%02d:%02d", $months[$mon], $mday, $hour, $min, $sec);
	my $buffer = sprintf("<%d>%s CEF:0|%s|%s|%s|regex-match|One or more regex matched|%d|request=%s destinationDnsDomain=pastebin.com msg=Interesting data has been found on pastebin.com. ", 
			29,
			$timeStamp,
			"blog.rootshell.be",
			$program,
			$version,
			$cefSeverity,
			$pastie
	);
 	my $key;
	my $i = 1;
	for $key (keys %matches) {
		$buffer = $buffer . "cs" . $i . "=" . $matches{$key}[0] . " cs" . $i . "Label=Regex". $i . "Name cn" . $i . "=" . $matches{$key}[1]. " cn" . $i . "Label=Regex" . $i . "Count ";
		if (++$i > 6) {
			syslogOutput("Maximum 6 matching regex can be logged");
			last;
		}
	}

	# Ready to send the packet!
	my $sock = new IO::Socket::INET(PeerAddr => $cefDestination,
					PeerPort => $cefPort,
					Proto => 'udp',
					Timeout => 1) or die 'Could not create socket: $!';
	$sock->send($buffer) or die "Send UDP packet error: $!";
}

#
# Return the description corresponding to a regex
#
sub getRegexDesc {
	my $regex = shift;
	return unless defined($regex);
	foreach my $r (@regexList) {
		if ($regex eq @$r[0]) {
			return(@$r[3]);
		}
	}
	return;
}

#
# Create a Wordpress blog post
#
sub createBlogPost {
	my $pastie = shift;
	
	my $key;
	my $title;
	my $buffer;
	my $tags = "";

	# Generate tag based on the URL
	if ($pastie =~ /pastebin\.com/) {
		$tags = 'pastebin.com,';
	}
	elsif ($pastie =~ /pastie\.org/) {
		$tags = 'pastie.org,';
	}
	elsif ($pastie =~ /nopaste\.me/) {
		$tags = 'nopaste.me,';
	}
	elsif($pastie =~ /pastesite\.com/) {
		$tags = 'pastesite.com,';
	}

	for $key (keys %matches) {
		if (!$title) {
			$title = 'Potential leak of data: ' . getRegexDesc($matches{$key}[0]);
		}
		$buffer = $buffer . 'Detected ' . $matches{$key}[1] . ' occurrence(s) of \'' . $matches{$key}[0] . '\':<br>';
		$buffer = $buffer . '<pre>' . encode_entities($matches{$key}[2]) . '</pre><p>';
		# Populate Wordpress tags
		$tags = $tags . getRegexDesc($matches{$key}[0]) . ',';
	}
	$buffer = $buffer . 'Source: <a href="' . $pastie . '">' . $pastie . '</a><br>';
	# Prepare the XML request
	my $o = WordPress::XMLRPC->new;
	$o->username($wpUser);
	$o->password($wpPass);
	$o->proxy('http://' . $wpSite . '/xmlrpc.php');
	if (!$o->server()) {
		syslogOutput("Cannot connect to the Wordpress blog");
		return;
	}

	my $hashref = {
		'title' 		=> $title,
		'categories'		=> [ $wpCategory ],
		'description'		=> $buffer,
		'mt_keywords'		=> $tags,
		'mt_allow_comments'	=> 0,
	};
	# WordPress::XMLRPC does not handle exceptions properly.
	# Eval will catch runtime errors or die() and report the
	# error properly (into $@)
	my $ret = eval {
		my $ID = $o->newPost($hashref, 1);
	};
	if (!$ret) {
		syslogOutput("Cannot post Wordpress article: $@");
	}
	return;
}

#
# Perl trim function to remove whitespace from the start and end of the string
#
sub trim($) {
	my $string = shift;
	$string =~ s/^\s+//;
	$string =~ s/\s+$//;
	return $string;
}

#
# Compare a pastie to the already loaded ones using the Jaro Winkler algorithm
# See http://en.wikipedia.org/wiki/Jaro%E2%80%93Winkler_distance
#
sub FuzzyMatch {
	my $newContent = shift;
	my $timeIn = time();

	# Is this feature enabled?
	(!$distanceMin) && return 0;

	# A dump directory must be configured!
	(!$newContent || !$dumpDir) && return 0;

	# Ignore content if size above configured limit (performance)
	(length($newContent) > $distanceMaxSize) && return 0;

	foreach my $pastie (@seenPasties) {
		my $tempPastie = getPastieID($pastie);
		my $tempDir = validateDumpDir($dumpDir);
		if (open(FD, "$tempDir/$tempPastie.raw")) {
			my $buffer = do { local $/; <FD> };
			close(FD);
			# Remove the 2 first lines
 			$buffer =~ /^Matched: .*\n\n(.*)/s;
			$buffer = $1;
			if (length($buffer) > 0) { # Bug fix 2012/07/16: Only process "matched" pasties!
				my $distance = strcmp95($newContent, $buffer, length($newContent), TOUPPER => 1, HIGH_PROB => 0);
				if ($distance > $distanceMin) {
					syslogOutput("Potential duplicate content found with pastie $pastie (distance: $distance)");
					return 1;
				}
			}
		}
	}
	my $timeOut = time();
	$timeOut -= $timeIn;
	($debug) && print STDERR "+++ Time: " . $timeOut . "\n";
	return 0;
}

#
# Build the dump directory based on macro and create it
#
sub validateDumpDir {
	my $dir = shift;
	(!$dir) && return "";

	# Replace macro-% by correct values. Supported:
	# %Y : Year
	# %M : Month
	# %D : Day
	# %H : Hour
	my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime(time);
	$year+=1900;
	$mon  = sprintf("%02d", ++$mon);
	$mday = sprintf("%02d", $mday);
	$hour = sprintf("%02d", $hour);
	$dir =~ s/\%Y/$year/g;
	$dir =~ s/\%M/$mon/g;
	$dir =~ s/\%D/$mday/g;
	$dir =~ s/\%H/$hour/g;
	if (!(-d $dir)) {
		if (!mkpath("$dir")) {
			# If mkpath() failed, re-check the directory
			# (Could have been created by another threat!
			(-d $dir) && return $dir;
			syslogOutput("mkdir(\"$dir\") failed: $!");
			return "";
		}
	}
	return $dir;
}

# 
# Extract the pastie from an URL:
# pastebin.com: pastebin.com/raw.php?i=(XXX)
# pastie.org: pastie.org/pastes/(XXX)/download
#
sub getPastieID {
	my $pastie = shift or return "";
	if ($pastie =~ /pastebin\.com\/raw\.php\?i=(\w+)/) {
		return $1;
	}
	if ($pastie =~ /pastie\.org\/pastes\/(\d+)\/download/) {
		return $1;
	}
	return "";
}

#
# Return a random User-Agent
# (Feel free to add or create yours)
#
sub getRandomUA {
	my @UA = ( 
		"Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 5.1",
		"Opera/9.20 (Windows NT 6.0; U; en)",
		"Googlebot/2.1 ( http://www.googlebot.com/bot.html)",
		"Mozilla/5.0 (Windows; U; Windows NT 5.1; en-US; rv:1.7.5) Gecko/20060127 Netscape/8.1",
		"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_7_4) AppleWebKit/536.5 (KHTML, like Gecko) Chrome/19.0.1084.56 Safari/536.5",
		"Mozilla/5.0 (compatible; MSIE 9.0; Windows NT 6.1; Trident/5.0)",
		"Mozilla/5.0 (iPhone; CPU iPhone OS 5_1_1 like Mac OS X) AppleWebKit/534.46 (KHTML, like Gecko) Version/5.1 Mobile/9B206 Safari/7534.48.3",
		"Mozilla/5.0 (Macintosh; Intel Mac OS X 10.6; rv:12.0) Gecko/20100101 Firefox/12.0",
		"Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; SV1; FunWebProducts; .NET CLR 1.1.4322; PeoplePal 6.2)",
		"Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:12.0) Gecko/20100101 Firefox/12.0"
	);
	my $rnd = rand(@UA);
	return $UA[$rnd];
}

# Eof
