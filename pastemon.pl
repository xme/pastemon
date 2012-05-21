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
# 2012/01/17	Firt version released
# 2012/01/20	Added '--dump' configuration switch
# 2012/01/21	Fixed a bug with case sensitivity search
# 2012/01/23	Added support for "excluded" regular expressions
# 2012/01/26	Added '--pidfile' configuration switch
#		Added '--sample' configuration switch
# 2012/01/30	Bug fix with CEF events (index starting at 0)
# 2012/02/15	Added notification of proxy usage
# 2012/02/19	Adapted regex to mach pasties in the new site layout
# 2012/02/21	Added detection of pastebin "slow down" message
# 2012/03/09	Added support for Wordpress XMLRPC and support for proxy randomization
# 2012/04/08	Added support for "included" regular expressions
# 2012/04/13	Fixed in bug in getRegexDesc()
# 2012/04/20	Added support for comments ('#') in the regex configuration file
# 2012/05/11	Moved configuration parameters from command line switches to an XML file
#		Added matching regex in dump files
#		Added SMTP notifications
# 2012/05/15	Added distance check to detect duplicate pasties (using Jaro-Winkler algorithm)
#

use strict;
use Getopt::Long;
use IO::Socket;
use LWP::UserAgent;
use HTML::Entities;
use Sys::Syslog;
use Encode;
use WordPress::XMLRPC;
use XML::XPath;
use XML::XPath::XMLParser;
use Net::SMTP;
use POSIX qw(setsid);
use Text::JaroWinkler qw(strcmp95);

my $program = "pastemon.pl";
my $version = "v1.7";
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
my @regexList;
my @regexDesc;
my $pidFile = "/var/run/pastemon.pid";
my $configFile;		# Main XML configuration file
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

my $syslogFacility = "daemon";
my $dumpDir;
my $sampleSize;
my %matches;

$SIG{'TERM'}	= \&sigHandler;
$SIG{'INT'}	= \&sigHandler;
$SIG{'KILL'}	= \&sigHandler;
$SIG{'USR1'}	= \&sigReload;

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

# ---------
# Main loop
# ---------

while(1) {
	my $pastie;
	my $regex;
	if (!&fetchLastPasties) {
		foreach $pastie (@pasties) {
			exit 0 if ($caught == 1);
			if (!grep /$pastie/, @seenPasties) {
				my $content = fetchPastie($pastie);
				if ($content) {
					# If we receive a "slow down" message, follow Pastin recommandation!
					if ($content =~ /Please slow down/) {
						($debug) &&  print STDERR "+++ Slow down message received. Paused 5 seconds\n";
						sleep(5);
					}
					else {
						undef(%matches);	# Reset the matches regex/counters
						my $i = 0;
						foreach $regex (@regexList) {
							# Search for an exception regex
							my ($preRegex, $postRegex) = split(/_EXCLUDE_|_INCLUDE_/, $regex);
							$preRegex = trim($preRegex);	# Remove leading/trailing spaces
							$postRegex = trim($postRegex);
							my $sampleData;
							my ($startPos, $endPos);
							my $preCount = 0;
							if ($ignoreCase) {
								$preCount += () = $content =~ /$preRegex/gi;
								$startPos = $-[0];
								$endPos = $+[0];
							}
							else {
								$preCount += () = $content =~ /$preRegex/g;
								$startPos = $-[0];
								$endPos = $+[0];
							}
							if ($preCount > 0) {
								if ($sampleSize) {
									# Optional: extract a sample of the data
									$startPos = (($startPos - $sampleSize) < 0) ? 0 : ($startPos - $sampleSize);
									$sampleData = encode('UTF8', substr($content, $startPos, ($endPos - $startPos) + $sampleSize));
								}
								# If exception defined, search for NON matches
								if ($postRegex) {
									my $postCount = 0;
									if ($ignoreCase) {
										$postCount += () = $content =~ /$postRegex/gi;
									}
									else {
										$postCount += () = $content =~ /$postRegex/g;
									}
									if ((! $postCount && $regex =~ /_EXCLUDE_/) ||
									    (  $postCount && $regex =~ /_INCLUDE_/)) {
										# No match for $postRegex with _EXCLUDE_ keyword or
										# Matches for $postRegex with _INCLUDE_ keyword
										$matches{$i} = [ ( $preRegex, $preCount, $sampleData ) ];
										$i++;
									}
								}
								else {
									$matches{$i} = [ ( $preRegex, $preCount, $sampleData ) ];
									$i++;
								}
							}
						}
						if ($i) {
							# Try to find a corresponding pastie?
							if (!FuzzyMatch($content))
							{
								# Generate the results based on matches
								my $buffer = "Found in http://pastebin.com/raw.php?i=" . $pastie . " : ";
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
									my $smtp = Net::SMTP->new($smtpServer);
									$smtp->mail($smtpFrom);
									$smtp->to($smtpRecipient);
									$smtp->data();
									my $smtpBody = "To: $smtpRecipient\nSubject: $smtpSubject\n\n";
									for $key (keys %matches) {
										$smtpBody = $smtpBody . "Matched: " . $matches{$key}[0] . " (" . $matches{$key}[1] . " time(s))\n";
									}
									$smtpBody = $smtpBody . "\n" . $content;
									$smtp->datasend($smtpBody);
									$smtp->dataend();
									$smtp->quit();
								}

								# Save pastie content in the dump directory (if configured)
								if ($dumpDir) {
									open(DUMP, ">:encoding(UTF-8)", "$dumpDir/$pastie.raw") or die "Cannot write to $dumpDir/$pastie.raw : $!";
									for $key (keys %matches) {
										print DUMP "Matched: " . $matches{$key}[0] . " (" . $matches{$key}[1] . " time(s))\n";
									}
									print DUMP "\n$content";
									close(DUMP);
								}

								push(@seenPasties, $pastie);
							}
						}
						# Wait a random number of seconds to not mess with pastebin.com webmasters
						sleep(int(rand(5)));
					}
				}
			}
		}
		exit 0 if ($caught == 1);
	}
	purgeOldPasties($maxPasties);
	# Wait a random number of seconds to not mess with pastebin.com webmasters
	sleep(int(rand(5)));
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

	# Core Parameters
	my $nodes = $xml->find('/pastemon/core');
	foreach my $node ($nodes->get_nodelist) {
		$buff			= $node->find('ignore-case')->string_value;
		if (lc($buff) eq "yes" || $buff eq "1") {
			$ignoreCase++;
			($debug) && print STDERR "+++ Non-sensitive search enabled.\n";
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
		(-w $dumpDir) or die "Directory $dumpDir is not writable: $!";
		syslogOutput("Using $dumpDir as dump directory");
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
		(!$wpSite || !$wpUser || !$wpPass || !$wpCategory) && die "Incomplete Wordpress configuration";
		($sampleSize) || die "A sample buffer length must be given with Wordpress output";
		syslogOutput("Dumping data to $wpSite/xmlrpc.php");
	}

	# Verify SMTP config
	if ($smtpServer) {
		(!$smtpServer || !$smtpFrom || !$smtpRecipient || !$smtpSubject) && die "Incomplete SMTP configuration";
		syslogOutput("Sending SMTP notifications to <".$smtpRecipient.">");
	}

	# Load proxies
	if ($proxyFile) {
		(-r $proxyFile) or die "Cannot read proxy configuration file $proxyFile: $!";
		loadProxyFromFile($proxyFile) || die "Cannot load proxies from file $proxyFile";
	}

	# Distance
	if ($distanceMin) {
		(!$dumpDir) && die "A dump directory must be configured to use the distance check";
		($distanceMin > 0 && $distanceMin < 1) or die "Minimum distance must be between 0 and 1";
		if ($distanceMaxSize) {
			die "Distance max size must be an integer!" if not $distanceMaxSize =~ /\d+/;
			syslogOutput("Enabled duplicate detection with distance of $distanceMin (size limit: $distanceMaxSize bytes)");
		} else {
		syslogOutput("Enabled duplicate detection with distance of $distanceMin");
		}
	}

	return;
}

#
# Download the latest pasties and load them in a Perl array
# (http://pastebin.com/archive)
#
sub fetchLastPasties {
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
	$ua->agent("Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 5.1");
	my $response = $ua->get("http://pastebin.com/archive");
	if ($response->is_success) {
		# Load the pasties into an array
		# @pasties = $response->decoded_content =~ /<td class=\"icon\"><a href=\"\/(\w+)\">.+<\/a><\/td>/g;
		# New format (2012/02/19):
		@pasties = $response->decoded_content =~ /<a href=\"\/(\w{8})\">.+<\/a><\/td>/g;
		return(0);
	}
	syslogOutput("Cannot fetch pasties: " . $response->status_line);
	# If cannot fetch pastie and we use proxies, disable the current one!
	(@proxies) && disableProxy($tempProxy);
	return 1;
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
	$ua->agent("Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 5.1");
	my $response = $ua->get("http://pastebin.com/raw.php?i=" . $pastie);
	if ($response->is_success) {
		return $response->decoded_content;
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
	undef @regexDesc;
	open(REGEX_FD, "$file") || die "Cannot open file $file : $!";
	while(<REGEX_FD>) {
		chomp;
		if (length > 0 && !($_ =~ /^#/)) {
			# Default format regex<TAB>description
			my ($regex, $desc) = split(/[\t]+/, $_);
			push(@regexList, $regex);
			push(@regexDesc, $desc);
		}
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

sub sigReload {
	syslogOutput("Reloading config files");
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
	my $buffer = sprintf("<%d>%s CEF:0|%s|%s|%s|regex-match|One or more regex matched|%d|request=http://pastebin.com/raw.php?i=%s destinationDnsDomain=pastebin.com msg=Interesting data has been found on pastebin.com. ", 
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
	my $pos;
	for our $pos (0 .. $#regexList) {
		my ($preRegex, $postRegex) = split(/_EXCLUDE_|_INCLUDE_/, $regexList[$pos]);
		$preRegex = trim($preRegex);
		if ($preRegex eq $regex) {
			return($regexDesc[$pos]);
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
	my $tags = 'pastebin,';
	for $key (keys %matches) {
		if (!$title) {
			$title = 'Potential leak of data: ' . getRegexDesc($matches{$key}[0]);
		}
		$buffer = $buffer . 'Detected ' . $matches{$key}[1] . ' occurrence(s) of \'' . $matches{$key}[0] . '\':<br>';
		$buffer = $buffer . '<pre>' . encode_entities($matches{$key}[2]) . '</pre><p>';
		# Populate Wordpress tags
		$tags = $tags . getRegexDesc($matches{$key}[0]) . ',';
	}
	$buffer = $buffer . 'Source: <a href="http://pastebin.com/raw.php?i=' . $pastie . '">pastebin.com/raw.php?i=' . $pastie . '</a><br>';
	# Prepare the XML request
	my $o = WordPress::XMLRPC->new;
	$o->username($wpUser);
	$o->password($wpPass);
	$o->proxy('http://' . $wpSite . '/xmlrpc.php');
	if (!$o->server()) {
		syslogOutput("Cannot create the Wordpress blog post");
		return;
	}

	my $hashref = {
		'title' 		=> $title,
		'categories'		=> [ $wpCategory ],
		'description'		=> $buffer,
		'mt_keywords'		=> $tags,
		'mt_allow_comments'	=> 0,
	};
	my $ID = $o->newPost($hashref, 1);
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
		open(FD, "$dumpDir/$pastie.raw") || die "Cannot read dumped pastie $pastie: $!";
		my $buffer = do { local $/; <FD> };
		close(FD);
		# Remove the 2 first lines
 		$buffer =~ /^Matched: .*\n\n(.*)/s;
		$buffer = $1;
		my $distance = strcmp95($newContent, $buffer, length($newContent), TOUPPER => 1, HIGH_PROB => 0);
		if ($distance > $distanceMin) {
			syslogOutput("Potential duplicate content found with pastie $pastie (distance: $distance)");
			return 1;
		}
	}
	my $timeOut = time();
	$timeOut -= $timeIn;
	($debug) && print STDERR "+++ Time: " . $timeOut . "\n";
	return 0;
}

# Eof
