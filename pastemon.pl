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
#

use strict;
use Getopt::Long;
use IO::Socket;
use LWP::UserAgent;
use HTML::Entities;
use Sys::Syslog;
use Encode;
use WordPress::XMLRPC;
use POSIX qw(setsid);

my $program = "pastemon.pl";
my $version = "v1.6";
my $debug;
my $help;
my $ignoreCase;		# By default respect case in strings search
my $cefDestination;	# Send CEF events to this destination:port
my $cefPort = 514;
my $cefSeverity = 3;
my $caught = 0;
my @pasties;
my @seenPasties;
my $maxPasties = 500;
my @regexList;
my @regexDesc;
my $pidFile = "/var/run/pastemon.pid";
my $configFile;
my $wpConfigFile;
my $proxyConfigFile;
my @proxies;

my $wpSite;		# Wordpress settings
my $wpUser;
my $wpPass;
my $wpCategory;
my $wpTags;

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
	"cef-destination=s"	=> \$cefDestination,
	"cef-port=s"		=> \$cefPort,
	"cef-severity=s"	=> \$cefSeverity,
	"debug"			=> \$debug,
        "dump=s"		=> \$dumpDir,
	"facility=s"		=> \$syslogFacility,
	"help"			=> \$help,
	"ignore-case"		=> \$ignoreCase,
	"pidfile=s"		=> \$pidFile,
	"regex=s"		=> \$configFile,
	"wp-config=s"		=> \$wpConfigFile,
	"proxy-config=s"	=> \$proxyConfigFile,
	"sample=s"		=> \$sampleSize,
);

if ($help) {
	print <<__HELP__;
Usage: $0 --regex=filepath [--facility=daemon ] [--ignore-case][--debug] [--help]
		[--cef-destination=fqdn|ip] [--cef-port=<1-65535> [--cef-severity=<1-10>]
                [--dump=/directory] [--pidfile=file] [--wp-config=file]
                [--proxy-config=file] [--sample=bufferlength]
Where:
--cef-destination : Send CEF events to the specified destination (ArcSight)
--cef-port        : UDP port used by the CEF receiver (default: 514)
--cef-severity    : Generate CEF events with the specified priority (default: 3)
--debug           : Enable debug mode (verbose - do not detach)
--dump            : Save a copy of the pasties in the directory
--facility        : Syslog facility to send events to (default: daemon)
--help            : What you're reading now.
--ignore-case     : Perform case insensitive search
--pidfile         : Location of the PID file (default: /var/run/pastemon.pid)
--proxy-config    : Configuration with proxies to use (random)
--regex           : Configuration file with regular expressions (send SIGUSR1 to reload)
--sample          : Display a sample of match data (# of bytes before and after the mathch)
--wp-config       : Configuration file for Wordpress XMLRPC import
__HELP__
	exit 0;
}

($debug) && print STDERR "+++ Running in foreground.\n";

($cefDestination) && syslogOutput("Sending CEF events to $cefDestination:$cefPort (severity $cefSeverity)");

# Check if the provided dump directory is writable to us
if ($dumpDir) {
	(-w $dumpDir) or die "Directory $dumpDir is not writable: $!";
	syslogOutput("Using $dumpDir as dump directory");
	
}
# Do not allow multiple running instances!
if (-r $pidFile) {
	open(PIDH, "<$pidFile") || die "Cannot read pid file!";
	my $currentpid = <PIDH>;
	close(PIDH);
	die "$program already running (PID $currentpid)";
}

# Verifiy sampleSize format if specified
if ($sampleSize) {
	die "Sample buffer length must be an integer!" if not $sampleSize =~ /\d+/;
	syslogOutput("Dumping $sampleSize bytes samples");
}

# Load a Wordpress config file
if ($wpConfigFile) {
	loadWPConfigFile($wpConfigFile) || die "Cannot load Wordpress configuration from file $wpConfigFile";
	(!$wpSite || !$wpUser || !$wpPass || !$wpCategory) && die "Incomplete Wordpress configuration in $wpConfigFile";
	($sampleSize) || die "A sample buffer length must be given with Wordpress output";
	syslogOutput("Dumping data to $wpSite/xmlrpc.php");
}

loadRegexFromFile($configFile) || die "Cannot load regex from file $configFile";

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
	($proxyConfigFile) && die "The HTTP_PROXY environment variable conflicts with the use of a proxies list";
	syslogOutput("Using detected HTTP proxy: " . $ENV{'HTTP_PROXY'});
}

# Load proxies config file
loadProxyFromFile($proxyConfigFile) || die "Cannot load proxy configuration from file $proxyConfigFile";

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
							my ($preRegex, $postRegex) = split("_EXCLUDE_", $regex);
							my $sampleData;
							my ($startPos, $endPos);
							$preRegex =~ s/^\s+//; $preRegex =~ s/\s+$//;
							$postRegex =~ s/^\s+//; $postRegex =~ s/\s+$//;
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
									if (! $postCount) {
										# No match for $postRegex!
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
	
							if ($dumpDir) {
								# Save pastie content in the dump directory
								open(DUMP, ">:encoding(UTF-8)", "$dumpDir/$pastie.raw") or die "Cannot write to $dumpDir/$pastie.raw : $!";
								print DUMP "$content";
								close(DUMP);
							}

							push(@seenPasties, $pastie);
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
# Download the latest pasties and load them in a Perl array
# (http://pastebin.com/archive)
#
sub fetchLastPasties {
	my $tempProxy;
	my $ua = LWP::UserAgent->new;
	$ua->timeout(10);
	if (@proxies) {
		$tempProxy = selectRandomProxy();
		$ua->proxy('http', $tempProxy);
	}
	else {
		$ua->env_proxy;
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
	$ua->timeout(10);
	if (@proxies) {
		$tempProxy = selectRandomProxy();
		$ua->proxy('http', $tempProxy);
	}
	else {
		$ua->env_proxy;
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
		if (length > 0) {
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
# Load Wordpress configuration
#
sub loadWPConfigFile {
	my $file = shift;
	die "A configuration file is required" unless defined($file);
	open(WPCONFIG_FD, "$file") || die "Cannot open file $file : $!";
	while(<WPCONFIG_FD>) {
		chomp;
		$_=~s/\s//g;
		my ($keyword, $value) = split("=", $_);
		$keyword =~ tr/A-Z/a-z/;
		SWITCH: {
			if ($keyword eq "wp-site") {
				$wpSite = $value;
				last SWITCH;
			}
			if ($keyword eq "wp-user") {
				$wpUser = $value;
				last SWITCH;
			}
			if ($keyword eq "wp-pass") {
				$wpPass = $value;
				last SWITCH;
			}
			if ($keyword eq "wp-category") {
				$wpCategory = $value;
				last SWITCH;
			}
		}
	}
	close(WPCONFIG_FD);
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
	loadRegexFromFile($configFile);
	(@proxies) && loadProxyFromFile($proxyConfigFile);
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
		if ($regexList[$pos] eq $regex) {
			return($regexDesc[$pos]);
		}
	}
	return;
}

#
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

# Eof
