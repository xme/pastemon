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
#
# Todo
# ----
#

use strict;
use Getopt::Long;
use IO::Socket;
use LWP::UserAgent;
use Sys::Syslog;
use POSIX qw(setsid);

my $program = "pastemon.pl";
my $version = "v1.2";
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
my $pidFile = "/var/run/" . $program . ".pid";
my $configfile;
my $syslogFacility = "daemon";
my $dumpDir;
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
	"regex=s"		=> \$configfile,
);

if ($help) {
	print <<__HELP__;
Usage: $0 --regex=filepath [--facility=daemon ] [--ignore-case][--debug] [--help]
		[--cef-destination=fqdn|ip] [--cef-port=<1-65535> [--cef-severity=<1-10>]
                [--dump=/directory]
Where:
--cef-destination : Send CEF events to the specified destination (ArcSight)
--cef-port        : UDP port used by the CEF receiver (default: 514)
--cef-severity    : Generate CEF events with the specified priority (default: 3)
--debug           : Enable debug mode (verbose - do not detach)
--dump            : Save a copy of the pasties in the directory
--facility        : Syslog facility to send events to (default: daemon)
--help            : What you're reading now.
--ignore-case     : Perform case insensitive search
--regex           : Configuration file with regular expressions (send SIGUSR1 to reload)
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

loadRegexFromFile($configfile) || die "Cannot load regex from file $configfile";

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
					undef(%matches);	# Reset the matches regex/counters
					my $i = 0;
					foreach $regex (@regexList) {
						# Search for an exception regex
						my ($preRegex, $postRegex) = split("_EXCLUDE_", $regex);
						$preRegex =~ s/^\s+//; $preRegex =~ s/\s+$//;
						$postRegex =~ s/^\s+//; $postRegex =~ s/\s+$//;
						my $preCount = 0;
						if ($ignoreCase) {
							$preCount += () = $content =~ /$preRegex/gi;
						}
						else {
							$preCount += () = $content =~ /$preRegex/g;
						}
						if ($preCount > 0) {
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
									$matches{$i} = [ ( $preRegex, $preCount ) ];
									$i++;
								}
							}
							else {
								$matches{$i} = [ ( $preRegex, $preCount ) ];
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
						syslogOutput($buffer);
						($cefDestination) && sendCEFEvent($pastie);

						# Save pastie content in the dump directory
						open(DUMP, ">:encoding(UTF-8)", "$dumpDir/$pastie.raw") or die "Cannot write to $dumpDir/$pastie.raw : $!";
						print DUMP "$content";
						close(DUMP);
						push(@seenPasties, $pastie);
					}
				}
				# Wait a random number of seconds to not mess with pastebin.com webmasters
				sleep(int(rand(3)));
			}
		}
	}
	else {
		syslogOutput("Cannot fetch pasties");
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
	my $ua = LWP::UserAgent->new;
	$ua->timeout(10);
	$ua->env_proxy;
	$ua->agent("Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 5.1");
	my $response = $ua->get("http://pastebin.com/archive");
	if ($response->is_success) {
		# Load the pasties into an array
		@pasties = $response->decoded_content =~ /<td class=\"icon\"><a href=\"\/(\w+)\">.+<\/a><\/td>/g;
		return(0);
	}
	syslogOutput("Cannot fetch pasties: " . $response->status_line);
	return 1;
}

#
# Fetch the raw content of a pastie and return its content
#
sub fetchPastie {
	my $pastie = shift;
	my $ua = LWP::UserAgent->new;
	$ua->timeout(10);
	$ua->env_proxy;
	$ua->agent("Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 5.1");
	my $response = $ua->get("http://pastebin.com/raw.php?i=" . $pastie);
	if ($response->is_success) {
		return $response->decoded_content;
	}
	($debug) &&  print STDERR "+++ Cannot fetch pastie $pastie: " . $response->status_line . "\n";
	return "";
}

#
# Load the regular expressions from the configuration file to a Perl array
#
sub loadRegexFromFile {
	my $file = shift;
	die "A configuration file is required" unless defined($file);
	undef @regexList; # Clean up array (if reloaded via SIGUSR1
	open(REGEX_FD, "$file") || die "Cannot open file $file";
	while(<REGEX_FD>) {
		chomp;
		(length > 0) && push(@regexList, $_);
	}
	syslogOutput("Loaded " . @regexList . " regular expressions from " . $file);
	return(1);
}

sub purgeOldPasties {
	my $max = shift;
	while (@seenPasties > $max) {
		delete $seenPasties[0];
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
	syslogOutput("Reloading regular expressions");
	loadRegexFromFile($configfile);
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
	my $i = 0;
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

# Eof
