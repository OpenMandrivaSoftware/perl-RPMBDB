use strict;
use ExtUtils::MakeMaker;

my $ldflags = `pkg-config --libs rpm`;
chomp($ldflags);
$ldflags .= " -lrpmdb";
my $includes = `pkg-config --cflags-only-I rpm`;
my $ccflags = join(' ', '-Wall -Wextra -std=gnu99', `pkg-config --cflags-only-other rpm`);
chomp($ccflags);

WriteMakefile(
    NAME	=> 'RPMBDB',
    CCFLAGS	=> $ccflags,
    VERSION_FROM	=> 'RPMBDB.pm',
    dynamic_lib	=> { OTHERLDFLAGS => $ldflags },
    INC		=> $includes,
    dist	=> { COMPRESS => "xz -f", SUFFIX => ".xz" },
    realclean	=> { FILES => "t/RPMS/noarch/*" },
);
