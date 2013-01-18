use strict;
use ExtUtils::MakeMaker;

my $libs = "-L../rpmdb/.libs -lrpmdb -L../lib/.libs -lrpm -L../rpmio/.libs -lrpmio";
my $includes = '-I../rpmdb -I../lib -I../rpmio';
my $ccflags = '-Wall -Wextra -std=gnu99';
chomp($ccflags);

WriteMakefile(
    NAME	=> 'RPMBDB',
    CCFLAGS	=> $ccflags,
    VERSION_FROM	=> 'RPMBDB.pm',
    dynamic_lib	=> { OTHERLDFLAGS => $libs },
    INC		=> $includes,
    dist	=> { COMPRESS => "xz -f", SUFFIX => ".xz" },
    realclean	=> { FILES => "t/RPMS/noarch/*" },
);
