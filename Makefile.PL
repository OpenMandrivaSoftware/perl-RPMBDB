use strict;
use ExtUtils::MakeMaker;

my $libs = "-L../rpmdb -lrpmdb -lrpm -lrpmio";
my $includes = '-I../rpmdb -I../lib -I../rpmio';
my $ccflags = join(' ', '-Wall -Wextra -std=gnu99', `pkg-config --cflags-only-other rpm`);
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
