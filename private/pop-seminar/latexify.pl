#!/usr/bin/perl
use strict;

foreach my $f (@ARGV) {
  undef $/;
  open (F, "$f") or die;
  my $str = <F>;
  close F or die;
  $str =~ s|{|\\{|g;
  $str =~ s|}|\\}|g;
  $str =~ s|<->|\\iIff|g; # must come before ->
  $str =~ s/->/\\iTo/g;
  $str =~ s/forall/\\iForall/g;
  $str =~ s|/\\|\\iAnd|g;
  $str =~ s|\\/|\\iOr|g;
  $str =~ s|=>|\\iImply|g;
  $str =~ s|not(\s)|\\iNot\1|g;
  $str =~ s/exists/\\iExists/g;
  $str =~ s/exists1/\\iExistsOne/g;
  $str =~ s/\|\|([^|]*)\|\|/\\iT{\1}/g;
  $str =~ s|=\(([^)]*)\)=|\\iPer{\1}|g;
  $str =~ s|=(\w*)=|\\iPer{\1}|g;
  $str =~ s|<=|\\iLeq|g;
  $str =~ s/\|=/\\iRz/g;

  open (G, ">${f}.ltx") or die;
  print G $str;
  close G or die;
  print "$f\n";
}
