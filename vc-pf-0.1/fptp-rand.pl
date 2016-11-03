#!/usr/bin/perl
# random votes for fptp counting

$num_votes = $ARGV[0];
$num_cands = 4;
@cands = ("Alice", "Bob", "Claire", "Darren");

print "\"[";
for ($i = 0; $i < $num_votes; $i++) {
  print $cands[int(rand($num_cands))];
  if ($i < $num_votes - 1) { print ", "; }
}
print "]\"";
