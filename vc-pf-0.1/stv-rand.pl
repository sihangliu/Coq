#!/usr/bin/perl
$num_votes = $ARGV[0];
$num_cands = 4;
@cands = ("Alice", "Bob", "Charlie", "Deliah");

print "\"[";
for ($i = 0; $i < $num_votes; $i++) {
  print "[";
  # guess a ballot length
  $ballot_len = int(rand($num_cands+1));
  # print $j; print "-";
  @t_cands = @cands;
  for ($j = 0; $j < $ballot_len; $j++) { 
    # print ">>"; print @t_cands; print "<<";
    $c = int(rand($num_cands - $j));
    print $t_cands[$c];
    $t_cands[$c] = $t_cands[$num_cands - $j -1];
    if ($j < $ballot_len - 1) { print ", "; }
  }
  if ($i < $num_votes - 1) { print "], "; }  else { print "]"; }
}
print "]\"";
