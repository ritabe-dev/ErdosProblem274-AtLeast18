import ErdosProblems.E274.UnconditionalTheorem

/-!
# Erdős Problem #274 lane entrypoint

This lane proves the bounded Herzog--Schönheim statement for arbitrary groups:
every exact finite-index coset partition with between two and seventeen cells
has a repeated subgroup index.  The public endpoint is
`erdos274AtMostSeventeen`.

The normal-core quotient, Lemma 2.3(b,c) consequences, and the four
source-shaped Margolis--Schnabel obstruction arguments are proved locally.
The exact arithmetic recursion is checked by split `decide +kernel`
certificates.  Its five length-seventeen survivors are ruled out by a direct
index-four assignment bridge and split, memo-free kernel DFS certificates.
No native-evaluation theorem or external theorem parameter occurs in the final
dependency chain.  The unrestricted conjecture remains open, and the
length-eighteen survivors are necessary-condition profiles rather than group
partitions.
-/
