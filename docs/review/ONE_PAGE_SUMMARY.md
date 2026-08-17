# E274 bounded coset-partition theorem: one-page summary

This is an unreviewed, computer-assisted candidate. The unrestricted
Herzog-Schönheim conjecture remains open.

## Claim

Every nontrivial exact coset partition of an arbitrary group into at most
seventeen left cosets of finite-index subgroups has two equal subgroup
indices. Equivalently, every counterexample requires at least eighteen cells.

## Proof outline

1. Choose a counterexample with the fewest cells among those with at most
   seventeen cells.
2. An index-two cell gives a distinct-index partition of the index-two
   subgroup with one fewer cell, contradicting minimality.
3. The common normal core gives a finite quotient with exactly the same cells
   and index profile.
4. Sort the indices. Local Lean proofs give reciprocal sum one, pairwise gcd
   greater than one, and four source-shaped forbidden harmonic patterns.
5. A complete exact search is empty through sixteen. At seventeen it leaves
   exactly five profiles, all beginning with index four.
6. Use the index-four cell as an anchor. Its complement consists of three
   non-anchor boxes. For every other index `n`, support size `d`, and induced
   index `e`, one has `n*d = 4*e`.
7. Induced indices in the same box have gcd greater than one, and each box has
   reciprocal capacity one.
8. These conditions define a finite labelled mask assignment. Lean proves
   that every mathematical assignment supplies a successful branch of a
   direct DFS.
9. Split `decide +kernel` certificates prove the DFS false for all five
   profiles, giving the contradiction.

The arithmetic certificate tree has 1,052 states in 18 modules. The fiber
certificate family has 251 modules: one data module, 174 leaves, 71 internal
nodes, and five profile endpoints. A leaf covers at most 6,000 DFS states; a
parent unfolds one transition and rewrites all children.

At eighteen terms, a supplementary Python diagnostic has 470 arithmetic
profiles and leaves 39 after the first-order one-anchor test. They are
necessary-condition lists, not group partitions.

## Lean boundary

The final endpoint is `erdos274AtMostSeventeen`. It has no external theorem
parameter. The finite quotient, two partition identities, four source-shaped
obstruction proofs, detector transfers, arithmetic enumeration, index-four
bridge, DFS completeness, and five negative computations are all in its local
dependency chain.

Its axiom report contains only `propext`, `Classical.choice`, and
`Quot.sound`. The theorem-facing tree contains no `sorry`, custom axiom,
`native_decide`, `bv_decide`, compiler evaluation axiom, `unsafe`, `extern`,
or `implemented_by` declaration.

## Main review questions

- Do the local source-shaped P4.2/P4.3/P4.5/P4.7 statements and proofs match
  the required published obstructions?
- Is the index-four support equation and per-box capacity argument correct
  without assuming the anchor subgroup is normal?
- Does the assignment-to-DFS theorem cover every declarative assignment?
- Do the split certificates cover every DFS branch without extra rejection?
- Is an arbitrary-group bound through seventeen already in the literature?
