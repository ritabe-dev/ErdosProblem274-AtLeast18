# Akman--Sissokho bounded-coset excerpt

Retrieved: 2026-08-03 JST (UTC+09:00)

Paper: F. Akman and P. A. Sissokho, *Transversal Coset Partitions of Groups*.

Publication: *Beiträge zur Algebra und Geometrie* 66 (2025), 417--441.

Author PDF:
https://bpb-us-w2.wpmucdn.com/about.illinoisstate.edu/dist/3/176/files/2024/05/TransversalCosetPartitionsOfGroups_Preprint_April23-299aa957e61e24f4.pdf

DOI: https://doi.org/10.1007/s13366-024-00748-9

Publisher online date: 2024-04-25.  The publisher supplies a calendar date
but no time or time zone, so no UTC or JST time is inferred.

Theorem 6 checks the Herzog--Schönheim conjecture for partitions of arbitrary
groups involving `2 <= r <= 7` distinct proper subgroups. In a counterexample
the indices are distinct, so the same subgroup cannot occur in two cells.
Thus the number of distinct subgroups equals the number of cells, which is
the bridge to the seven-cell formulation used in the E274 manuscript. On
printed page 13, the authors state that their computation stopped at `r = 7`
because `r = 8` exceeded their time limit. Their three arithmetic filters
were repeated denominators, an index equal to 2, and a coprime pair.

The same page displays arithmetic lists at `r = 13` and `r = 15` that evade
those three filters.  In particular, the `r = 13` list is

`[3,6,9,12,15,18,24,27,30,45,54,60,72]`.

This paper therefore supplies the prior general bound `r <= 7`, not a result
for `8 <= r <= 16`.

Related public code:
https://github.com/psissok72/Egyptian-Fractions

The `master` branch HEAD inspected on 2026-08-03 JST was
`5d37918be097bc70972ed35f07e5ae875198e920`.  The local audit did not freeze
the commit timestamp and source time zone, so neither is asserted here.  Its
checked-in programs cover the reported searches through seven terms.
