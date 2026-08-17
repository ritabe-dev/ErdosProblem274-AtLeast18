# Lean theorem and dependency map

## Statement and reduction surface

| Mathematical role | Lean item | File |
| --- | --- | --- |
| Exact coset partition | `IsCosetPartition` | `Problem.lean` |
| Distinct-index counterexample | `HasDistinctIndexCosetPartition` | `Problem.lean` |
| Final bounded target | `erdos274AtMostSeventeenTarget` | `Problem.lean` |
| Index-two descent | `IsCosetPartition.descendIndexTwo` | `IndexTwoDescent.lean` |
| Minimal index-two-free witness | `HasBoundedCounterexample.existsIndexTwoFreeWitness` | `MinimalCounterexample.lean` |
| Normal-core finite quotient | `HasDistinctIndexCosetPartition.toFiniteQuotient` | `FiniteQuotientBridge.lean` |
| Reciprocal-sum identity | `IsCosetPartition.sum_inv_index_eq_one` | `LocalPartitionFacts.lean` |
| Pairwise-gcd consequence | `IsCosetPartition.gcd_index_gt_one` | `LocalPartitionFacts.lean` |

## Local obstruction closure

| Source-shaped role | Lean endpoint | File |
| --- | --- | --- |
| Proposition 4.2 finite obstruction | `margolisSchnabelP42` | `MargolisSchnabelP42.lean` |
| Proposition 4.3 finite obstruction | `margolisSchnabel_prop4_3_finite` | `MargolisSchnabelP43.lean` |
| Proposition 4.5 finite obstruction | `margolisSchnabel_prop4_5_finite` | `MargolisSchnabelP45.lean` |
| Proposition 4.7 finite obstruction | `margolisSchnabel_prop4_7_finite` | `MargolisSchnabelP47.lean` |
| Detector selection and transfer | `p42DetectorCorollary` and analogues | `MargolisSchnabelP4*Detector.lean` |
| Six-field local bundle | `localMargolisSchnabelFacts` | `LocalMargolisSchnabelFacts.lean` |

`MargolisSchnabelFacts` remains an internal interface in
`MargolisSchnabelImports.lean`. It is locally inhabited and is not a parameter
of the public final theorem.

## Exact arithmetic layer

| Mathematical role | Lean item | File |
| --- | --- | --- |
| Four obstruction detectors | `containsP42`, `containsP43`, `containsP45`, `containsP47` | `ArithmeticSearch.lean` |
| Detector semantics | `containsP42_eq_true_iff_witness` and analogues | `HarmonicObstructionSemantics.lean` |
| Exact recursive enumerator | `candidateIndexLists` | `ArithmeticSearch.lean` |
| Semantic completeness | `searchComplete` | `SearchCompleteness.lean` |
| Split arithmetic certificates | `arithmeticSearchCertificateD*` | `ArithmeticSearchCertificateD0.lean` through `D17.lean` |
| Exact five profiles | `checked_seventeen_survivors` | `ArithmeticSearchCertificateD0.lean` |

The 18 certificate modules cover the exact 1,052-state recursion tree. Local
finite checks use `decide +kernel`; internal nodes rewrite imported child
theorems.

## Index-four bridge and kernel DFS

| Mathematical role | Lean item | File |
| --- | --- | --- |
| Three boxes and index relation | `indexFourFiberAssignment` | `IndexFourFiberBridge.lean` |
| Ordered mask witness | `OrderedFiberMaskAssignment4` | `FiberMaskBasics.lean` |
| Group witness to mask witness | `IndexFourFiberAssignment.toOrderedMaskAssignment4` | `IndexFourFiberMaskBridge.lean` |
| Executable DFS | `kernelFiberDFS4` | `FiberKernelDFSCore.lean` |
| Assignment-to-DFS completeness | `kernelFiberDFS4_complete_of_orderedAssignment` | `FiberKernelDFSSoundness.lean` |
| Five split profile endpoints | `kernelFiberProfile1_unsat` through `kernelFiberProfile5_unsat` | `FiberKernelDFSCertificateP1.lean` through `P5.lean` |
| Combined assignment obstruction | `seventeenIndexFourAssignmentObstruction_kernel` | `FiberKernelAssignmentObstruction.lean` |

The 251 generated fiber modules consist of one data module, 174 leaves, 71
internal nodes, and five profile endpoints. No old breadth-first/native route
is imported by this standalone tree.

## Final composition

| Mathematical role | Lean item | File |
| --- | --- | --- |
| Composition from finite assignment obstruction | `erdos274AtMostSeventeen_of_assignmentObstruction` | `KernelFiberComposition.lean` |
| Public closed theorem with no external theorem parameter | `erdos274AtMostSeventeen` | `UnconditionalTheorem.lean` |

`erdos274AtMostSeventeen` has type `erdos274AtMostSeventeenTarget`, has no
external theorem argument, and its audited axiom set is exactly the ordinary
Lean subset `propext`, `Classical.choice`, and `Quot.sound`.
