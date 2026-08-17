# Lean review request

Please run a fresh-copy build and inspect the exact theorem and trust surface.

```bash
bash scripts/check_release.sh
```

Please confirm:

1. `erdos274AtMostSeventeen` has type
   `erdos274AtMostSeventeenTarget` and no external theorem argument;
2. `localMargolisSchnabelFacts` constructs all six internal interface fields
   from local Lean proofs;
3. the normal-core quotient and detector-selection bridges occur in the local
   dependency chain;
4. `checked_seventeen_survivors` is obtained from the complete D0–D17 split
   arithmetic certificate;
5. `IndexFourFiberAssignment.toOrderedMaskAssignment4` represents every
   group-theoretic assignment without assuming a normal anchor;
6. `kernelFiberDFS4_complete_of_orderedAssignment` proves the required
   assignment-to-executable direction;
7. the 174 fiber leaves and 71 internal nodes cover every successful DFS
   child and use no extra rejection condition;
8. `seventeenIndexFourAssignmentObstruction_kernel` combines all five
   negative profile endpoints;
9. the public final endpoint and all audited intermediate endpoints use only
   `propext`, `Classical.choice`, and `Quot.sound`;
10. no `sorry`, custom axiom, native/compiler evaluation, unsafe declaration,
    external implementation, or incomplete import closure remains.

Please also inspect both deterministic generators. Their default modes must
be read-only and reproduce the checked-in certificate modules byte for byte.
Generator correctness is useful for reproducibility, but the Lean parent and
leaf proofs themselves must establish certificate coverage.

The review should distinguish a closed bounded Lean endpoint with no external
theorem parameter from a line-by-line transcription of the cited article.
