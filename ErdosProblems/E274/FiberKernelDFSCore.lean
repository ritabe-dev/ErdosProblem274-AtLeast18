import ErdosProblems.E274.FiberMaskBasics

/-!
# Kernel-reducible depth-first fiber checker for E274

This lightweight core is independent of the hash-set breadth-first search and
contains no closed computation theorem.  Certificate modules import it and
split the finite computation into kernel-manageable branches.
-/

namespace ErdosProblems.E274

abbrev KernelFiberColumn := Nat × List Nat
abbrev KernelFiberState := List KernelFiberColumn

/-- Constant-time population count for the seven nonempty three-bit masks. -/
def kernelSupportSize3Fast (mask : Nat) : Nat :=
  match mask with
  | 1 | 2 | 4 => 1
  | 3 | 5 | 6 => 2
  | 7 => 3
  | _ => 0

/-- The induced index determined by `n * d = 4 * e`, when a mask is valid. -/
def kernelInducedIndex4 (index mask : Nat) : Option Nat :=
  let d := kernelSupportSize3Fast mask
  if 1 <= mask && mask < 8 && (index * d) % 4 = 0 then
    some ((index * d) / 4)
  else none

/-- All nonempty three-box masks satisfying the index relation for one row. -/
def kernelFiberChoices4 (index : Nat) : List (Nat × Nat) :=
  (List.range' 1 7).filterMap fun mask =>
    (kernelInducedIndex4 index mask).map fun induced => (mask, induced)

/-- Update one box, rejecting overfill and a coprime pair. -/
def kernelUpdateFiberColumn (scale induced : Nat)
    (column : KernelFiberColumn) : Option KernelFiberColumn :=
  if induced = 0 || scale % induced != 0 then none
  else
    let increment := scale / induced
    if column.1 + increment > scale then none
    else if column.2.any (fun old => decide (Nat.gcd induced old = 1)) then none
    else some (column.1 + increment, induced :: column.2)

/-- Apply one mask to all three labelled boxes. -/
def kernelUpdateFiberColumns (scale mask induced : Nat) :
    Nat → KernelFiberState → Option KernelFiberState
  | _column, [] => some []
  | column, head :: tail => do
      let newHead ←
        if mask.testBit column then
          kernelUpdateFiberColumn scale induced head
        else some head
      let newTail ←
        kernelUpdateFiberColumns scale mask induced (column + 1) tail
      pure (newHead :: newTail)

/-- Memo-free labelled DFS.  `true` means that at least one complete mask
assignment fills every box exactly. -/
def kernelFiberDFS4 (scale : Nat) :
    List Nat → KernelFiberState → Bool
  | [], state => state.all fun column => column.1 = scale
  | index :: rows, state =>
      (kernelFiberChoices4 index).any fun choice =>
        match kernelUpdateFiberColumns scale choice.1 choice.2 0 state with
        | none => false
        | some next => kernelFiberDFS4 scale rows next

/-- Common exact denominator for all possible induced reciprocals. -/
def kernelFiberScale4 (rows : List Nat) : Nat :=
  (rows.flatMap fun index =>
    (kernelFiberChoices4 index).map Prod.snd).foldl Nat.lcm 1

def emptyKernelFiberState : KernelFiberState :=
  [(0, []), (0, []), (0, [])]

end ErdosProblems.E274
