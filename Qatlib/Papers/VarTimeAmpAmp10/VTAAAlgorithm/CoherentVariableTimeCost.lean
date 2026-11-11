/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimePrefix

/-!
# Directed calls and paid prefix costs

`directedCalls` counts oracle accesses by slot and direction. The module proves adjoint and
concatenation laws for calls and costs, then computes the exact forward and inverse call counts,
known-gate counts, and dyadic access prices of `paidPrefix`.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `paidPrefix_directedCalls` and `paidPrefix_inverseCalls`: exact directed prefix accesses.
* `paidPrefix_accessPrice`: dyadic access price `2^n - 1`.
* `paidPrefix_totalPrice`: access and known-gate price accounting.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false



namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators
set_option warningAsError false
noncomputable section
set_option linter.unusedSectionVars false

/-- The number of oracle instructions in a word with the specified slot and adjoint-direction
flag. -/
def directedCalls {H : Type} {r : ℕ} (C : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) (slot : ℕ) (adj : Bool) : ℕ :=
  C.countP fun s => match s with
    | .known _ => false
    | .call i _ a => decide (i = slot) && decide (a = adj)

/-- Directed oracle-call counts are additive under word concatenation. -/
theorem directedCalls_append {H : Type} {r : ℕ}
    (C D : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) (slot : ℕ) (adj : Bool) :
    directedCalls (C ++ D) slot adj = directedCalls C slot adj + directedCalls D slot adj :=
  List.countP_append

/-- Taking a word adjoint exchanges the forward and adjoint directed call counts at every oracle
slot. -/
theorem directedCalls_adjoint {H : Type} {r : ℕ}
    (C : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) (slot : ℕ) (adj : Bool) :
    directedCalls (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint C) slot adj = directedCalls C slot (!adj) := by
  unfold directedCalls Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint
  rw [List.countP_map, List.countP_reverse]
  congr 1
  funext s
  cases s with
  | known U => rfl
  | call i T a => cases a <;> cases adj <;> rfl

/-- Taking a word adjoint preserves the known-gate count. -/
theorem knownCount_adjoint {H : Type} {r : ℕ} (C : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint C) = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount C := by
  unfold Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint
  rw [List.countP_map, List.countP_reverse]
  congr 1
  funext s
  cases s <;> rfl

/-- The known-gate count is additive under word concatenation. -/
theorem knownCount_append {H : Type} {r : ℕ} (C D : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (C ++ D) = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount C + Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount D := List.countP_append

/-- Weighted oracle access cost is additive under word concatenation. -/
theorem weightedCost_append {H : Type} {r : ℕ} (prices : ℕ → ℕ) (C D : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices (C ++ D) =
      Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices C + Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices D := by
  simp only [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost, List.map_append,
      List.sum_append]

/-- Taking a word adjoint preserves weighted oracle access cost. -/
theorem weightedCost_adjoint {H : Type} {r : ℕ} (prices : ℕ → ℕ) (C : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint C) = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices C := by
  unfold Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint
  rw [List.map_map, List.map_reverse, List.sum_reverse]
  congr 1
  apply List.map_congr_left
  intro s _
  cases s <;> rfl

variable {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}

/-- A paid stage word makes exactly one forward call to its own slot and no other directed
calls. -/
theorem paidStage_directedCalls (P target : Matrix H H ℂ) (slot k : ℕ) (adj : Bool) :
    directedCalls (paidStageWord P target slot) k adj =
      if slot = k ∧ adj = false then 1 else 0 := by
  cases adj <;> by_cases h : slot = k <;> simp [directedCalls, paidStageWord, h]

/-- The weighted oracle cost of a paid stage word equals the price of its slot. -/
theorem paidStage_weightedCost (P target : Matrix H H ℂ) (slot : ℕ) (prices : ℕ → ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices (paidStageWord P target slot) = prices slot := by
  simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost, paidStageWord]

/-- A paid prefix of length `n` contains exactly `4 * n` known gates. -/
theorem paidPrefix_knownCount (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (paidPrefix f n hn) = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [paidPrefix, knownCount_append, ih, frameStageWord,
      (paidStage_calls _ _ _).2]
    omega

/-- A paid prefix of length `n` makes exactly one forward call at each slot below `n` and no
other directed calls. -/
theorem paidPrefix_directedCalls (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m)
    (slot : ℕ) (adj : Bool) :
    directedCalls (paidPrefix f n hn) slot adj = if slot < n ∧ adj = false then 1 else 0 := by
  induction n with
  | zero => simp [paidPrefix, directedCalls]
  | succ n ih =>
    rw [paidPrefix, directedCalls_append, frameStageWord, paidStage_directedCalls, ih]
    change (if slot < n ∧ adj = false then (1 : ℕ) else 0) +
      (if n = slot ∧ adj = false then 1 else 0) =
      if slot < n + 1 ∧ adj = false then 1 else 0
    cases adj with
    | false =>
      simp only [and_true]
      split_ifs <;> omega
    | true => simp

/-- The adjoint of a paid prefix of length `n` makes exactly one adjoint call at each slot below
`n` and no other directed calls. -/
theorem paidPrefix_inverseCalls (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m)
    (slot : ℕ) (adj : Bool) :
    directedCalls (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidPrefix f n hn)) slot adj =
      if slot < n ∧ adj = true then 1 else 0 := by
  rw [directedCalls_adjoint, paidPrefix_directedCalls]
  cases adj <;> simp

/-- The dyadically weighted access cost of a paid prefix of length `n`, plus one, equals `2^n`. -/
theorem paidPrefix_accessPrice (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun j => 2 ^ j) (paidPrefix f n hn) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [paidPrefix, weightedCost_append, frameStageWord, paidStage_weightedCost, pow_succ]
    change Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun j => 2 ^ j)
        (paidPrefix f n (by omega)) + 2 ^ n + 1 = _
    have hi := ih (by omega)
    omega

/-- The paid prefix's access cost plus priced known-gate count equals `(2^n - 1) + macroPrice *
(4 * n)`. -/
theorem paidPrefix_totalPrice (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m) (macroPrice : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun j => 2 ^ j) (paidPrefix f n hn) +
      macroPrice * Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (paidPrefix f n hn) =
      (2 ^ n - 1) + macroPrice * (4 * n) := by
  rw [paidPrefix_knownCount]
  have hprice := paidPrefix_accessPrice f n hn
  omega

/-- With unit known-gate price, a paid prefix's total access and gate cost equals `(2^n - 1) + 4
* n`. -/
theorem paidPrefix_unitMacroPrice (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun j => 2 ^ j) (paidPrefix f n hn) +
      Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (paidPrefix f n hn) = (2 ^ n - 1) + 4 * n := by
  simpa only [one_mul] using! paidPrefix_totalPrice f n hn 1

end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
