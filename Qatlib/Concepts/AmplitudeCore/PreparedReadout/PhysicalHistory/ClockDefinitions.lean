/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdder
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Midpoint clocks and dyadic pulse coefficients

This module defines rational and real midpoint labels and identifies binary clock strings with
`Fin (2^q)` using least-significant-bit weights. `axisEnabled`, `axes`, and
`midpointCoefficient` describe the constant and bit-controlled pulses used to synthesize these
times.

The register and binary-label conventions fit the quantum circuit framework of
[NielsenChuang2010].

## Main statements

* `clockLabel_val`: the finite label equals the least-significant-bit value of the clock word.
* `raw_label_sum`: the clock label is the sum of its enabled powers of two.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

noncomputable section
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.Clock

/-- The rational midpoint `(j+1/2)/N` of the `j`th cell of a uniform partition of `[0,1]`. -/
def rationalMidpoint (N : ℕ) (j : Fin N) : ℚ := ((j : ℚ) + 1/2) / N

/-- The real midpoint `(j+1/2)/N` of the `j`th cell of a uniform partition of `[0,1]`. -/
def midpoint (N : ℕ) (j : Fin N) : ℝ := ((j : ℝ) + 1/2) / N

/-- For positive `N`, each real partition midpoint lies in `[0,1]`. -/
theorem midpoint_bounds (N : ℕ) (hN : 0 < N) (j : Fin N) :
    0 ≤ midpoint N j ∧ midpoint N j ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hj : (j : ℝ) < N := by exact_mod_cast j.isLt
  constructor
  · dsimp [midpoint]; positivity
  · dsimp [midpoint]
    apply (div_le_one hn).mpr
    have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_iff.mpr j.isLt
    linarith

/-- Convert a binary clock string to a finite label using least-significant-bit order. -/
def clockLabel (q : ℕ) (x : Reg q) : Fin (2 ^ q) :=
  bitVecEquiv q (fun j => x (Fin.rev j))

/-- The natural value of the clock label equals the least-significant-bit value of the Boolean
word. -/
theorem clockLabel_val (q : ℕ) (x : Reg q) :
    (clockLabel q x).val = booleanWordLSBValue q x := rfl

/-- The equivalence between `q`-bit clock strings and labels in `Fin (2^q)`. -/
def clockEquiv (q : ℕ) : Reg q ≃ Fin (2 ^ q) where
  toFun := clockLabel q
  invFun j i := (bitVecEquiv q).symm j (Fin.rev i)
  left_inv x := by
    funext i
    simp only [clockLabel, Equiv.symm_apply_apply, Fin.rev_rev]
  right_inv j := by
    change bitVecEquiv q (fun i => (bitVecEquiv q).symm j (Fin.rev (Fin.rev i))) = j
    simp only [Fin.rev_rev, Equiv.apply_symm_apply]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.Clock

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.DyadicClockPulses

open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

/-- The constant pulse is always enabled, while a bit pulse is enabled exactly when its clock
bit is true. -/
def axisEnabled {q : ℕ} : Option (Fin q) → Reg q → Bool
  | none, _ => true
  | some i, x => x i

/-- The list containing the constant pulse axis followed by every bit pulse axis. -/
def axes (q : ℕ) : List (Option (Fin q)) := none :: List.ofFn (fun i : Fin q => some i)

/-- The full dyadic pulse-axis list has length `q+1`. -/
theorem axes_length (q : ℕ) : (axes q).length = q + 1 := by simp [axes]

/-- Summing over the full axis list equals the constant-axis value plus the sum over bit axes. -/
theorem axes_sum (q : ℕ) (f : Option (Fin q) → ℚ) :
    ((axes q).map f).sum = f none + ∑ i : Fin q, f (some i) := by
  simp [axes, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- The rational dyadic denominator `2^q` for a `q`-bit clock. -/
def denominator (q : ℕ) : ℚ := (2 : ℚ) ^ q

/-- The dyadic clock denominator is strictly positive. -/
theorem denominator_pos (q : ℕ) : 0 < denominator q := by unfold denominator; positivity

/-- The dyadic clock denominator is at least one. -/
theorem denominator_one_le (q : ℕ) : 1 ≤ denominator q :=
  one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)

/-- The constant coefficient `1/(2*2^q)` or the bit coefficient `2^i/2^q` used to form midpoint
times. -/
def midpointCoefficient (q : ℕ) : Option (Fin q) → ℚ
  | none => 1 / (2 * denominator q)
  | some i => (2 : ℚ) ^ i.val / denominator q

/-- The rational clock label equals the sum of `2^i` over its true bits. -/
theorem raw_label_sum (q : ℕ) (x : Reg q) :
    ((Clock.clockLabel q x).val : ℚ) =
      ∑ i : Fin q, if x i then (2 : ℚ) ^ i.val else 0 := by
  rw [Clock.clockLabel_val, boolean_word_lsb_value, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [Nat.cast_pow]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.DyadicClockPulses

end
