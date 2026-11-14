/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Qatlib.Papers.AdiabPower02.GapExamples.QubitSpectrum

@[expose] public section

/-!
# A perturbed Hamming weight potential

Defines the Hamming weight potential `weightPot` and the modified potential `perturbedPot`,
which takes value `-1` on the all-ones string. The module also bounds the tensor ground-state
amplitude at that string using the one-qubit amplitude estimate. See [VanDamMoscaVazirani2001].

## Main statements

* `perturbedPot_allOnes`: The distinguished all-ones string has potential `-1`.
* `ground_amplitude_bound`: The tensor amplitude is at most `(1 / sqrt 2) ^ n`.

## References

* [van Dam et al., 2001][VanDamMoscaVazirani2001]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix

namespace Qatlib.Papers.AdiabPower02.GapExamples

/-- The Boolean string whose every bit is true. -/
def allOnes (n : ℕ) : Fin n → Bool := fun _ => true

/-- The Hamming weight of a Boolean string, regarded as a real potential. -/
def weightPot {n : ℕ} (z : Fin n → Bool) : ℝ := (boolWeight z : ℝ)

/-- The Hamming weight potential modified to equal `-1` at the all-ones string. -/
def perturbedPot {n : ℕ} (z : Fin n → Bool) : ℝ :=
  if z = allOnes n then -1 else (boolWeight z : ℝ)

/-- The perturbed potential equals `-1` at the all-ones string. -/
@[simp] lemma perturbedPot_allOnes (n : ℕ) : perturbedPot (allOnes n) = -1 := by
  simp [perturbedPot]

/-- Away from the all-ones string, the perturbed potential equals the Hamming weight potential
[VanDamMoscaVazirani2001]. -/
lemma perturbedPot_of_ne {n : ℕ} {z : Fin n → Bool} (hz : z ≠ allOnes n) :
    perturbedPot z = weightPot z := by
  simp [perturbedPot, weightPot, hz]

/-- The all-ones string of length `n` has Hamming weight `n`. -/
lemma boolWeight_allOnes {n : ℕ} : boolWeight (allOnes n) = n := by
  simp [boolWeight, allOnes]

/-- For `0 ≤ s ≤ 1`, the `n`th power of the one-qubit ground-state amplitude is at most `(1 /
sqrt 2) ^ n`. -/
theorem ground_amplitude_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    amp1 s ^ n ≤ (1 / Real.sqrt 2) ^ n := by
  have h := amp_pow_le hs0 hs1 n
  have hsqrt : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    simp
  rwa [hsqrt] at h

/-- Multiplying the ground-state amplitude bound by any nonnegative real coefficient preserves
the inequality [VanDamMoscaVazirani2001]. -/
theorem perturbation_amplitude_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    c * amp1 s ^ n ≤ c * (1 / Real.sqrt 2) ^ n :=
  mul_le_mul_of_nonneg_left (ground_amplitude_bound hs0 hs1 n) hc

end Qatlib.Papers.AdiabPower02.GapExamples
