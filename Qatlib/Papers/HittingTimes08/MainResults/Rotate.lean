/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.Detect

/-!
# Approximate rotation in a normed space

This module models an approximate rotation as `rotationMixtureModel`, a weighted sum of an ideal
vector and a residual vector. It proves a norm-error estimate and a detection-cost bound
corresponding to the rotation analysis in [MagniezEtAl2008].

## Main statements

* `theorem_3_9`: bounds the deviation from the ideal vector by `sqrt (8 * ε)`.
* `theorem_3_9_cost`: bounds the modeled detection cost by `2 * k * (T + 1)`.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

/-- The vector mixture `sqrt (1 - η) • rot + sqrt η • junk`. -/
def rotationMixtureModel {E : Type*} [Add E] [SMul ℝ E] (rot junk : E) (η : ℝ) : E :=
  Real.sqrt (1 - η) • rot + Real.sqrt η • junk

/-- For unit vectors `rot` and `junk`, `0 < ε ≤ 1 / 2`, and `(1 / 3) ^ k ≤ 2 * ε`, the mixture
differs from `rot` by at most `sqrt (8 * ε)`. This is the norm estimate associated with
[Magniez et al., Theorem 3.9][MagniezEtAl2008]. -/
theorem theorem_3_9 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rot junk : E) (ε : ℝ) (k : ℕ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη : (1 / 3 : ℝ) ^ k ≤ 2 * ε)
    (hrot : ‖rot‖ = 1) (hjunk : ‖junk‖ = 1) :
    ‖rotationMixtureModel rot junk ((1 / 3 : ℝ) ^ k) - rot‖ ≤ Real.sqrt (8 * ε) := by
  set η : ℝ := (1 / 3 : ℝ) ^ k with hηdef
  have hη0 : 0 ≤ η := pow_nonneg (by norm_num) k
  have hη1 : η ≤ 1 := by linarith

  have hsqrt_le_one : Real.sqrt (1 - η) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith

  have hle_sqrt : 1 - η ≤ Real.sqrt (1 - η) := by
    have h0 : (0 : ℝ) ≤ 1 - η := by linarith
    rw [Real.le_sqrt (x := 1 - η) (y := 1 - η) h0 h0]
    nlinarith

  have habs : |Real.sqrt (1 - η) - 1| ≤ η := by
    rw [abs_of_nonpos (by linarith)]
    linarith

  have hsq : η ≤ Real.sqrt η := by
    rw [Real.le_sqrt hη0 hη0]
    nlinarith

  have hsplit : rotationMixtureModel rot junk η - rot =
      (Real.sqrt (1 - η) - 1) • rot + Real.sqrt η • junk := by
    have h2 : Real.sqrt (1 - η) • rot - rot = (Real.sqrt (1 - η) - 1) • rot := by
      calc Real.sqrt (1 - η) • rot - rot
          = Real.sqrt (1 - η) • rot - (1 : ℝ) • rot := by rw [one_smul]
        _ = (Real.sqrt (1 - η) - 1) • rot := by rw [sub_smul]
    unfold rotationMixtureModel
    calc Real.sqrt (1 - η) • rot + Real.sqrt η • junk - rot
        = (Real.sqrt (1 - η) • rot - rot) + Real.sqrt η • junk := by abel
      _ = (Real.sqrt (1 - η) - 1) • rot + Real.sqrt η • junk := by rw [h2]

  have hsqrt4 : Real.sqrt 4 = (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hbig : 2 * Real.sqrt η ≤ Real.sqrt (8 * ε) := by
    have hle : Real.sqrt η ≤ Real.sqrt (2 * ε) :=
      Real.sqrt_le_sqrt (by linarith)
    have heq : 2 * Real.sqrt (2 * ε) = Real.sqrt (8 * ε) := by
      rw [show (8 : ℝ) * ε = 4 * (2 * ε) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
    linarith
  calc
    ‖rotationMixtureModel rot junk η - rot‖
        = ‖(Real.sqrt (1 - η) - 1) • rot + Real.sqrt η • junk‖ := by rw [hsplit]
    _ ≤ ‖(Real.sqrt (1 - η) - 1) • rot‖ + ‖Real.sqrt η • junk‖ := norm_add_le _ _
    _ = |Real.sqrt (1 - η) - 1| + |Real.sqrt η| := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hrot, hjunk]
          simp
    _ ≤ η + Real.sqrt η := by
          rw [abs_of_nonneg (Real.sqrt_nonneg η)]
          linarith
    _ ≤ Real.sqrt (8 * ε) := by linarith

/-- For positive `ε` and `T`, under the stated quantile hypothesis, the detection cost at
threshold `1 / T` is at most `2 * k * (T + 1)`, as used for Theorem 3.9 of
[MagniezEtAl2008]. -/
theorem theorem_3_9_cost {J : Type*} [Fintype J] (S : PhaseSpectrum J)
    (ε T : ℝ) (k : ℕ) (hε0 : 0 < ε) (hT0 : 0 < T)
    (hT : (S.law).quantile ε ≤ T) :
    PhaseSpectrum.detectCostModel (1 / T) k ≤ 2 * (k : ℝ) * (T + 1) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcost : PhaseSpectrum.detectCostModel (1 / T) k = (k : ℝ) * (T + 1) := by
    unfold PhaseSpectrum.detectCostModel
    field_simp
  rw [hcost]
  nlinarith [hk0, hT0.le]

end Qatlib.Papers.HittingTimes08.MainResults
