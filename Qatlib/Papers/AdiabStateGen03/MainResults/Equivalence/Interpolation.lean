/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath.Basic
import Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence.SqrtGateOperator

/-!
# Norm and gap estimates for linear interpolation

Defines `linInterp` and proves its norm, Lipschitz, and Hermiticity properties. A scalar
interpolation-gap expression is bounded below when the overlap parameter is at least `1 / sqrt
2`, and a positive-gap inequality gives the stated adiabatic time estimate. See
[AharonovTaShma2007].

## Main statements

* `interpGap_ge_sqrt_half`: The scalar interpolated gap is at least `1 / sqrt 2` under the
  overlap bounds.
* `linInterp_norm_le`: A convex interpolation preserves a common operator-norm bound.
* `linInterp_isHermitian`: Real affine interpolation preserves Hermiticity.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- The affine Hamiltonian interpolation `(1 - s) • A + s • B`. -/
def linInterp (A B : Ham n) (s : ℝ) : Ham n := (1 - s) • A + s • B

/-- If `1 / sqrt 2 ≤ r ≤ 1` and `0 ≤ η ≤ 1`, the square root of `1 - 4 * (1 - η) * η * (1 - r ^
2)` is at least `1 / sqrt 2` [AharonovTaShma2007]. -/
theorem interpGap_ge_sqrt_half {η r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) (hr1 : r ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    1 / Real.sqrt 2 ≤ Real.sqrt (1 - 4 * (1 - η) * η * (1 - r ^ 2)) := by
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  exact hr.trans (JaggedPath.overlap_le_sqrt_gap hη0 hη1 hr0 hr1)

/-- The norm difference between interpolation values at `s` and `s'` is at most `|s - s'| * (‖A‖
+ ‖B‖)` [AharonovTaShma2007]. -/
theorem linInterp_lipschitz (A B : Ham n) (s s' : ℝ) :
    ‖linInterp A B s - linInterp A B s'‖ ≤ |s - s'| * (‖A‖ + ‖B‖) := by
  have hdiff : linInterp A B s - linInterp A B s' = (s' - s) • (A - B) := by
    unfold linInterp
    rw [smul_sub]
    match_scalars <;> ring
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_sub_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact norm_sub_le A B

/-- A convex interpolation of two Hamiltonians with norms at most `Λ` also has norm at most `Λ`
[AharonovTaShma2007]. -/
theorem linInterp_norm_le (A B : Ham n) (Λ : ℝ) (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖linInterp A B s‖ ≤ Λ := by
  unfold linInterp
  calc ‖(1 - s) • A + s • B‖ ≤ ‖(1 - s) • A‖ + ‖s • B‖ := norm_add_le _ _
    _ = (1 - s) * ‖A‖ + s * ‖B‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hs0]
    _ ≤ Λ := by
        nlinarith [hA, hB, mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ 1 - s),
          mul_le_mul_of_nonneg_left hB hs0]

/-- The real affine interpolation of two Hermitian Hamiltonians is Hermitian
[AharonovTaShma2007]. -/
theorem linInterp_isHermitian (A B : Ham n) (hA : IsHermitian A) (hB : IsHermitian B)
    (s : ℝ) : IsHermitian (linInterp A B s) := by
  have hA' : Matrix.IsHermitian A := hA
  have hB' : Matrix.IsHermitian B := hB
  have h1 : IsSelfAdjoint ((1 - s : ℝ)) := by
    simp [IsSelfAdjoint]
  have h2 : IsSelfAdjoint (s : ℝ) := by
    simp [IsSelfAdjoint]
  show Matrix.IsHermitian (linInterp A B s)
  unfold linInterp
  exact (Matrix.IsHermitian.smul hA' h1).add (Matrix.IsHermitian.smul hB' h2)

/-- For positive `γ`, the inequality `2 * Λ ≤ T * ε * γ ^ 2` implies `2 * Λ / γ ^ 2 ≤ T * ε`
[AharonovTaShma2007]. -/
theorem adiabaticTime_bound {Λ γ T ε : ℝ} (hγ : 0 < γ)
    (hT : 2 * Λ ≤ T * ε * γ ^ 2) :
    2 * Λ / γ ^ 2 ≤ T * ε := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hγ, hT]

end Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence
