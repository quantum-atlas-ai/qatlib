/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.ApparatusShift
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Fourier implementation of cyclic pointer shifts

This module realizes a finite pointer translation by conjugating a diagonal momentum phase with
the positive quantum Fourier transform. The definitions `momPhaseDiag` and `cyclicShift` fix the
sign convention for the finite apparatus discussed in [LidarWang1999].

The proofs establish unitarity and the exact action on pointer basis vectors for a positive
register size.

## Main statements

* `fourier_conj_diag_eq_shift`: Fourier conjugation of the momentum phase equals the cyclic
  shift.
* `cyclicShift_unitary`: the resulting shift matrix is unitary.
* `fourier_word_delta`: the Fourier word translates a pointer basis vector modulo the register
  size.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ThermalRate98.MainResults

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Matrix

/-- The momentum phase at index `p`, given by the integer power `-(k * p.val)` of `primRoot M`. -/
def momPhase (M : ℕ) (k : ℤ) : Fin M → ℂ :=
  fun p => primRoot M ^ (-(k * (p.val : ℤ)))

/-- The diagonal matrix of momentum phases implementing a displacement by `k` after Fourier
conjugation. -/
def momPhaseDiag (M : ℕ) (k : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal (momPhase M k)

/-- The cyclic translation matrix whose `(x, z)` entry is one exactly when `x` equals `z + k`
modulo `M`. -/
def cyclicShift (M : ℕ) (k : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
  fun x z => if ((M : ℤ) ∣ ((x.val : ℤ) - k - (z.val : ℤ))) then 1 else 0

/-- Every integer power of `primRoot M` has complex conjugate times itself equal to one. -/
theorem primRoot_unit (M : ℕ) (c : ℤ) :
    star (primRoot M ^ c) * primRoot M ^ c = 1 := by
  rw [show star (primRoot M ^ c) = primRoot M ^ (-c) from primRoot_conj_zpow M c,
    ← zpow_add₀ (primRoot_ne_zero M)]
  simp

/-- The diagonal momentum phase matrix is unitary for a positive register size. -/
theorem momPhaseDiag_unitary {M : ℕ} (_hM : 0 < M) (k : ℤ) :
    momPhaseDiag M k ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold momPhaseDiag
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hfun : (fun i : Fin M => star (momPhase M k) i * momPhase M k i) = fun _ => (1 : ℂ) := by
    funext i
    simp only [Pi.star_apply]
    exact primRoot_unit M _
  rw [hfun, Matrix.diagonal_one]

/-- For `M > 0`, conjugating `momPhaseDiag M k` by the positive Fourier matrix yields
`cyclicShift M k`. This gives the finite pointer translation underlying the apparatus
construction in [LidarWang1999]. -/
theorem fourier_conj_diag_eq_shift {M : ℕ} (hM : 0 < M) (k : ℤ) :
    QFTMatrix M * momPhaseDiag M k * (QFTMatrix M)ᴴ = cyclicShift M k := by
  ext x z
  unfold cyclicShift momPhaseDiag
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def]
  have hconj : ∀ y : Fin M,
      (starRingEnd ℂ) (QFTMatrix M z y)
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹
            * primRoot M ^ (-((z.val : ℤ) * (y.val : ℤ))) := by
    intro y
    rw [qftMatrix_apply, map_mul, map_inv₀, Complex.conj_ofReal, primRoot_conj_zpow]
  have hterm : ∀ y : Fin M,
      (QFTMatrix M x y * momPhase M k y) * (starRingEnd ℂ) (QFTMatrix M z y)
        = (M : ℂ)⁻¹
            * primRoot M ^ (((x.val : ℤ) - k - (z.val : ℤ)) * (y.val : ℤ)) := by
    intro y
    rw [hconj y, qftMatrix_apply]
    unfold momPhase
    rw [show (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ ((x.val : ℤ) * (y.val : ℤ))
          * primRoot M ^ (-(k * (y.val : ℤ)))
          * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((z.val : ℤ) * (y.val : ℤ))))
        = primRoot M ^ ((x.val : ℤ) * (y.val : ℤ)) * primRoot M ^ (-(k * (y.val : ℤ)))
            * primRoot M ^ (-((z.val : ℤ) * (y.val : ℤ))) * (M : ℂ)⁻¹ from by
        rw [← inv_sqrt_mul_inv_sqrt hM]; ring]
    rw [← zpow_add₀ (primRoot_ne_zero M), ← zpow_add₀ (primRoot_ne_zero M), mul_comm]
    congr 2
    ring
  trans ∑ y : Fin M,
      (M : ℂ)⁻¹ * primRoot M ^ (((x.val : ℤ) - k - (z.val : ℤ)) * (y.val : ℤ))
  · apply Finset.sum_congr rfl
    intro y _
    exact hterm y
  · rw [← Finset.mul_sum]
    by_cases h : ((M : ℤ) ∣ ((x.val : ℤ) - k - (z.val : ℤ)))
    · rw [sum_primRoot_zpow_of_dvd hM h, ite_eq_left h]
      exact inv_mul_cancel₀ (by exact_mod_cast hM.ne' : (M : ℂ) ≠ 0)
    · rw [sum_primRoot_zpow hM h, ite_eq_right h, mul_zero]

/-- The cyclic translation matrix is unitary when `M > 0`. -/
theorem cyclicShift_unitary {M : ℕ} (hM : 0 < M) (k : ℤ) :
    cyclicShift M k ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  rw [← fourier_conj_diag_eq_shift hM k]
  have hQ : QFTMatrix M ∈ Matrix.unitaryGroup (Fin M) ℂ := qftMatrix_unitary hM
  have hQstar : (QFTMatrix M)ᴴ ∈ Matrix.unitaryGroup (Fin M) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hQ
  exact (Matrix.unitaryGroup (Fin M) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin M) ℂ).mul_mem hQ (momPhaseDiag_unitary hM k)) hQstar

/-- Applying a cyclic shift to the basis vector at `z₀` gives the indicator of `x = z₀ + k`
modulo `M`. -/
theorem cyclicShift_delta_mulVec {M : ℕ} (k : ℤ) (z₀ x : Fin M) :
    (cyclicShift M k).mulVec (fun z => if z = z₀ then (1 : ℂ) else 0) x
      = if ((M : ℤ) ∣ ((x.val : ℤ) - k - (z₀.val : ℤ))) then 1 else 0 := by
  simp only [Matrix.mulVec, dotProduct, cyclicShift]
  rw [Finset.sum_eq_single z₀]
  · simp
  · intro z _ hz
    simp [hz]
  · intro h
    exact absurd (Finset.mem_univ z₀) h

/-- For `M > 0`, the Fourier phase word sends the pointer basis vector at `z₀` to its
translation by `k` modulo `M`. -/
theorem fourier_word_delta {M : ℕ} (hM : 0 < M) (k : ℤ) (z₀ x : Fin M) :
    (QFTMatrix M * momPhaseDiag M k * (QFTMatrix M)ᴴ).mulVec
        (fun z => if z = z₀ then (1 : ℂ) else 0) x
      = if ((M : ℤ) ∣ ((x.val : ℤ) - k - (z₀.val : ℤ))) then 1 else 0 := by
  rw [fourier_conj_diag_eq_shift hM k]
  exact cyclicShift_delta_mulVec k z₀ x

end Qatlib.Papers.ThermalRate98.MainResults
