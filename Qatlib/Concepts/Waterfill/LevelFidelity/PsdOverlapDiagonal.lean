/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Positive semidefinite overlap bound

The theorem `psd_weighted_overlap_diagonal` bounds a weighted quadratic form of a positive
semidefinite complex matrix using only its real diagonal entries. Nonnegative weights turn
entrywise positivity bounds into a bound by a squared diagonal sum, as used in water-fill
overlap estimates related to [OzolsRoettelerRoland2013].

## Main statements

* `psd_weighted_overlap_diagonal`: Bound weighted overlap by the squared weighted diagonal-root
  sum.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.Waterfill.LevelFidelity
open Matrix
open scoped BigOperators ComplexOrder

/-- For a positive semidefinite complex matrix and nonnegative real weights, the real part of
the weighted quadratic sum is at most the square of the weighted sum of square roots of its
diagonal entries. -/
theorem psd_weighted_overlap_diagonal (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ)
    (σ : Fin m → ℝ) (hM : M.PosSemidef) (hσ : ∀ i, 0 ≤ σ i) :
    (∑ i, ∑ j, (σ i : ℂ) * M i j * (σ j : ℂ)).re ≤
      (∑ i, σ i * Real.sqrt (M i i).re) ^ 2 := by
  classical
  letI := M.toSeminormedAddCommGroup hM
  letI := M.toInnerProductSpace hM
  letI : Norm (Fin m → ℂ) := (M.toSeminormedAddCommGroup hM).toNorm
  letI : NormedSpace ℂ (Fin m → ℂ) := (M.toInnerProductSpace hM).toNormedSpace
  let v : Fin m → ℂ := fun i => (σ i : ℂ)
  have hn (w : Fin m → ℂ) : ‖w‖ = Real.sqrt ((M *ᵥ w) ⬝ᵥ star w).re := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    rfl
  have he (i : Fin m) : ‖(Pi.single i (1 : ℂ) : Fin m → ℂ)‖ = Real.sqrt (M i i).re := by
    rw [hn]
    have hs : star (Pi.single i (1 : ℂ) : Fin m → ℂ) = Pi.single i (1 : ℂ) := by
      ext j
      simp [Pi.star_apply, Pi.single_apply]
    rw [hs, Matrix.mulVec_single_one, dotProduct_single_one]
    rfl
  have hv : v = ∑ i : Fin m, (σ i : ℂ) • (Pi.single i (1 : ℂ) : Fin m → ℂ) := by
    ext j
    simp [v, Finset.sum_apply, Pi.single_apply]
  have hbound : ‖v‖ ≤ ∑ i : Fin m, σ i * Real.sqrt (M i i).re := by
    rw [hv]
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_smul, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ i)]
  have hquad : (∑ i, ∑ j, (σ i : ℂ) * M i j * (σ j : ℂ)).re = ‖v‖ ^ 2 := by
    rw [hn, Real.sq_sqrt]
    · congr 1
      simp only [Matrix.mulVec, dotProduct, Pi.star_apply, v, Complex.star_def,
        Complex.conj_ofReal, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simpa only [dotProduct_comm] using! hM.re_dotProduct_nonneg v
  rw [hquad]
  have hn0 : 0 ≤ ‖v‖ := by rw [hn]; exact Real.sqrt_nonneg _
  nlinarith

end Qatlib.Concepts.Waterfill.LevelFidelity
