/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.ClassicalAnalogue

/-!
# The discriminant of the classical walk kernel

This module defines the diagonal rescaling `disc` and identifies it with the product of opposite
walk amplitudes when the joint amplitudes are symmetric. It also transports eigenvectors under
rescaling, supplying the discriminant identities used for Theorem 3.18 of [MagniezEtAl2008].

## Main statements

* `disc_eq_quantum`: identifies the rescaled classical kernel with the amplitude-product matrix.
* `disc_mulVec_similar`: transports an eigenvector by pointwise multiplication with the
  rescaling function.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

namespace WalkStructure

variable {X : Type*} [Fintype X]

/-- The pointwise square root of the probability weight `π`. -/
def sqrtPi (D : WalkStructure X) (x : X) : ℝ := Real.sqrt (D.π x)

/-- The matrix with entries `s x * p x y / s y`, representing diagonal rescaling of `p` when `s`
is nowhere zero. -/
def disc (s : X → ℝ) (p : X → X → ℝ) : Matrix X X ℝ := fun x y => s x * p x y / s y

/-- For positive `π` and symmetric joint amplitudes, the discriminant of the squared-amplitude
kernel equals the matrix `φ y x * φ x y`. -/
theorem disc_eq_quantum (D : WalkStructure X) (hπ : ∀ x, 0 < D.π x)
    (h : D.swapFixed) :
    disc (sqrtPi D) (fun x y => (D.φ x y) ^ 2) =
      (fun x y => D.φ y x * D.φ x y) := by
  funext x y
  have hsy : Real.sqrt (D.π y) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hπ y))
  have hrev : Real.sqrt (D.π x) * D.φ x y = Real.sqrt (D.π y) * D.φ y x := by
    have h1 := D.w_φ x y
    have h2 := D.w_φ y x
    have h3 := h x y
    rw [h1, h2] at h3
    exact h3
  simp only [disc, sqrtPi]
  field_simp [hsy]
  calc Real.sqrt (D.π x) * D.φ x y ^ 2
      = (Real.sqrt (D.π x) * D.φ x y) * D.φ x y := by ring
    _ = (Real.sqrt (D.π y) * D.φ y x) * D.φ x y := by rw [hrev]
    _ = D.φ x y * Real.sqrt (D.π y) * D.φ y x := by ring

/-- If `s` is nowhere zero, pointwise multiplication by `s` sends any eigenvector of `p` with
eigenvalue `μ` to an eigenvector of `disc s p` with the same eigenvalue. -/
theorem disc_mulVec_similar (s : X → ℝ) (hs : ∀ x, s x ≠ 0)
    (p : Matrix X X ℝ) (v : X → ℝ) (μ : ℝ)
    (hpv : p.mulVec v = μ • v) :
    (disc s p).mulVec (fun x => s x * v x) = μ • (fun x => s x * v x) := by
  ext x
  simp only [disc, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ y, s x * p x y / s y * (s y * v y)) =
      s x * ∑ y, p x y * v y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by field_simp [hs y])
  have hx := congrFun hpv x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx
  rw [hsum, hx]
  ring

/-- Under positive weights and symmetric joint amplitudes, combines the amplitude-product
discriminant identity with transport of a classical-kernel eigenvector. These are the
discriminant ingredients for Theorem 3.18 in [MagniezEtAl2008]. -/
theorem theorem_3_18_discriminant (D : WalkStructure X) (hπ : ∀ x, 0 < D.π x)
    (h : D.swapFixed) (v : X → ℝ) (μ : ℝ)
    (hpv : (Matrix.of (fun x y => (D.φ x y) ^ 2)).mulVec v = μ • v) :
    disc (sqrtPi D) (fun x y => (D.φ x y) ^ 2) =
        (fun x y => D.φ y x * D.φ x y) ∧
      (disc (sqrtPi D) (fun x y => (D.φ x y) ^ 2)).mulVec
          (fun x => sqrtPi D x * v x) = μ • (fun x => sqrtPi D x * v x) := by
  refine ⟨disc_eq_quantum D hπ h, ?_⟩
  exact disc_mulVec_similar (sqrtPi D)
    (fun x => ne_of_gt (Real.sqrt_pos.mpr (hπ x))) _ _ _ hpv

end WalkStructure

end Qatlib.Papers.HittingTimes08.MainResults
