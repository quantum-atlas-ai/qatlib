/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedAlgebra

/-!
# Norm bounds for nearby weighted states

`nearbyLCUMean` is a finite real-weighted sum in a complex inner product space. The module
expands its squared norm in terms of pairwise inner products and bounds the norm loss of convex
combinations of nearby unit vectors, providing estimates for the LCU analysis of
[ChildsWiebe2012].

`nearby_signed_mix_norm_sq` expresses the squared norm of a signed mixture using the two
component norms and the norm of their sum.

## Main statements

* `nearbyLCUMean_loss_le`: bounds convex-mean norm loss by half the squared pairwise distance
  bound.
* `nearbyLCUMean_norm_le_one`: bounds a convex combination of unit vectors by one.
* `nearby_signed_mix_norm_sq`: gives the signed-mixture norm identity.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open scoped ComplexConjugate
variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The finite sum of the vectors `v j` with real coefficients `α j`, viewed as complex scalars. -/
def nearbyLCUMean (α : J→ℝ) (v : J→E) : E := ∑ j,(α j:ℂ) • v j

/-- The real part of the inner product of two real-scaled vectors is the product of their
scalars times the real part of the original inner product. -/
private theorem inner_real_weights (p q : ℝ) (A B : E) :
    (inner ℂ ((p:ℂ) • A) ((q:ℂ) • B)).re=p*q*(inner ℂ A B).re := by
  rw [inner_smul_left (𝕜 := ℂ),inner_smul_right (𝕜 := ℂ)]
  simp [Complex.mul_re]
  ring

/-- The squared norm of a real-weighted mean is the double sum of coefficient products times
real pairwise inner products. -/
theorem nearbyLCUMean_norm_sq (α : J→ℝ) (v : J→E) :
    ‖nearbyLCUMean α v‖^2=∑ i : J,∑ j : J,α i*α j*(inner ℂ (v i) (v j)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  unfold nearbyLCUMean
  simp only [sum_inner (𝕜 := ℂ),inner_sum (𝕜 := ℂ)]
  change (∑ i : J,∑ j : J,inner ℂ ((α i:ℂ) • v i) ((α j:ℂ) • v j)).re=_
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact inner_real_weights (α i) (α j) (v i) (v j)

/-- A convex combination of unit vectors whose pairwise squared distances are at most `Δ ^ 2`
has squared-norm loss at most `Δ ^ 2 / 2`. -/
theorem nearbyLCUMean_loss_le (α : J→ℝ) (v : J→E) (Δ : ℝ)
    (hα : ∀ j,0≤α j) (hsum : ∑ j,α j=1) (hv : ∀ j,‖v j‖=1)
    (hΔ : ∀ i j,‖v i-v j‖^2≤Δ^2) : 1-‖nearbyLCUMean α v‖^2≤Δ^2/2 := by
  have hp (i j : J) : 1-Δ^2/2≤(inner ℂ (v i) (v j)).re := by
    have hh := norm_sub_sq (𝕜 := ℂ) (v i) (v j)
    rw [hv i,hv j] at hh
    change ‖v i-v j‖^2=1^2-2*(inner ℂ (v i) (v j)).re+1^2 at hh
    nlinarith [hΔ i j]
  have hw : ∑ i : J,∑ j : J,α i*α j*(1-Δ^2/2) = 1-Δ^2/2 := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
    rw [hsum]
    ring
  have hh : ∑ i : J,∑ j : J,α i*α j*(1-Δ^2/2) ≤
      ∑ i : J,∑ j : J,α i*α j*(inner ℂ (v i) (v j)).re := by
    exact Finset.sum_le_sum (fun i _=>Finset.sum_le_sum
      (fun j _=>mul_le_mul_of_nonneg_left (hp i j) (mul_nonneg (hα i) (hα j))))
  rw [hw,← nearbyLCUMean_norm_sq] at hh
  linarith

/-- A convex combination of unit vectors has norm at most one. -/
theorem nearbyLCUMean_norm_le_one (α : J→ℝ) (v : J→E)
    (hα : ∀ j,0≤α j) (hsum : ∑ j,α j=1) (hv : ∀ j,‖v j‖=1) : ‖nearbyLCUMean α v‖≤1 := by
  unfold nearbyLCUMean
  calc _≤∑ j : J,‖(α j:ℂ) • v j‖ := norm_sum_le _ _
    _=1 := by
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hα _),hv,mul_one];exact hsum

/-- When `p + q = 1`, the squared norm of `p • A - q • B` equals `p * ‖A‖ ^ 2 + q * ‖B‖ ^ 2 - p
* q * ‖A + B‖ ^ 2`. -/
theorem nearby_signed_mix_norm_sq (p q : ℝ) (hpq : p+q=1) (A B : E) :
    ‖(p:ℂ) • A-(q:ℂ) • B‖^2 =
      p*‖A‖^2+q*‖B‖^2-p*q*‖A+B‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ),norm_add_sq (𝕜 := ℂ)]
  change ‖(p:ℂ) • A‖^2-2*(inner ℂ ((p:ℂ) • A) ((q:ℂ) • B)).re+‖(q:ℂ) • B‖^2 =
    p*‖A‖^2+q*‖B‖^2-p*q*(‖A‖^2+2*(inner ℂ A B).re+‖B‖^2)
  rw [inner_real_weights]
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]
  linear_combination ‖A‖^2*p*hpq+‖B‖^2*q*hpq
end Qatlib.Papers.HamLCUSim12.LCUDeferred
