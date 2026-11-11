/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelCircleBounds

/-!
# Radial bounds for finite pole sets

`finitePoleRadius` gives an explicit radius containing a finite complex pole set. For a nonempty
pole set bounded by `B ≥ 1`, `finite_pole_denominator_lower` bounds the product of pole
distances and the target distance from below outside radius `B + 1`.

These estimates control rational contour kernels in the framework of [WangEtAl2026].

## Main statements

* `finite_pole_denominator_lower`: gives a quadratic radial lower bound.
* `norm_le_finitePoleRadius`: places every pole inside the chosen radius.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators

/-- If a nonempty pole set has norms at most `B ≥ 1` and `‖z‖ ≥ B + 1`, then `‖z + i‖` times the
product of pole distances is at least `(‖z‖ - B) ^ 2`. -/
theorem finite_pole_denominator_lower (s : Finset ℂ) (hs : s.Nonempty)
    (B : ℝ) (hB : 1 ≤ B) (hp : ∀ p ∈ s, ‖p‖ ≤ B)
    (z : ℂ) (hz : B + 1 ≤ ‖z‖) :
    (‖z‖ - B) ^ 2 ≤ ‖z + Complex.I‖ * ∏ p ∈ s, ‖z - p‖ := by
  have hd : 1 ≤ ‖z‖ - B := by linarith
  have hprod : (‖z‖ - B) ^ s.card ≤ ∏ p ∈ s, ‖z - p‖ := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ => by linarith)
    intro p hps
    have h := norm_sub_norm_le z p
    linarith [hp p hps]
  have hI : ‖z‖ - B ≤ ‖z + Complex.I‖ := by
    have h := norm_sub_norm_le z (-Complex.I)
    simp only [norm_neg, Complex.norm_I, sub_neg_eq_add] at h
    linarith
  calc
    _ ≤ (‖z‖ - B) ^ (s.card + 1) := pow_le_pow_right₀ hd (by simpa using hs.card_pos)
    _ = (‖z‖ - B) * (‖z‖ - B) ^ s.card := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul hI hprod (by positivity) (norm_nonneg _)

/-- The explicit pole radius `1 + ∑ p ∈ s, ‖p‖`. -/
def finitePoleRadius (s : Finset ℂ) : ℝ := 1 + ∑ p ∈ s, ‖p‖

/-- The finite pole radius is at least one. -/
theorem finitePoleRadius_ge_one (s : Finset ℂ) : 1 ≤ finitePoleRadius s := by
  have h : 0 ≤ ∑ p ∈ s, ‖p‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  dsimp [finitePoleRadius]
  linarith

/-- Every member of a finite pole set has norm at most its finite pole radius. -/
theorem norm_le_finitePoleRadius (s : Finset ℂ) (p : ℂ) (hp : p ∈ s) :
    ‖p‖ ≤ finitePoleRadius s := by
  have h := Finset.single_le_sum (fun q (_ : q ∈ s) => norm_nonneg q) hp
  dsimp [finitePoleRadius]
  linarith

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
