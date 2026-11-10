/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelCircleBounds
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators

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

def finitePoleRadius (s : Finset ℂ) : ℝ := 1 + ∑ p ∈ s, ‖p‖

theorem finitePoleRadius_ge_one (s : Finset ℂ) : 1 ≤ finitePoleRadius s := by
  have h : 0 ≤ ∑ p ∈ s, ‖p‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  dsimp [finitePoleRadius]
  linarith

theorem norm_le_finitePoleRadius (s : Finset ℂ) (p : ℂ) (hp : p ∈ s) :
    ‖p‖ ≤ finitePoleRadius s := by
  have h := Finset.single_le_sum (fun q (_ : q ∈ s) => norm_nonneg q) hp
  dsimp [finitePoleRadius]
  linarith

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
