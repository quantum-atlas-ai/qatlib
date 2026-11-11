/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinLossBridge

set_option backward.isDefEq.respectTransparency false

/-!
# Full Loss Nuisance

The actual complete loss retains a uniformly bounded velocity nuisance for every pointwise normalized sign and phase realization.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The actual complete loss retains a uniformly bounded velocity nuisance for every pointwise normalized sign and phase realization. -/
theorem original_full_loss_velocity_nuisance {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]
    {d : ℕ} (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (e : Fin d → Equiv.Perm S) (h lam : ℝ) (hh : h≠0) :
    0≤ spinorDiscreteLoss a b c k (fun _ _ => 0) e h 1 lam-
      (2*lam^2/h^2)*(∑ j : Fin d,bellMean a b c k ((e j).trans (e j))) ∧
    spinorDiscreteLoss a b c k (fun _ _ => 0) e h 1 lam-
      (2*lam^2/h^2)*(∑ j : Fin d,bellMean a b c k ((e j).trans (e j)))≤(d : ℝ)/h^2 := by
  have hc : 4*(lam^2/(2*h^2))=2*lam^2/h^2 := by field_simp; ring
  have hl := spinor_discrete_loss_eq a b c k hz (fun _ _ => 0) e h 1 lam hh one_ne_zero
  rw [implemented_loss_bell_form _ _ a b c k hz] at hl
  simp only [one_div,mul_zero,sub_zero] at hl
  rw [hc] at hl
  rw [hl,add_sub_cancel_right]
  constructor
  · exact Finset.sum_nonneg (fun j _ => site_mean_nonneg _ (fun _ => sq_nonneg _))
  · have hpoint (j : Fin d) : siteMean (fun x => (h⁻¹*spinorCurrentMean a b c k e j x)^2)≤1/h^2 := by
      have hs (x : S) : |(h⁻¹*spinorCurrentMean a b c k e j x)^2|≤1/h^2 := by
        have hb := abs_le.mp (spinor_current_mean_bound a b c k hz e j x)
        have hm : (spinorCurrentMean a b c k e j x)^2≤1 := by nlinarith
        rw [abs_of_nonneg (sq_nonneg _),mul_pow,inv_pow,one_div]
        exact mul_le_of_le_one_right (inv_nonneg.mpr (sq_nonneg h)) hm
      exact (le_abs_self _).trans (site_mean_abs_le_bound _ _ hs)
    calc
      _ ≤ ∑ _j : Fin d,1/h^2 := Finset.sum_le_sum (fun j _ => hpoint j)
      _ = _ := by simp [div_eq_mul_inv]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence
