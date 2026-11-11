/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellLowMean

set_option backward.isDefEq.respectTransparency false

/-!
# Low Spin Loss Bridge

Low Spin Loss Bridge constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators

variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
/-- Complete original `spinor_bell_probability_identity` guarantee for `LowSpinLossBridge`; all source hypotheses and output obligations are retained. -/
theorem spinor_bell_probability_identity (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (x y : S) :
    4*bellProbability (complexSpinor a b c k x) (complexSpinor a b c k y)=
      1-∑ i : Fin 3,pauliField a b c k i x*pauliField a b c k i y := by
  have hd := bell_probability_eq_bloch_distance (complexSpinor a b c k x)
    (complexSpinor a b c k y) (complex_spinor_mass a b c k hz x)
    (complex_spinor_mass a b c k hz y)
  rw [complex_spinor_bloch,complex_spinor_bloch] at hd
  have hs := pauli_field_unit a b c k hz
  have hdiff : (∑ i : Fin 3,(pauliField a b c k i x-pauliField a b c k i y)^2)=
      2-2*(∑ i : Fin 3,pauliField a b c k i x*pauliField a b c k i y) := by
    have hp (i : Fin 3) :
        (pauliField a b c k i x-pauliField a b c k i y)^2=
          (pauliField a b c k i x)^2+(pauliField a b c k i y)^2-
            2*(pauliField a b c k i x*pauliField a b c k i y) := by ring
    simp_rw [hp,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [hs x,hs y]
    ring
  rw [hdiff] at hd
  linarith

/-- Complete original `bell_mean_as_spin_correlation` guarantee for `LowSpinLossBridge`; all source hypotheses and output obligations are retained. -/
theorem bell_mean_as_spin_correlation (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : S → S) :
    4*bellMean a b c k τ=
      1-∑ i : Fin 3,siteMean (fun x => pauliField a b c k i x*pauliField a b c k i (τ x)) := by
  change 4*siteMean (fun x => bellProbability (complexSpinor a b c k x)
    (complexSpinor a b c k (τ x)))=_
  rw [← site_mean_mul]
  calc
    _ = siteMean (fun x => 1-∑ i : Fin 3,
        pauliField a b c k i x*pauliField a b c k i (τ x)) := by
      apply congrArg siteMean
      funext x
      exact spinor_bell_probability_identity a b c k hz x (τ x)
    _ = _ := by rw [site_mean_sub,site_mean_const,site_mean_sum]

/-- Complete original `bell_spin_term_identity` guarantee for `LowSpinLossBridge`; all source hypotheses and output obligations are retained. -/
theorem bell_spin_term_identity {d : ℕ} (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Fin d → S → S) (γ : ℝ) :
    4*γ*(∑ j : Fin d,bellMean a b c k (τ j))=
      γ*((d : ℝ)-∑ i : Fin 3 × Fin d,
        siteMean (fun x => pauliField a b c k i.1 x*pauliField a b c k i.1 (τ i.2 x))) := by
  have hswap : (∑ j : Fin d,∑ i : Fin 3,
      siteMean (fun x => pauliField a b c k i x*pauliField a b c k i (τ j x)))=
        ∑ i : Fin 3 × Fin d,
          siteMean (fun x => pauliField a b c k i.1 x*pauliField a b c k i.1 (τ i.2 x)) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  calc
    _ = γ*(∑ j : Fin d,4*bellMean a b c k (τ j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = γ*(∑ j : Fin d,(1-∑ i : Fin 3,
        siteMean (fun x => pauliField a b c k i x*pauliField a b c k i (τ j x)))) := by
      simp_rw [bell_mean_as_spin_correlation a b c k hz]
    _ = _ := by
      rw [Finset.sum_sub_distrib,hswap]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

/-- Complete original `bell_spin_term_range` guarantee for `LowSpinLossBridge`; all source hypotheses and output obligations are retained. -/
theorem bell_spin_term_range {d : ℕ} (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Fin d → S → S)
    (γ : ℝ) (hγ : 0≤γ) :
    0≤4*γ*(∑ j : Fin d,bellMean a b c k (τ j)) ∧
      4*γ*(∑ j : Fin d,bellMean a b c k (τ j))≤2*(d : ℝ)*γ := by
  rw [bell_spin_term_identity a b c k hz τ γ]
  exact spin_total_mean_range (pauliField a b c k) (pauli_field_unit a b c k hz) τ γ hγ

/-- Complete original `implemented_loss_bell_form` guarantee for `LowSpinLossBridge`; all source hypotheses and output obligations are retained. -/
theorem implemented_loss_bell_form {d : ℕ} (mv u : Fin d → S → ℝ) (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Fin d → Equiv.Perm S) (α β γ : ℝ) :
    implementedResidualLoss mv u (pauliField a b c k) τ α β γ=
      (∑ j : Fin d,siteMean (fun x => (α*mv j x-β*u j x)^2))+
        4*γ*(∑ j : Fin d,bellMean a b c k (τ j)) := by
  rw [bell_spin_term_identity a b c k hz (fun j => τ j) γ]
  rfl

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.spinor_bell_probability_identity
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_mean_as_spin_correlation
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_spin_term_identity
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_spin_term_range
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.implemented_loss_bell_form
