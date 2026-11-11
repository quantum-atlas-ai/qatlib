/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

set_option backward.isDefEq.respectTransparency false

/-!
# Prior Moments

Moments of the unique original independent sign-pair prior factor over actual pair labels.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorMoments
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation

/-- Moments of the unique original independent sign-pair prior factor over actual pair labels. -/
theorem product_moment {E : Type*} [Fintype E] [DecidableEq E] (ρ : ℝ) (f : E → Fin 4 → ℝ) :
    (∑ κ : E → Fin 4,pairedSignLaw ρ κ*(∏ e,f e (κ e)))=
      ∏ e,∑ i : Fin 4,signPairLaw ρ i*f e i := by
  simp only [pairedSignLaw,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun e i => signPairLaw ρ i*f e i)).symm

/-- The original finite pair law retains exactly the source's first-sign mean, second-sign mean and correlation. -/
theorem single_sign_moments (ρ : ℝ) :
    (∑ i : Fin 4,signPairLaw ρ i*firstSign i)=0 ∧
    (∑ i : Fin 4,signPairLaw ρ i*secondSign i)=0 ∧
    (∑ i : Fin 4,signPairLaw ρ i*firstSign i*secondSign i)=ρ := by
  norm_num [Fin.sum_univ_succ,signPairLaw,firstSign,secondSign]
  ring

/-- A one-coordinate actual prior marginal is the same original four-sign law. -/
theorem single_moment {E : Type*} [Fintype E] [DecidableEq E] (ρ : ℝ)
    (hlo : -1≤ρ) (hhi : ρ≤1) (e : E) (f : Fin 4 → ℝ) :
    (∑ κ : E → Fin 4,pairedSignLaw ρ κ*f (κ e))=∑ i : Fin 4,signPairLaw ρ i*f i := by
  have ht (κ : E → Fin 4) : f (κ e)=∏ j : E,if j=e then f (κ j) else 1 :=
    (Fintype.prod_ite_eq' e (fun j => f (κ j))).symm
  simp_rw [ht]
  rw [product_moment ρ (fun j i => if j=e then f i else 1)]
  have hw := (signPairLaw_prob ρ hlo hhi).2
  have hs (j : E) : (∑ i : Fin 4,signPairLaw ρ i*(if j=e then f i else 1))=
      if j=e then (∑ i : Fin 4,signPairLaw ρ i*f i) else 1 := by
    by_cases h : j=e
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h,mul_one,hw]
  simp_rw [hs]
  exact Fintype.prod_ite_eq' e (fun _ => ∑ i : Fin 4,signPairLaw ρ i*f i)

/-- Distinct actual pair coordinates have the original independent product marginal. -/
theorem distinct_moment {E : Type*} [Fintype E] [DecidableEq E] (ρ : ℝ)
    (hlo : -1≤ρ) (hhi : ρ≤1) (e z : E) (hez : e≠z) (f g : Fin 4 → ℝ) :
    (∑ κ : E → Fin 4,pairedSignLaw ρ κ*f (κ e)*g (κ z))=
      (∑ i : Fin 4,signPairLaw ρ i*f i)*(∑ i : Fin 4,signPairLaw ρ i*g i) := by
  have ht (κ : E → Fin 4) : f (κ e)*g (κ z)=
      ∏ j : E,(if j=e then f (κ j) else 1)*(if j=z then g (κ j) else 1) := by
    rw [Finset.prod_mul_distrib,Fintype.prod_ite_eq',Fintype.prod_ite_eq']
  simp_rw [mul_assoc,ht]
  rw [product_moment ρ (fun j i => (if j=e then f i else 1)*(if j=z then g i else 1))]
  have hw := (signPairLaw_prob ρ hlo hhi).2
  have hs (j : E) :
      (∑ i : Fin 4,signPairLaw ρ i*((if j=e then f i else 1)*(if j=z then g i else 1)))=
      (if j=e then (∑ i : Fin 4,signPairLaw ρ i*f i) else 1)*
        (if j=z then (∑ i : Fin 4,signPairLaw ρ i*g i) else 1) := by
    by_cases hje : j=e
    · subst j
      simp only [ite_true,ite_eq_right hez,mul_one]
    · by_cases hjz : j=z
      · simp only [ite_eq_right hje,ite_eq_left hjz,one_mul]
      · simp only [ite_eq_right hje,ite_eq_right hjz,mul_one,hw]
  simp_rw [hs]
  rw [Finset.prod_mul_distrib,Fintype.prod_ite_eq',Fintype.prod_ite_eq']

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorMoments
