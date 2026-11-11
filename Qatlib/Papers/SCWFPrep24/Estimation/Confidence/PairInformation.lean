/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPair
import Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Pair Information

A root fidelity bounded below by one quarter converts deficit into a uniform logarithmic loss.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification

/-- A root fidelity bounded below by one quarter converts deficit into a uniform logarithmic loss. -/
theorem log_lower_of_quarter (f : ℝ) (hlo : 1/4≤f) (hhi : f≤1) :
    -4*(1-f)≤Real.log f := by
  have hf : 0<f := by linarith
  have h := mul_le_mul_of_nonneg_right (Real.one_sub_inv_le_log_of_pos hf) (le_of_lt hf)
  have hi : f⁻¹*f=1 := inv_mul_cancel₀ (ne_of_gt hf)
  have hp := mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0≤4*f-1)
  apply (mul_le_mul_iff_left₀ hf).mp
  nlinarith

/-- The original physical conditional pair densities are legal normalized density operators. -/
theorem original_pair_density (N r s : ℕ) (hN : 256≤N) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    IsDensityOperator (physicalPairMixture (128/((N : ℝ)^2)) r s ρ) := by
  have hb := original_weak_excitation N hN
  have h := mixture_density (pairEven (128/((N : ℝ)^2)) r s)
    (pairOdd (128/((N : ℝ)^2)) r s)
    (physical_source_normalized (128/((N : ℝ)^2)) r s hb.1 (by linarith)) ρ hlo hhi
  rw [physical_source_eq] at h
  exact h

/-- Each original conditional pair gives the source's exponential information factor without a supplied fidelity certificate. -/
theorem original_conditional_pair_exp (N r s : ℕ) (hN : 256≤N) :
    Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*(min r s : ℕ))≤
      Froot (physicalPairMixture (128/((N : ℝ)^2)) r s (3/4))
        (physicalPairMixture (128/((N : ℝ)^2)) r s (-3/4)) := by
  have hlo := original_conditional_pair_floor N r s hN
  have hinf := original_conditional_pair_information N r s hN
  have hρ := original_pair_density N r s hN (3/4) (by norm_num) (by norm_num)
  have hσ := original_pair_density N r s hN (-3/4) (by norm_num) (by norm_num)
  have hhi := (g1 _ _ _ hρ hσ).2.1.2.1
  have hl := log_lower_of_quarter _ hlo hhi
  have hp : 0<Froot (physicalPairMixture (128/((N : ℝ)^2)) r s (3/4))
      (physicalPairMixture (128/((N : ℝ)^2)) r s (-3/4)) := by linarith
  rw [←Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  linarith

/-- The product of genuine count-indexed pair fidelities, without a supplied tensor-fidelity certificate. -/
def actualPairProduct {E : Type} [Fintype E] [DecidableEq E] {Q : ℕ}
    (N : ℕ) (y : Fin Q → E × Bool) : ℝ :=
  ∏ e : E,Froot
    (physicalPairMixture (128/((N : ℝ)^2))
      (Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases.multiplicity y (e,false))
      (Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases.multiplicity y (e,true)) (3/4))
    (physicalPairMixture (128/((N : ℝ)^2))
      (Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases.multiplicity y (e,false))
      (Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases.multiplicity y (e,true)) (-3/4))

open Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Conditional pair information multiplies over every actual matching cohort, with zero counts retained. -/
theorem actualPairProduct_exp {E : Type} [Fintype E] [DecidableEq E] {Q : ℕ}
    (N : ℕ) (hN : 256≤N) (y : Fin Q → E × Bool) :
    Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*(pairedMinCount y : ℝ))≤actualPairProduct N y := by
  calc
    _ = ∏ e : E,Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
        (min (multiplicity y (e,false)) (multiplicity y (e,true)) : ℕ)) := by
      rw [pairedMinCount,Nat.cast_sum,Finset.mul_sum,Real.exp_sum]
    _ ≤ _ := Finset.prod_le_prod₀ (fun e _ => (Real.exp_pos _).le)
      (fun e _ => original_conditional_pair_exp N _ _ hN)

/-- The true address product law gives the actual Jensen lower bound for the mean pair product. -/
theorem actualPairProduct_expect_exp {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (N Q : ℕ) (hN : 256≤N) :
    Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
      (uniformCopyLaw (E × Bool) Q).expect (fun y => (pairedMinCount y : ℝ)))≤
        (uniformCopyLaw (E × Bool) Q).expect (actualPairProduct N) := by
  let p := uniformCopyLaw (E × Bool) Q
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p.prob)
    (p := fun y : Fin Q → E × Bool => -(216/7 : ℝ)*(128/((N : ℝ)^2))*(pairedMinCount y : ℝ))
    (fun y _ => p.nonneg y) (by simpa only using p.sum_one) (fun _ _ => Set.mem_univ _)
  have he : (∑ y,p.prob y*(-(216/7 : ℝ)*(128/((N : ℝ)^2))*(pairedMinCount y : ℝ)))=
      -(216/7 : ℝ)*(128/((N : ℝ)^2))*p.expect (fun y => (pairedMinCount y : ℝ)) := by
    unfold FinDist.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [smul_eq_mul,he] at hj
  exact hj.trans (Finset.sum_le_sum (fun y _ =>
    mul_le_mul_of_nonneg_left (actualPairProduct_exp N hN y) (p.nonneg y)))

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The original exponent at both collision scales follows from actual pair fidelities and true address moments; the global quantum fidelity connection remains separate. -/
theorem actualPairProduct_squared_scale {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (N Q : ℕ) (hN : 256≤ N) :
    Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
      min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/(Fintype.card (E × Bool) : ℝ)))≤
        ((uniformCopyLaw (E × Bool) Q).expect (actualPairProduct N))^2 := by
  let p := uniformCopyLaw (E × Bool) Q
  let H := p.expect (fun y => (pairedMinCount y : ℝ))
  let c : ℝ := (216/7)*(128/((N : ℝ)^2))
  have hc : 0≤ c := by dsimp [c]; positivity
  have hM : (Fintype.card (E × Bool) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hH : 2*H≤ min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/(Fintype.card (E × Bool) : ℝ)) := by
    apply le_min
    · have h := pairedMinCount_expect_half (E := E) Q
      change H≤(Q : ℝ)/2 at h
      linarith
    · have h := pairedMinCount_expect_collision (E := E) Q
      change H≤(Q : ℝ)*((Q : ℝ)-1)/(2*(Fintype.card (E × Bool) : ℝ)) at h
      calc
        2*H≤2*((Q : ℝ)*((Q : ℝ)-1)/(2*(Fintype.card (E × Bool) : ℝ))) := by linarith
        _ = _ := by field_simp [hM]
  have hmean : Real.exp (-c*H)≤ p.expect (actualPairProduct N) :=
    by simpa only [p,H,c,neg_mul] using actualPairProduct_expect_exp (E := E) N Q hN
  have hsq : (Real.exp (-c*H))^2≤(p.expect (actualPairProduct N))^2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hmean 2
  have hpow : (Real.exp (-c*H))^2=Real.exp (-c*(2*H)) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [hpow] at hsq
  calc
    _ = Real.exp (-c*min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/(Fintype.card (E × Bool) : ℝ))) := by
      congr 1
      dsimp [c]
      ring
    _ ≤ Real.exp (-c*(2*H)) := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hH hc])
    _ ≤ _ := hsq

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence
