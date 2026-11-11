/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressTrainedOriginal

set_option backward.isDefEq.respectTransparency false

/-!
Unrotated matching confidence with the actual q=1/2 production count.
The real minority bound is 1, not 1/2. Existing variance constants leave enough
slack in the same integer budget; no minority promise is accepted as input.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.Functional
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open RetainedSpin UniformMatching
variable {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]

omit [DecidableEq E] in
/-- Complete original `actual_minority_one` guarantee for `PartialAddressUnrotated`; all source hypotheses and output obligations are retained. -/
theorem actual_minority_one (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1) :
    average (fun e => sectorMass (u e) (v e) true)≤1 := by
  have hp (e : E) : sectorMass (u e) (v e) true≤1 := by
    have ht := sector_mass_total (u e) (v e) (hu e) (hv e)
    have hn := sector_mass_nonneg (u e) (v e) false
    linarith
  have h := average_mono _ (fun _ => (1 : ℝ)) hp
  simpa [average] using h

-- q=1/2 here specifies the production count, not a false minority promise.
/-- Complete original `unrotated_count_confidence` guarantee for `PartialAddressUnrotated`; all source hypotheses and output obligations are retained. -/
theorem unrotated_count_confidence (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (ε δ : ℚ) (hε : 0<ε) (hδ : 0<δ) :
    (law u v hu hv).probEvent (fun ω : Fin (xyzCountQ (2*Fintype.card E) (1/2) ε δ) → GlobalRecord E =>
      (ε : ℝ)< |(CountMap.sparseCountValueQ ω : ℝ)-average (fun e => bellProbability (u e) (v e))|)≤(δ : ℝ) := by
  simp only [CountMap.sparse_value_eq_ustatistic]
  let n := xyzCountQ (2*Fintype.card E) (1/2) ε δ
  have hn2 : 2≤n := xyz_count_two _ (1/2) ε δ
  have hlin := xyz_count_linear_budget (2*Fintype.card E) (1/2) ε δ (by norm_num) hε hδ
  have hcol := xyz_count_collision_budget (2*Fintype.card E) (1/2) ε δ (by norm_num) hε hδ
  have heR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hdR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
  have hnR : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hden : (0 : ℝ)<((n*(n-1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0<n) (by omega : 0<n-1)
  have hfirst : 6/(n : ℝ)≤(δ : ℝ)*(ε : ℝ)^2/2 := by
    rw [div_le_iff₀ hnR]
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hlin
    change 16≤(n : ℝ)*((δ : ℝ)*(ε : ℝ)^2) at hlin
    nlinarith
  have hsecond : 30*(Fintype.card E : ℝ)/(n*(n-1) : ℕ)≤(δ : ℝ)*(ε : ℝ)^2/2 := by
    rw [div_le_iff₀ hden]
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_mul,Nat.cast_ofNat] at hcol ⊢
    change 100*(2*(Fintype.card E : ℝ))*(1/2)≤
      (n : ℝ)*((n-1 : ℕ) : ℝ)*((δ : ℝ)*(ε : ℝ)^2) at hcol
    nlinarith
  have hvar := actual_global_variance_bound u v hu hv hn2 1 (actual_minority_one u v hu hv)
  calc
    _ ≤ (∑ ω : Fin n → GlobalRecord E,(law u v hu hv).probOf ω*
        (orderedUStatistic globalKernel ω-average (fun e => bellProbability (u e) (v e)))^2)/(ε : ℝ)^2 :=
      product_chebyshev _ _ _ _ heR
    _ ≤ (6/(n : ℝ)+30*(Fintype.card E : ℝ)/(n*(n-1) : ℕ))/(ε : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [mul_one] using hvar
    _ ≤ (δ : ℝ) := by
      rw [div_le_iff₀ (sq_pos_of_pos heR)]
      linarith

/-- Complete original `checked_unrotated_confidence` guarantee for `PartialAddressUnrotated`; all source hypotheses and output obligations are retained. -/
theorem checked_unrotated_confidence (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (ε δ : ℚ) (n : ℕ) (hc : checkedXYZCountQ (2*Fintype.card E) (1/2) ε δ=some n) :
    (law u v hu hv).probEvent (fun ω : Fin n → GlobalRecord E =>
      (ε : ℝ)< |(CountMap.sparseCountValueQ ω : ℝ)-average (fun e => bellProbability (u e) (v e))|)≤(δ : ℝ) := by
  unfold checkedXYZCountQ at hc
  split_ifs at hc with h
  · have hn := Option.some.inj hc
    subst n
    exact unrotated_count_confidence u v hu hv ε δ h.2.2.1 h.2.2.2.1

#print axioms actual_minority_one
#print axioms unrotated_count_confidence
#print axioms checked_unrotated_confidence
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.Functional
