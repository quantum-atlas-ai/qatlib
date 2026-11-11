/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorMoments
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPromise
import Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

set_option backward.isDefEq.respectTransparency false

/-!
# Matching Energy

The two signs belonging to an actual sampled pair label.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The two signs belonging to an actual sampled pair label. -/
def siteSign {E : Type*} (κ : E → Fin 4) (a : E × Bool) : ℝ :=
  if a.2 then secondSign (κ a.1) else firstSign (κ a.1)

/-- Every actual pair label gives unit signs on both vertices. -/
theorem siteSign_unit {E : Type*} (κ : E → Fin 4) (a : E × Bool) : (siteSign κ a)^2=1 := by
  have h (i : Fin 4) : (firstSign i)^2=1 ∧ (secondSign i)^2=1 := by
    fin_cases i <;> norm_num [firstSign,secondSign]
  unfold siteSign
  split_ifs
  · exact (h (κ a.1)).2
  · exact (h (κ a.1)).1

/-- The actual weak-spin Bell value on one directed graph edge. -/
def edgeBell {E : Type*} (b : ℝ) (κ : E → Fin 4) (a z : E × Bool) : ℝ :=
  bellProbability (pairedWeakSpin b κ a) (pairedWeakSpin b κ z)

/-- Every actual edge value has the original weak-state range. -/
theorem edgeBell_range {E : Type*} (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1)
    (κ : E → Fin 4) (a z : E × Bool) : 0≤edgeBell b κ a z ∧ edgeBell b κ a z≤2*b := by
  constructor
  · exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  · exact weakSpin_bell_le b (siteSign κ a) (siteSign κ z) hb0 hb1
      (siteSign_unit κ a) (siteSign_unit κ z)

/-- An indicator records the two actual vertices controlled by one pair variable. -/
def affected {E : Type*} [DecidableEq E] (e : E) (a : E × Bool) : ℝ := if a.1=e then 1 else 0

/-- One pair variable controls exactly its two actual site labels. -/
theorem affected_sum {E : Type*} [Fintype E] [DecidableEq E] (e : E) :
    (∑ a : E × Bool,affected e a)=2 := by
  rw [Fintype.sum_prod_type]
  simp only [affected,Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  norm_num

/-- Every actual permutation has exactly two incoming vertices controlled by the same pair variable. -/
theorem affected_perm_sum {E : Type*} [Fintype E] [DecidableEq E]
    (e : E) (τ : Equiv.Perm (E × Bool)) : (∑ a,affected e (τ a))=2 :=
  (Equiv.sum_comp τ (affected e)).trans (affected_sum e)

/-- A change of one actual pair variable affects only the two incident endpoint labels. -/
theorem edge_change {E : Type*} [Fintype E] [DecidableEq E]
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (e : E) (κ ξ : E → Fin 4)
    (hκ : ∀ f,f≠e → κ f=ξ f) (a z : E × Bool) :
    |edgeBell b κ a z-edgeBell b ξ a z|≤2*b*(affected e a+affected e z) := by
  have hp := edgeBell_range b hb0 hb1 κ a z
  have hq := edgeBell_range b hb0 hb1 ξ a z
  have hm : |edgeBell b κ a z-edgeBell b ξ a z|≤2*b := abs_le.mpr ⟨by linarith,by linarith⟩
  by_cases ha : a.1=e
  · by_cases hz : z.1=e
    · simp only [affected,ite_eq_left ha,ite_eq_left hz]
      linarith
    · simp only [affected,ite_eq_left ha,ite_eq_right hz,add_zero,mul_one]
      exact hm
  · by_cases hz : z.1=e
    · simp only [affected,ite_eq_right ha,ite_eq_left hz,zero_add,mul_one]
      exact hm
    · have hleft : pairedWeakSpin b κ a=pairedWeakSpin b ξ a := by
        simp only [pairedWeakSpin,hκ _ ha]
      have hright : pairedWeakSpin b κ z=pairedWeakSpin b ξ z := by
        simp only [pairedWeakSpin,hκ _ hz]
      simp only [edgeBell,hleft,hright,sub_self,abs_zero,affected,ite_eq_right ha,ite_eq_right hz,add_zero,mul_zero]
      exact le_rfl

/-- The actual original Bell spin energy on a finite permutation graph. -/
def spinEnergy {E : Type} [Fintype E] {d : ℕ} (b G : ℝ)
    (τ : Fin d → Equiv.Perm (E × Bool)) (κ : E → Fin 4) : ℝ :=
  (G/(Fintype.card (E × Bool) : ℝ))*(∑ j : Fin d,∑ a : E × Bool,edgeBell b κ a (τ j a))

/-- The source's bounded-difference constant is derived from actual Bell values and actual incoming/outgoing permutations. -/
theorem spinEnergy_coordinate_change {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {d : ℕ} (b G : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hG : 0≤G)
    (τ : Fin d → Equiv.Perm (E × Bool)) (e : E) (κ ξ : E → Fin 4)
    (hκ : ∀ f,f≠e → κ f=ξ f) :
    |spinEnergy b G τ κ-spinEnergy b G τ ξ|≤8*(d : ℝ)*G*b/(Fintype.card (E × Bool) : ℝ) := by
  have hj (j : Fin d) : (∑ a : E × Bool,|edgeBell b κ a (τ j a)-edgeBell b ξ a (τ j a)|)≤8*b := by
    calc
      _ ≤ ∑ a : E × Bool,2*b*(affected e a+affected e (τ j a)) :=
        Finset.sum_le_sum (fun a _ => edge_change b hb0 hb1 e κ ξ hκ a (τ j a))
      _ = _ := by
        rw [←Finset.mul_sum,Finset.sum_add_distrib,affected_sum,affected_perm_sum]
        ring
  have hs : |∑ j : Fin d,∑ a : E × Bool,(edgeBell b κ a (τ j a)-edgeBell b ξ a (τ j a))|≤(d : ℝ)*(8*b) := by
    calc
      _ ≤ ∑ j : Fin d,|∑ a : E × Bool,(edgeBell b κ a (τ j a)-edgeBell b ξ a (τ j a))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d,∑ a : E × Bool,|edgeBell b κ a (τ j a)-edgeBell b ξ a (τ j a)| :=
        Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _j : Fin d,8*b := Finset.sum_le_sum (fun j _ => hj j)
      _ = _ := by simp
  have hc : 0≤G/(Fintype.card (E × Bool) : ℝ) := div_nonneg hG (Nat.cast_nonneg _)
  calc
    _ = (G/(Fintype.card (E × Bool) : ℝ))*
        |∑ j : Fin d,∑ a : E × Bool,(edgeBell b κ a (τ j a)-edgeBell b ξ a (τ j a))| := by
      unfold spinEnergy
      rw [←mul_sub,abs_mul,abs_of_nonneg hc]
      simp only [Finset.sum_sub_distrib]
    _ ≤ (G/(Fintype.card (E × Bool) : ℝ))*((d : ℝ)*(8*b)) := mul_le_mul_of_nonneg_left hs hc
    _ = _ := by ring

open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

/-- The unique original four-sign probabilities bundled for actual independent sampling. -/
def singleSignLaw (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) : FinDist (Fin 4) where
  prob := signPairLaw ρ
  nonneg := (signPairLaw_prob ρ hlo hhi).1
  sum_one := (signPairLaw_prob ρ hlo hhi).2

/-- Actual independent pair variables retain the original same-sign-copy prior. -/
def actualPairLaw (r : ℕ) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) : FinDist (Fin r → Fin 4) :=
  independentSampleLaw (fun _ => singleSignLaw ρ hlo hhi)

/-- The bundled independent law uses literally the same unique original prior weights. -/
theorem actualPairLaw_prob (r : ℕ) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) (κ : Fin r → Fin 4) :
    (actualPairLaw r ρ hlo hhi).prob κ=pairedSignLaw ρ κ := rfl

/-- The actual graph spin loss obeys the original sharp bad-prior bound, using its proved coordinate differences and actual independent sign law. -/
theorem actual_spin_tail (r d : ℕ) (hr : 0<r) (hd : 0<d)
    (b G η ρ : ℝ) (hb : 0<b) (hb1 : b≤1) (hG : 0<G) (hη : 0<η)
    (hlo : -1≤ρ) (hhi : ρ≤1) (τ : Fin d → Equiv.Perm (Fin r × Bool)) :
    (∑ κ ∈ Finset.univ.filter (fun κ : Fin r → Fin 4 =>
      η/2≤|spinEnergy b G τ κ-(actualPairLaw r ρ hlo hhi).expect (spinEnergy b G τ)|),
      (actualPairLaw r ρ hlo hhi).prob κ)≤
      2*Real.exp (-(Fintype.card (Fin r × Bool) : ℝ)*η^2/(64*(d : ℝ)^2*G^2*b^2)) := by
  let : NeZero r := ⟨ne_of_gt hr⟩
  let c : ℝ := 8*(d : ℝ)*G*b/(Fintype.card (Fin r × Bool) : ℝ)
  have hrR : 0<(r : ℝ) := by exact_mod_cast hr
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  have hc : 0<c := by dsimp [c]; positivity
  have hS : 0<∑ _i : Fin r,c^2 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_pos hrR (sq_pos_of_pos hc)
  have ht := finite_product_bounded_differences_tail (Fin 4) r
    (fun _ => singleSignLaw ρ hlo hhi) (spinEnergy b G τ) (fun _ => c) (η/2)
    (fun _ => hc.le) hS (by positivity) (fun i κ ξ hκ =>
      spinEnergy_coordinate_change b G hb.le hb1 hG.le τ i κ ξ hκ)
  have he : -2*(η/2)^2/(∑ _i : Fin r,c^2)=
      -(Fintype.card (Fin r × Bool) : ℝ)*η^2/(64*(d : ℝ)^2*G^2*b^2) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,c,
      Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
    field_simp [ne_of_gt hrR,ne_of_gt hdR,ne_of_gt hG,ne_of_gt hb]
    ring
  simpa only [actualPairLaw,he] using ht.2

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorMoments
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation

/-- Either actual sign of one sampled pair has mean zero under the original sign law. -/
theorem side_sign_mean (ρ : ℝ) (t : Bool) :
    (∑ i : Fin 4,signPairLaw ρ i*(if t then secondSign i else firstSign i))=0 := by
  cases t
  · exact (single_sign_moments ρ).1
  · exact (single_sign_moments ρ).2.1

/-- The actual same-pair correlation is one on equal sites and rho between the two distinct signs. -/
theorem side_sign_correlation (ρ : ℝ) (t u : Bool) :
    (∑ i : Fin 4,signPairLaw ρ i*(if t then secondSign i else firstSign i)*
      (if u then secondSign i else firstSign i))=(if t=u then 1 else ρ) := by
  cases t <;> cases u <;> norm_num [Fin.sum_univ_succ,signPairLaw,firstSign,secondSign] <;> ring

/-- The original physical sign prior has exact actual correlations, rather than an input moment certificate. -/
theorem actual_sign_correlation {E : Type*} [Fintype E] [DecidableEq E] (ρ : ℝ)
    (hlo : -1≤ρ) (hhi : ρ≤1) (a z : E × Bool) :
    (∑ κ : E → Fin 4,pairedSignLaw ρ κ*siteSign κ a*siteSign κ z)=
      if a.1=z.1 then (if a.2=z.2 then 1 else ρ) else 0 := by
  rcases a with ⟨e,t⟩
  rcases z with ⟨z,u⟩
  by_cases hez : e=z
  · subst z
    have hm := single_moment ρ hlo hhi e
      (fun i => (if t then secondSign i else firstSign i)*(if u then secondSign i else firstSign i))
    have hc := side_sign_correlation ρ t u
    simp only [mul_assoc] at hc
    simpa only [siteSign,Prod.fst,Prod.snd,ite_true,mul_assoc] using hm.trans hc
  · have hm := distinct_moment ρ hlo hhi e z hez
      (fun i => if t then secondSign i else firstSign i)
      (fun i => if u then secondSign i else firstSign i)
    rw [side_sign_mean,side_sign_mean,mul_zero] at hm
    simpa only [siteSign,Prod.fst,Prod.snd,ite_eq_right hez] using hm

/-- Every actual weak Bell value is exactly its spin-correlation deficit. -/
theorem edgeBell_correlation {E : Type*} (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1)
    (κ : E → Fin 4) (a z : E × Bool) :
    edgeBell b κ a z=b*(1-b)*(1-siteSign κ a*siteSign κ z) := by
  change Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bellProbability
    (Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin.weakSpin b (siteSign κ a))
    (Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin.weakSpin b (siteSign κ z))=_
  rw [Qatlib.Papers.SCWFPrep24.Estimation.Confidence.weakSpin_bell_exact b _ _ hb0 hb1]
  linear_combination (b*(1-b)/2)*(siteSign_unit κ a)+(b*(1-b)/2)*(siteSign_unit κ z)

/-- The actual original Bell prior mean is derived from its literal shared sign probabilities and fields. -/
theorem actual_edge_mean {E : Type*} [Fintype E] [DecidableEq E]
    (b ρ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1) (a z : E × Bool) :
    (∑ κ : E → Fin 4,pairedSignLaw ρ κ*edgeBell b κ a z)=
      b*(1-b)*(1-(if a.1=z.1 then (if a.2=z.2 then 1 else ρ) else 0)) := by
  simp_rw [edgeBell_correlation b hb0 hb1]
  calc
    _ = b*(1-b)*((∑ κ : E → Fin 4,pairedSignLaw ρ κ)-
      ∑ κ : E → Fin 4,pairedSignLaw ρ κ*siteSign κ a*siteSign κ z) := by
      rw [mul_sub (b*(1-b)) (∑ κ : E → Fin 4,pairedSignLaw ρ κ)
        (∑ κ : E → Fin 4,pairedSignLaw ρ κ*siteSign κ a*siteSign κ z),
        Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro κ _
      ring
    _ = _ := by rw [(pairedSignLaw_prob ρ hlo hhi).2,actual_sign_correlation ρ hlo hhi]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

/-- The actual original pair prior on arbitrary known finite labels uses exactly the same unique original weights. -/
def finitePairLaw (E : Type) [Fintype E] [DecidableEq E] (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    FinDist (E → Fin 4) where
  prob := pairedSignLaw ρ
  nonneg := (pairedSignLaw_prob ρ hlo hhi).1
  sum_one := (pairedSignLaw_prob ρ hlo hhi).2

/-- Only the known labels of actual independent sign variables are relabeled to finite coordinate positions. -/
def signsEquiv {E : Type} [Fintype E] (e : E ≃ Fin (Fintype.card E)) :
    (Fin (Fintype.card E) → Fin 4) ≃ (E → Fin 4) where
  toFun θ := fun a => θ (e a)
  invFun κ := fun i => κ (e.symm i)
  left_inv θ := by funext i; simp
  right_inv κ := by funext a; simp

/-- Complete known relabeling preserves the actual original sign-prior mass of every individual assignment. -/
theorem signsEquiv_prob {E : Type} [Fintype E] [DecidableEq E]
    (e : E ≃ Fin (Fintype.card E)) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1)
    (θ : Fin (Fintype.card E) → Fin 4) :
    (finitePairLaw E ρ hlo hhi).prob (signsEquiv e θ)=(actualPairLaw (Fintype.card E) ρ hlo hhi).prob θ := by
  change (∏ a : E,Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation.signPairLaw ρ (θ (e a)))=
    ∏ i : Fin (Fintype.card E),Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation.signPairLaw ρ (θ i)
  exact Equiv.prod_comp e (fun i : Fin (Fintype.card E) =>
    Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation.signPairLaw ρ (θ i))

/-- The original actual spin prior has the same sharp tail on every finite complete pairing, including the explicit original periodic-grid matching labels. -/
theorem finite_pair_spin_tail {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (d : ℕ) (hd : 0<d) (b G η ρ : ℝ) (hb : 0<b) (hb1 : b≤1) (hG : 0<G) (hη : 0<η)
    (hlo : -1≤ρ) (hhi : ρ≤1) (τ : Fin d → Equiv.Perm (E × Bool)) :
    (∑ κ ∈ Finset.univ.filter (fun κ : E → Fin 4 =>
      η/2≤|spinEnergy b G τ κ-(finitePairLaw E ρ hlo hhi).expect (spinEnergy b G τ)|),
      (finitePairLaw E ρ hlo hhi).prob κ)≤
      2*Real.exp (-(Fintype.card (E × Bool) : ℝ)*η^2/(64*(d : ℝ)^2*G^2*b^2)) := by
  let r := Fintype.card E
  let e := Fintype.equivFin E
  let f : (Fin r → Fin 4) → ℝ := fun θ => spinEnergy b G τ (signsEquiv e θ)
  let c : ℝ := 8*(d : ℝ)*G*b/(Fintype.card (E × Bool) : ℝ)
  have hrR : 0<(r : ℝ) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card E)
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  have hc : 0<c := by dsimp [c]; positivity
  have hS : 0<∑ _i : Fin r,c^2 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_pos hrR (sq_pos_of_pos hc)
  have hdiff (i : Fin r) (θ ξ : Fin r → Fin 4) (hi : ∀ j,j≠i → θ j=ξ j) : |f θ-f ξ|≤c := by
    apply spinEnergy_coordinate_change b G hb.le hb1 hG.le τ (e.symm i)
    intro a ha
    apply hi (e a)
    intro hh
    apply ha
    exact e.injective (by simpa only [Equiv.apply_symm_apply] using hh)
  have hmean : (finitePairLaw E ρ hlo hhi).expect (spinEnergy b G τ)=
      (actualPairLaw r ρ hlo hhi).expect f := by
    change (∑ κ : E → Fin 4,(finitePairLaw E ρ hlo hhi).prob κ*spinEnergy b G τ κ)=_
    rw [←Equiv.sum_comp (signsEquiv e) (fun κ => (finitePairLaw E ρ hlo hhi).prob κ*spinEnergy b G τ κ)]
    simp_rw [signsEquiv_prob]
    rfl
  have hmass : (∑ κ ∈ Finset.univ.filter (fun κ : E → Fin 4 =>
      η/2≤|spinEnergy b G τ κ-(finitePairLaw E ρ hlo hhi).expect (spinEnergy b G τ)|),
      (finitePairLaw E ρ hlo hhi).prob κ)=
      (∑ θ ∈ Finset.univ.filter (fun θ : Fin r → Fin 4 =>
        η/2≤|f θ-(actualPairLaw r ρ hlo hhi).expect f|),(actualPairLaw r ρ hlo hhi).prob θ) := by
    simp only [Finset.sum_filter,hmean]
    rw [←Equiv.sum_comp (signsEquiv e) (fun κ =>
      if η/2≤|spinEnergy b G τ κ-(actualPairLaw r ρ hlo hhi).expect f|
      then (finitePairLaw E ρ hlo hhi).prob κ else 0)]
    simp_rw [signsEquiv_prob]
    rfl
  have ht := finite_product_bounded_differences_tail (Fin 4) r
    (fun _ => singleSignLaw ρ hlo hhi) f (fun _ => c) (η/2)
    (fun _ => hc.le) hS (by positivity) hdiff
  have he : -2*(η/2)^2/(∑ _i : Fin r,c^2)=
      -(Fintype.card (E × Bool) : ℝ)*η^2/(64*(d : ℝ)^2*G^2*b^2) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,c,
      Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
    change -2*(η/2)^2/((r : ℝ)*(8*(d : ℝ)*G*b/((r : ℝ)*2))^2)=_
    field_simp [ne_of_gt hrR,ne_of_gt hdR,ne_of_gt hG,ne_of_gt hb]
    ring
  rw [hmass]
  simpa only [actualPairLaw,he] using ht.2

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
