/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Confidence Weak Spin

The actual two-amplitude weak spin with a real sign.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation
namespace Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

/-- The actual two-amplitude weak spin with a real sign. -/
def weakSpin (b σ : ℝ) : QState Bool :=
  fun q => if q then ((σ*Real.sqrt b : ℝ) : ℂ) else ((Real.sqrt (1-b) : ℝ) : ℂ)

/-- Every actual weak spin with unit sign has norm one. -/
theorem weakSpin_normalized (b σ : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hσ : σ^2=1) :
    Normalized (weakSpin b σ) := by
  simp only [Normalized,Fintype.sum_bool,weakSpin,Bool.false_eq_true,ite_false,ite_true,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,
    Real.sq_sqrt hb0,Real.sq_sqrt (by linarith : 0 ≤ 1-b),hσ]
  ring

/-- All copies retain the same sign rather than independently resampling it. -/
def weakCopies (b σ : ℝ) (r : ℕ) : QState (Fin r → Bool) :=
  fun x => ∏ j,weakSpin b σ (x j)

/-- Repeated weak-spin vectors are normalized even when the copy count is zero. -/
theorem weakCopies_normalized (b σ : ℝ) (r : ℕ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hσ : σ^2=1) : Normalized (weakCopies b σ r) := by
  have h : (∑ q : Bool,‖weakSpin b σ q‖^2)=1 := weakSpin_normalized b σ hb0 hb1 hσ
  change (∑ x : Fin r → Bool,‖∏ j : Fin r,weakSpin b σ (x j)‖^2)=1
  simp only [norm_prod,←Finset.prod_pow]
  calc _ = ∏ _j : Fin r,∑ q : Bool,‖weakSpin b σ q‖^2 :=
        (Fintype.prod_sum (fun (_j : Fin r) (q : Bool) => ‖weakSpin b σ q‖^2)).symm
       _ = 1 := by simp only [h,Finset.prod_const_one]

/-- Opposite real signs have the exact original weak-spin overlap. -/
theorem weakSpin_opposite_inner (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Qatlib.Foundations.PureStateMath.Inner (weakSpin b 1) (weakSpin b (-1))=
      ((1-2*b : ℝ) : ℂ) := by
  rw [inner_apply]
  simp [weakSpin,←Complex.ofReal_mul,
    Real.mul_self_sqrt hb0,Real.mul_self_sqrt (by linarith : 0 ≤ 1-b)]
  push_cast
  ring

/-- The original same-sign r-copy vectors have exactly the r-th power overlap, including r=0. -/
theorem weakCopies_opposite_inner (b : ℝ) (r : ℕ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Qatlib.Foundations.PureStateMath.Inner (weakCopies b 1 r) (weakCopies b (-1) r)=
      ((1-2*b : ℝ) : ℂ)^r := by
  rw [inner_apply]
  simp only [weakCopies,map_prod,←Finset.prod_mul_distrib]
  have h : (∑ q : Bool,(starRingEnd ℂ) (weakSpin b 1 q)*weakSpin b (-1) q)=
      ((1-2*b : ℝ) : ℂ) := by
    simpa only [inner_apply] using weakSpin_opposite_inner b hb0 hb1
  calc _ = ∏ _j : Fin r,∑ q : Bool,(starRingEnd ℂ) (weakSpin b 1 q)*weakSpin b (-1) q :=
        (Fintype.prod_sum (fun (_j : Fin r) (q : Bool) =>
          (starRingEnd ℂ) (weakSpin b 1 q)*weakSpin b (-1) q)).symm
       _ = _ := by simp only [h,Fin.prod_const]


/-- The literal unnormalized odd component remains defined even at zero copies or zero excitation. -/
def oddCopies (b : ℝ) (r : ℕ) : QState (Fin r → Bool) :=
  fun x => (weakCopies b 1 r x-weakCopies b (-1) r x)/2

/-- The actual odd component has the original closed-form mass. -/
theorem oddCopies_mass (b : ℝ) (r : ℕ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∑ x,‖oddCopies b r x‖^2)=(1-(1-2*b)^r)/2 := by
  have hi := Qatlib.Concepts.MixedFidelity.FidelityMetric.PairOverlap.real_inner_eq_one_sub_distance
    (weakCopies b 1 r) (weakCopies b (-1) r)
    (weakCopies_normalized b 1 r hb0 hb1 (by norm_num))
    (weakCopies_normalized b (-1) r hb0 hb1 (by norm_num))
  rw [weakCopies_opposite_inner b r hb0 hb1] at hi
  simp only [←Complex.ofReal_pow,Complex.ofReal_re] at hi
  have hd : (∑ x,‖oddCopies b r x‖^2)=
      Qatlib.Concepts.MixedFidelity.FidelityMetric.PairOverlap.squareDistance
        (weakCopies b 1 r) (weakCopies b (-1) r)/4 := by
    norm_num [oddCopies,div_pow,←Finset.sum_div,
      Qatlib.Concepts.MixedFidelity.FidelityMetric.PairOverlap.squareDistance]
  rw [hd]
  linarith

/-- The original closed-form odd mass is bounded by the actual copy count times the excitation rate. -/
theorem oddMass_le_count (b : ℝ) (r : ℕ) (hb0 : 0 ≤ b) (hbhalf : b ≤ 1/2) :
    (1-(1-2*b)^r)/2 ≤ (r : ℝ)*b := by
  have hx0 : 0 ≤ 1-2*b := by linarith
  have hx1 : 1-2*b ≤ 1 := by linarith
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hp : (1-2*b)^r ≤ 1 := pow_le_one₀ hx0 hx1
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hp)]

end Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

namespace Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification

/-- The original two count-indexed spin registers, retaining every spin basis amplitude. -/
abbrev PairBasis (r s : ℕ) := (Fin r → Bool) × (Fin s → Bool)

/-- A basis equivalence only reindexes the physical tensor register. -/
def pairBasisEquiv (r s : ℕ) := Fintype.equivFin (PairBasis r s)

/-- The actual tensor amplitude, expressed on the existing finite matrix basis. -/
def tensorVector (r s : ℕ) (a : QState (Fin r → Bool)) (b : QState (Fin s → Bool)) :
    QState (Fin (Fintype.card (PairBasis r s))) :=
  fun i => a ((pairBasisEquiv r s).symm i).1*b ((pairBasisEquiv r s).symm i).2

/-- Reindexing preserves the literal tensor-product squared norm, with zero counts included. -/
theorem tensorVector_mass (r s : ℕ) (a : QState (Fin r → Bool)) (b : QState (Fin s → Bool)) :
    (∑ i,‖tensorVector r s a b i‖^2)=
      (∑ x,‖a x‖^2)*(∑ y,‖b y‖^2) := by
  calc _ = ∑ x : PairBasis r s,‖a x.1*b x.2‖^2 :=
        (pairBasisEquiv r s).symm.sum_comp (fun x => ‖a x.1*b x.2‖^2)
       _ = _ := by
         simp only [Fintype.sum_prod_type,norm_mul,mul_pow,Finset.mul_sum,Finset.sum_mul]
         rw [Finset.sum_comm]

/-- Actual normalized spin copies tensor to a normalized physical source vector. -/
theorem tensorVector_normalized (r s : ℕ) (a : QState (Fin r → Bool)) (b : QState (Fin s → Bool))
    (ha : Normalized a) (hb : Normalized b) : Normalized (tensorVector r s a b) := by
  change (∑ i,‖tensorVector r s a b i‖^2)=1
  rw [tensorVector_mass,ha,hb]
  norm_num

/-- The actual weak-spin pair vector keeps both signs fixed over their complete copy cohorts. -/
def physicalPair (b : ℝ) (r s : ℕ) (σ τ : ℝ) :=
  tensorVector r s (weakCopies b σ r) (weakCopies b τ s)

/-- No normalization certificate is needed for the original four physical weak-pair vectors. -/
theorem physicalPair_normalized (b : ℝ) (r s : ℕ) (σ τ : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hσ : σ^2=1) (hτ : τ^2=1) :
    Normalized (physicalPair b r s σ τ) :=
  tensorVector_normalized r s _ _ (weakCopies_normalized b σ r hb0 hb1 hσ)
    (weakCopies_normalized b τ s hb0 hb1 hτ)

end Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

namespace Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification

/-- The four original normalized weak-pair vectors, with no hidden classical sign register. -/
def physicalPairStates (b : ℝ) (r s : ℕ) :=
  ![physicalPair b r s (-1) (-1),physicalPair b r s 1 (-1),
    physicalPair b r s (-1) 1,physicalPair b r s 1 1]

/-- The actual uniform even component is defined without dividing by its possibly zero mass. -/
def evenCopies (b : ℝ) (r : ℕ) : QState (Fin r → Bool) :=
  fun x => (weakCopies b 1 r x+weakCopies b (-1) r x)/2

/-- The second sign is fixed across its complete supplied cohort. -/
def cohortSign (τ : Fin 2) : ℝ := if τ.val=0 then -1 else 1

/-- The first-cohort even component retains the full second unknown spin cohort. -/
def pairEven (b : ℝ) (r s : ℕ) (τ : Fin 2) :=
  tensorVector r s (evenCopies b r) (weakCopies b (cohortSign τ) s)

/-- The first-cohort odd component retains the full second unknown spin cohort. -/
def pairOdd (b : ℝ) (r s : ℕ) (τ : Fin 2) :=
  tensorVector r s (oddCopies b r) (weakCopies b (cohortSign τ) s)

/-- The generic purification source is exactly the four physical weak-pair vectors. -/
theorem physical_source_eq (b : ℝ) (r s : ℕ) :
    sourceStates (pairEven b r s) (pairOdd b r s)=physicalPairStates b r s := by
  funext i k
  fin_cases i <;>
    simp [sourceStates,physicalPairStates,pairEven,pairOdd,evenCopies,oddCopies,
      physicalPair,tensorVector,cohortSign] <;> ring

/-- The source norm is derived from the actual supplied tensor vectors. -/
theorem physical_source_normalized (b : ℝ) (r s : ℕ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ i,Normalized (sourceStates (pairEven b r s) (pairOdd b r s) i) := by
  intro i
  rw [physical_source_eq]
  fin_cases i
  · change Normalized (physicalPair b r s (-1) (-1))
    exact physicalPair_normalized b r s (-1) (-1) hb0 hb1 (by norm_num) (by norm_num)
  · change Normalized (physicalPair b r s 1 (-1))
    exact physicalPair_normalized b r s 1 (-1) hb0 hb1 (by norm_num) (by norm_num)
  · change Normalized (physicalPair b r s (-1) 1)
    exact physicalPair_normalized b r s (-1) 1 hb0 hb1 (by norm_num) (by norm_num)
  · change Normalized (physicalPair b r s 1 1)
    exact physicalPair_normalized b r s 1 1 hb0 hb1 (by norm_num) (by norm_num)

/-- The literal odd tensor component has exactly the original first-cohort odd mass. -/
theorem pairOdd_mass (b : ℝ) (r s : ℕ) (τ : Fin 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∑ i,‖pairOdd b r s τ i‖^2)=(1-(1-2*b)^r)/2 := by
  have hτ : (cohortSign τ)^2=1 := by unfold cohortSign; split_ifs <;> norm_num
  have hn : (∑ x,‖weakCopies b (cohortSign τ) s x‖^2)=1 :=
    weakCopies_normalized b (cohortSign τ) s hb0 hb1 hτ
  rw [pairOdd,tensorVector_mass,oddCopies_mass b r hb0 hb1,hn,mul_one]

/-- This is the literal original four-sign conditional physical density. -/
def physicalPairMixture (b : ℝ) (r s : ℕ) (ρ : ℝ) :=
  ∑ i : Fin 4,(signPairLaw ρ i : ℂ) • outerProduct (physicalPairStates b r s i)

/-- The actual conditional physical pair has a first-cohort copy-sensitive information bound. -/
theorem physical_pair_first_count (b : ℝ) (r s : ℕ) (a ρ ξ : ℝ)
    (hb0 : 0 ≤ b) (hbhalf : b ≤ 1/2) (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a) :
    1-Froot (physicalPairMixture b r s ρ) (physicalPairMixture b r s ξ) ≤
      (ρ-ξ)^2/(4*(1-a^2))*(2*(r : ℝ)*b) := by
  have hb1 : b ≤ 1 := by linarith
  have h := mixture_fidelity_quadratic (pairEven b r s) (pairOdd b r s)
    (physical_source_normalized b r s hb0 hb1) a ρ ξ ha hρ hξ
  rw [physical_source_eq] at h
  change 1-Froot (physicalPairMixture b r s ρ) (physicalPairMixture b r s ξ) ≤ _ at h
  have hm : (∑ i,(‖pairOdd b r s 0 i‖^2+‖pairOdd b r s 1 i‖^2))=1-(1-2*b)^r := by
    rw [Finset.sum_add_distrib,pairOdd_mass b r s 0 hb0 hb1,pairOdd_mass b r s 1 hb0 hb1]
    ring
  rw [hm] at h
  have ha0 : 0 ≤ a := (abs_nonneg ρ).trans hρ
  have hg : 0<1-a^2 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
  have hc : 0 ≤ (ρ-ξ)^2/(4*(1-a^2)) := div_nonneg (sq_nonneg _) (by positivity)
  have ho : 1-(1-2*b)^r ≤ 2*(r : ℝ)*b := by nlinarith [oddMass_le_count b r hb0 hbhalf]
  exact h.trans (mul_le_mul_of_nonneg_left ho hc)

end Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

namespace Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification

/-- The second-cohort even component keeps the full first physical cohort in its original register order. -/
def pairEvenSecond (b : ℝ) (r s : ℕ) (σ : Fin 2) :=
  tensorVector r s (weakCopies b (cohortSign σ) r) (evenCopies b s)

/-- The second-cohort odd component keeps the same physical register order. -/
def pairOddSecond (b : ℝ) (r s : ℕ) (σ : Fin 2) :=
  tensorVector r s (weakCopies b (cohortSign σ) r) (oddCopies b s)

/-- The second decomposition only permutes the two equal-weight middle sign labels. -/
theorem physical_source_second_eq (b : ℝ) (r s : ℕ) :
    sourceStates (pairEvenSecond b r s) (pairOddSecond b r s)=
      ![physicalPair b r s (-1) (-1),physicalPair b r s (-1) 1,
        physicalPair b r s 1 (-1),physicalPair b r s 1 1] := by
  funext i k
  fin_cases i <;>
    simp [sourceStates,pairEvenSecond,pairOddSecond,evenCopies,oddCopies,
      physicalPair,tensorVector,cohortSign] <;> ring

/-- The second decomposition is normalized from the same actual supplied vectors. -/
theorem physical_source_second_normalized (b : ℝ) (r s : ℕ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ i,Normalized (sourceStates (pairEvenSecond b r s) (pairOddSecond b r s) i) := by
  intro i
  rw [physical_source_second_eq]
  fin_cases i
  · change Normalized (physicalPair b r s (-1) (-1))
    exact physicalPair_normalized b r s (-1) (-1) hb0 hb1 (by norm_num) (by norm_num)
  · change Normalized (physicalPair b r s (-1) 1)
    exact physicalPair_normalized b r s (-1) 1 hb0 hb1 (by norm_num) (by norm_num)
  · change Normalized (physicalPair b r s 1 (-1))
    exact physicalPair_normalized b r s 1 (-1) hb0 hb1 (by norm_num) (by norm_num)
  · change Normalized (physicalPair b r s 1 1)
    exact physicalPair_normalized b r s 1 1 hb0 hb1 (by norm_num) (by norm_num)

/-- The actual density is unchanged when the two equal-weight sign labels are exchanged. -/
theorem physical_source_second_mixture (b : ℝ) (r s : ℕ) (ρ : ℝ) :
    (∑ i : Fin 4,(signPairLaw ρ i : ℂ) •
      outerProduct (sourceStates (pairEvenSecond b r s) (pairOddSecond b r s) i))=
        physicalPairMixture b r s ρ := by
  rw [physical_source_second_eq]
  norm_num [physicalPairMixture,physicalPairStates,signPairLaw,Fin.sum_univ_succ]
  abel

/-- The literal second odd tensor component has the original second-cohort odd mass. -/
theorem pairOddSecond_mass (b : ℝ) (r s : ℕ) (σ : Fin 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∑ i,‖pairOddSecond b r s σ i‖^2)=(1-(1-2*b)^s)/2 := by
  have hσ : (cohortSign σ)^2=1 := by unfold cohortSign; split_ifs <;> norm_num
  have hn : (∑ x,‖weakCopies b (cohortSign σ) r x‖^2)=1 :=
    weakCopies_normalized b (cohortSign σ) r hb0 hb1 hσ
  rw [pairOddSecond,tensorVector_mass,oddCopies_mass b s hb0 hb1,hn,one_mul]

/-- The same actual physical density also has the second-cohort copy-sensitive bound. -/
theorem physical_pair_second_count (b : ℝ) (r s : ℕ) (a ρ ξ : ℝ)
    (hb0 : 0 ≤ b) (hbhalf : b ≤ 1/2) (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a) :
    1-Froot (physicalPairMixture b r s ρ) (physicalPairMixture b r s ξ) ≤
      (ρ-ξ)^2/(4*(1-a^2))*(2*(s : ℝ)*b) := by
  have hb1 : b ≤ 1 := by linarith
  have h := mixture_fidelity_quadratic (pairEvenSecond b r s) (pairOddSecond b r s)
    (physical_source_second_normalized b r s hb0 hb1) a ρ ξ ha hρ hξ
  rw [physical_source_second_mixture,physical_source_second_mixture] at h
  have hm : (∑ i,(‖pairOddSecond b r s 0 i‖^2+‖pairOddSecond b r s 1 i‖^2))=1-(1-2*b)^s := by
    rw [Finset.sum_add_distrib,pairOddSecond_mass b r s 0 hb0 hb1,pairOddSecond_mass b r s 1 hb0 hb1]
    ring
  rw [hm] at h
  have ha0 : 0 ≤ a := (abs_nonneg ρ).trans hρ
  have hg : 0<1-a^2 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
  have hc : 0 ≤ (ρ-ξ)^2/(4*(1-a^2)) := div_nonneg (sq_nonneg _) (by positivity)
  have ho : 1-(1-2*b)^s ≤ 2*(s : ℝ)*b := by nlinarith [oddMass_le_count b s hb0 hbhalf]
  exact h.trans (mul_le_mul_of_nonneg_left ho hc)

/-- The original conditional physical weak pair has a bound in the smaller actual copy count, including zero counts. -/
theorem physical_pair_min_count (b : ℝ) (r s : ℕ) (a ρ ξ : ℝ)
    (hb0 : 0 ≤ b) (hbhalf : b ≤ 1/2) (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a) :
    1-Froot (physicalPairMixture b r s ρ) (physicalPairMixture b r s ξ) ≤
      (ρ-ξ)^2/(4*(1-a^2))*(2*(min r s : ℕ)*b) := by
  rcases le_total r s with hrs | hsr
  · rw [Nat.min_eq_left hrs]
    exact physical_pair_first_count b r s a ρ ξ hb0 hbhalf ha hρ hξ
  · rw [Nat.min_eq_right hsr]
    exact physical_pair_second_count b r s a ρ ξ hb0 hbhalf ha hρ hξ

/-- The source's exact original conditional-pair constant follows without a free fidelity or state-normalization certificate. -/
theorem physical_pair_original_information (b : ℝ) (r s : ℕ) (a ρ ξ : ℝ)
    (hb0 : 0 ≤ b) (hbhalf : b ≤ 1/2) (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a) :
    1-Froot (physicalPairMixture b r s ρ) (physicalPairMixture b r s ξ) ≤
      (3/(2*(1-a^2)))*b*(min r s : ℕ)*(ρ-ξ)^2 := by
  have h := physical_pair_min_count b r s a ρ ξ hb0 hbhalf ha hρ hξ
  have ha0 : 0 ≤ a := (abs_nonneg ρ).trans hρ
  have hg : 0<1-a^2 := by nlinarith [mul_pos (by linarith : 0<1-a) (by linarith : 0<1+a)]
  have he : (ρ-ξ)^2/(4*(1-a^2))*(2*(min r s : ℕ)*b)=
      (1/(2*(1-a^2)))*b*(min r s : ℕ)*(ρ-ξ)^2 := by
    field_simp [ne_of_gt hg]
    ring
  rw [he] at h
  have hp : 0 ≤ (1/(2*(1-a^2)))*b*(min r s : ℕ)*(ρ-ξ)^2 := by positivity
  have he3 : (3/(2*(1-a^2)))*b*(min r s : ℕ)*(ρ-ξ)^2=
      3*((1/(2*(1-a^2)))*b*(min r s : ℕ)*(ρ-ξ)^2) := by ring
  rw [he3]
  linarith

end Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

namespace Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.PairPurification

/-- The literal original pair mixture is a density operator for every legal correlation. -/
theorem physicalPairMixture_density (b : ℝ) (r s : ℕ) (ρ : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hlo : -1 ≤ ρ) (hhi : ρ ≤ 1) :
    IsDensityOperator (physicalPairMixture b r s ρ) := by
  unfold physicalPairMixture
  rw [←physical_source_eq]
  exact mixture_density (pairEven b r s) (pairOdd b r s)
    (physical_source_normalized b r s hb0 hb1) ρ hlo hhi

/-- The actual weak-pair mixtures retain the uniform positive fidelity floor needed for logarithmic confidence bounds. -/
theorem physical_pair_fidelity_floor (b : ℝ) (r s : ℕ) (a ρ ξ : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a) :
    1-a ≤ Froot (physicalPairMixture b r s ρ) (physicalPairMixture b r s ξ) := by
  have hn : ∀ i,Normalized (physicalPairStates b r s i) := by
    rw [←physical_source_eq]
    exact physical_source_normalized b r s hb0 hb1
  unfold physicalPairMixture
  exact prepared_signPair_fidelity_lower (physicalPairStates b r s) hn a ρ ξ ha hρ hξ

/-- A zero supplied cohort contains no pair-correlation information in the actual physical quantum state. -/
theorem physical_pair_zero_count (b : ℝ) (r s : ℕ) (a ρ ξ : ℝ)
    (hb0 : 0 ≤ b) (hbhalf : b ≤ 1/2) (ha : a<1) (hρ : |ρ| ≤ a) (hξ : |ξ| ≤ a)
    (hzero : r=0 ∨ s=0) :
    Froot (physicalPairMixture b r s ρ) (physicalPairMixture b r s ξ)=1 := by
  have hb1 : b ≤ 1 := by linarith
  have hr := abs_le.mp hρ
  have hx := abs_le.mp hξ
  have hdρ := physicalPairMixture_density b r s ρ hb0 hb1 (by linarith) (by linarith)
  have hdξ := physicalPairMixture_density b r s ξ hb0 hb1 (by linarith) (by linarith)
  have hup := (g1 _ _ _ hdρ hdξ).2.1.2.1
  have hlow := physical_pair_original_information b r s a ρ ξ hb0 hbhalf ha hρ hξ
  have hm : min r s=0 := by rcases hzero with rfl | rfl <;> simp
  rw [hm] at hlow
  norm_num at hlow
  linarith

end Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
