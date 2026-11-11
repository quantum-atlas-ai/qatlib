/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPilotProjection
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressAxisRisk

set_option backward.isDefEq.respectTransparency false

/-!
Three-coordinate training risk for rational box counters, with the literal
integer pilot count used by the reference plan. Boxes share the same records;
no independence between boxes is assumed. The final deterministic axis bound
is conditional on Bloch-length, average-defect and compiled-axis certificates.
It does not yet certify the general native grid partition or finite gate word.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.PilotVector
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open PilotProjection

/-- Complete original `finite_markov` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem finite_markov {X : Type} [Fintype X] (d : FinDist X) (f : X → ℝ)
    (hf : ∀ x,0 ≤ f x) (t : ℝ) (ht : 0<t) :
    d.expect (fun x => if t<f x then (1 : ℝ) else 0) ≤ d.expect f/t := by
  apply (le_div_iff₀ ht).mpr
  rw [mul_comm,← finite_expect_mul]
  apply finite_expect_mono
  intro x
  by_cases h : t<f x
  · simpa only [ite_eq_left h,mul_one] using h.le
  · simpa only [ite_eq_right h,mul_zero] using hf x

variable {B A : Type} [Fintype B] [Fintype A] [Nonempty B] [Nonempty A]
  [DecidableEq B] [DecidableEq A]

/-- Construction for training Law in the partial address pilot vector model. -/
def trainingLaw (m : Fin 3 → B × A → ℝ) (hm : ∀ h x,|m h x| ≤ 1) (n : ℕ) :
    FinDist (Fin 3 → Fin n → (B × A) × Bool) :=
  independentSampleLaw (fun h : Fin 3 =>
    independentSampleLaw (fun _ : Fin n => signedRecordLaw (m h) (hm h)))

/-- Construction for vector Estimate in the partial address pilot vector model. -/
def vectorEstimate {n : ℕ} (b : B) (Ω : Fin 3 → Fin n → (B × A) × Bool) : Fin 3 → ℝ :=
  fun h => (counterMeanQ b (Ω h) : ℝ)

/-- Construction for box Vector in the partial address pilot vector model. -/
def boxVector (m : Fin 3 → B × A → ℝ) (b : B) : Fin 3 → ℝ :=
  fun h => boxMean (m h) b

/-- Construction for mean Squared in the partial address pilot vector model. -/
def meanSquared {n : ℕ} (m : Fin 3 → B × A → ℝ) (b : B)
    (Ω : Fin 3 → Fin n → (B × A) × Bool) : ℝ :=
  AxisRisk.distSq (vectorEstimate b Ω) (boxVector m b)

/-- Construction for average Error in the partial address pilot vector model. -/
def averageError {n : ℕ} (m : Fin 3 → B × A → ℝ)
    (Ω : Fin 3 → Fin n → (B × A) × Bool) : ℝ :=
  (∑ b : B,meanSquared m b Ω)/(Fintype.card B : ℝ)

/-- Complete original `box_risk` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem box_risk (m : Fin 3 → B × A → ℝ) (hm : ∀ h x,|m h x| ≤ 1) (n : ℕ) (b : B) :
    (trainingLaw m hm n).expect (meanSquared m b) ≤
      6*(Fintype.card B : ℝ)/((n : ℝ)+1) := by
  unfold meanSquared AxisRisk.distSq vectorEstimate boxVector
  rw [finite_expect_sum]
  calc
    _ = ∑ h : Fin 3,(independentSampleLaw (fun _ : Fin n => signedRecordLaw (m h) (hm h))).expect
        (fun η : Fin n → (B × A) × Bool => ((counterMeanQ b η : ℝ)-boxMean (m h) b)^2) := by
      apply Finset.sum_congr rfl
      intro h _
      exact independentSampleLaw_expect_coord
        (fun j : Fin 3 => independentSampleLaw (fun _ : Fin n => signedRecordLaw (m j) (hm j))) h
        (fun η : Fin n → (B × A) × Bool => ((counterMeanQ b η : ℝ)-boxMean (m h) b)^2)
    _ ≤ ∑ _ : Fin 3,2*(Fintype.card B : ℝ)/((n : ℝ)+1) := by
      apply Finset.sum_le_sum
      intro h _
      exact counter_mean_risk (m h) (hm h) b n
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      norm_num
      ring

omit [Nonempty B] [Nonempty A] [DecidableEq A] in
/-- Complete original `average_error_nonneg` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem average_error_nonneg {n : ℕ} (m : Fin 3 → B × A → ℝ)
    (Ω : Fin 3 → Fin n → (B × A) × Bool) : 0 ≤ averageError m Ω := by
  exact div_nonneg (Finset.sum_nonneg fun b _ => AxisRisk.dist_sq_nonneg _ _)
    (Nat.cast_nonneg _)

/-- Complete original `average_risk` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem average_risk (m : Fin 3 → B × A → ℝ) (hm : ∀ h x,|m h x| ≤ 1) (n : ℕ) :
    (trainingLaw m hm n).expect (averageError m) ≤
      6*(Fintype.card B : ℝ)/((n : ℝ)+1) := by
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (trainingLaw m hm n).expect (averageError m)=
      (∑ b : B,(trainingLaw m hm n).expect (meanSquared m b))/(Fintype.card B : ℝ) := by
    unfold FinDist.expect averageError
    simp_rw [← mul_div_assoc,Finset.mul_sum]
    rw [← Finset.sum_div,Finset.sum_comm]
  rw [he]
  calc
    _ ≤ (∑ _ : B,6*(Fintype.card B : ℝ)/((n : ℝ)+1))/(Fintype.card B : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _ => box_risk m hm n b) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp

/-- Construction for pilot Count Q in the partial address pilot vector model. -/
def pilotCountQ (boxes : ℕ) (α τ : ℚ) : ℕ := ceilNatQ (96*(boxes : ℚ)/(α*τ))

/-- Complete original `pilot_count_budget` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem pilot_count_budget (boxes : ℕ) (α τ : ℚ) (hα : 0<α) (hτ : 0<τ) :
    96*(boxes : ℝ) ≤ (pilotCountQ boxes α τ : ℝ)*((α : ℝ)*(τ : ℝ)) := by
  let q : ℚ :=96*(boxes : ℚ)/(α*τ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hc := (ceil_nat_bounds q hq).1
  have hr : 96*(boxes : ℝ)/((α : ℝ)*(τ : ℝ)) ≤ (pilotCountQ boxes α τ : ℝ) := by
    simpa only [q,pilotCountQ,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using hc
  have hαR : (0 : ℝ)<α := Rat.cast_pos.mpr hα
  have hτR : (0 : ℝ)<τ := Rat.cast_pos.mpr hτ
  exact (div_le_iff₀ (mul_pos hαR hτR)).mp hr

/-- Construction for bad Probability in the partial address pilot vector model. -/
def badProbability (m : Fin 3 → B × A → ℝ) (hm : ∀ h x,|m h x| ≤ 1)
    (α τ : ℚ) : ℝ :=
  (trainingLaw m hm (pilotCountQ (Fintype.card B) α τ)).expect
    (fun Ω => if (τ : ℝ)/16<averageError m Ω then 1 else 0)

/-- Complete original `pilot_error_tail` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem pilot_error_tail (m : Fin 3 → B × A → ℝ) (hm : ∀ h x,|m h x| ≤ 1)
    (α τ : ℚ) (hα : 0<α) (hτ : 0<τ) : badProbability m hm α τ ≤ (α : ℝ) := by
  let n := pilotCountQ (Fintype.card B) α τ
  have hαR : (0 : ℝ)<α := Rat.cast_pos.mpr hα
  have hτR : (0 : ℝ)<τ := Rat.cast_pos.mpr hτ
  have hb := pilot_count_budget (Fintype.card B) α τ hα hτ
  have ht : (0 : ℝ)<(τ : ℝ)/16 := by positivity
  have hn : (0 : ℝ)<(n : ℝ)+1 := by positivity
  calc
    _ ≤ (trainingLaw m hm n).expect (averageError m)/((τ : ℝ)/16) :=
      finite_markov _ _ (average_error_nonneg m) _ ht
    _ ≤ (6*(Fintype.card B : ℝ)/((n : ℝ)+1))/((τ : ℝ)/16) :=
      div_le_div_of_nonneg_right (average_risk m hm n) ht.le
    _ ≤ (α : ℝ) := by
      rw [div_le_iff₀ ht,div_le_iff₀ hn]
      change 96*(Fintype.card B : ℝ) ≤ (n : ℝ)*((α : ℝ)*(τ : ℝ)) at hb
      nlinarith [mul_nonneg hαR.le hτR.le]

/-- Construction for average Defect in the partial address pilot vector model. -/
def averageDefect (m : Fin 3 → B × A → ℝ) : ℝ :=
  (∑ b : B,(1-AxisRisk.length (boxVector m b))/2)/(Fintype.card B : ℝ)

/-- Construction for average Minority in the partial address pilot vector model. -/
def averageMinority (m : Fin 3 → B × A → ℝ) (axes : B → Fin 3 → ℝ) : ℝ :=
  (∑ b : B,(1-AxisRisk.dot (boxVector m b) (axes b))/2)/(Fintype.card B : ℝ)

omit [Nonempty A] [DecidableEq A] in
/-- Complete original `average_compiled_risk` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem average_compiled_risk {n : ℕ} (m : Fin 3 → B × A → ℝ)
    (Ω : Fin 3 → Fin n → (B × A) × Bool) (axes : B → Fin 3 → ℝ) (τ : ℝ)
    (hr : ∀ b,AxisRisk.length (boxVector m b) ≤ 1)
    (hu : ∀ b,AxisRisk.dot (axes b) (axes b)=1)
    (hc : ∀ b,1-AxisRisk.dot (AxisRisk.axis (vectorEstimate b Ω)) (axes b) ≤ τ/32) :
    averageMinority m axes ≤ 8*averageDefect m+4*averageError m Ω+τ/32 := by
  have hp : (0 : ℝ)<Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ∑ b : B,(8*((1-AxisRisk.length (boxVector m b))/2)+
        4*AxisRisk.distSq (vectorEstimate b Ω) (boxVector m b)+τ/32) := by
      apply Finset.sum_le_sum
      intro b _
      exact AxisRisk.compiled_axis_risk _ _ _ _ (hr b) (hu b) (hc b)
    _ = _ := by
      simp only [averageDefect,averageError,meanSquared,Finset.sum_add_distrib,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
      field_simp

omit [Nonempty A] [DecidableEq A] in
/-- Complete original `good_average_minority` guarantee for `PartialAddressPilotVector`; all source hypotheses and output obligations are retained. -/
theorem good_average_minority {n : ℕ} (m : Fin 3 → B × A → ℝ)
    (Ω : Fin 3 → Fin n → (B × A) × Bool) (axes : B → Fin 3 → ℝ) (τ : ℝ)
    (hr : ∀ b,AxisRisk.length (boxVector m b) ≤ 1)
    (hu : ∀ b,AxisRisk.dot (axes b) (axes b)=1)
    (hc : ∀ b,1-AxisRisk.dot (AxisRisk.axis (vectorEstimate b Ω)) (axes b) ≤ τ/32)
    (hq : averageDefect m ≤ τ/32) (he : averageError m Ω ≤ τ/16) :
    averageMinority m axes ≤ 17*τ/32 := by
  have h := average_compiled_risk m Ω axes τ hr hu hc
  linarith

#print axioms finite_markov
#print axioms box_risk
#print axioms average_error_nonneg
#print axioms average_risk
#print axioms pilot_count_budget
#print axioms pilot_error_tail
#print axioms average_compiled_risk
#print axioms good_average_minority
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.PilotVector
