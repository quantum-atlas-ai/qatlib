/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases

/-!
# Tail bounds for complex sample means

`complexEstimate` combines empirical real and imaginary means, while `complexDeviation` centers
them at their expectations. The module proves real and complex exponential tail bounds for
bounded observations and the existence of a positive sample budget for prescribed positive error
and failure parameters. See [AharonovJonesLandau2009].

## Main statements

* `complex_estimator_tail`: For positive L, B, and ε, real and imaginary observations in [−B, B]
  give complex deviation probability at most 4 exp(−Lε²/(8B²)).
* `exists_sample_budget`: For positive B, ε, and δ, some positive natural sample count makes 4
  exp(−Lε²/(8B²)) at most δ.

## References

* [Aharonov et al., 2009][AharonovJonesLandau2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.JonesPoly05.MainResults.Estimator

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

variable {X : Type} [Fintype X] [DecidableEq X]

/-- For positive L, B, and ε, observations in [−B, B] have empirical-mean deviation probability
at most 2 exp(−Lε²/(2B²)); see [AharonovJonesLandau2009]. -/
theorem bounded_avg_tail (p : FinDist X) (f : X → ℝ) (L : ℕ) {B ε : ℝ}
    (hL : 0 < L) (hB : 0 < B) (hε : 0 < ε)
    (hf : ∀ x, f x ∈ Set.Icc (-B) B) :
    p.probEvent (fun ω : Fin L → X => ε ≤ |FinDist.avg f ω - p.expect f|) ≤
      2 * Real.exp (-(L : ℝ) * ε ^ 2 / (2 * B ^ 2)) := by
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hcpos : (0 : ℝ) < 2 * B / (L : ℝ) := by positivity
  have hsum : (∑ i : Fin L, (2 * B / (L : ℝ)) ^ 2) = 4 * B ^ 2 / (L : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  have hdiff : ∀ i (ω τ : Fin L → X), (∀ j, j ≠ i → ω j = τ j) →
      |FinDist.avg f ω - FinDist.avg f τ| ≤ 2 * B / (L : ℝ) := by
    intro i ω τ h
    rw [finite_avg_coordinate_difference L f ω τ i h, abs_div, abs_of_pos hLp]
    apply div_le_div_of_nonneg_right _ hLp.le
    apply abs_le.mpr
    constructor <;>
      linarith [(hf (ω i)).1, (hf (ω i)).2, (hf (τ i)).1, (hf (τ i)).2]
  have ht := (finite_product_bounded_differences_tail X L (fun _ => p) (FinDist.avg f)
      (fun _ => 2 * B / (L : ℝ)) ε (fun _ => hcpos.le) (by rw [hsum]; positivity)
      hε hdiff).2
  have hm : (independentSampleLaw (fun _ : Fin L => p)).expect (FinDist.avg f) =
      p.expect f := p.expect_avg f hL
  rw [hm] at ht
  change p.probEvent (fun ω : Fin L → X => ε ≤ |FinDist.avg f ω - p.expect f|) ≤ _ at ht
  refine ht.trans ?_
  rw [hsum]
  have he : -2 * ε ^ 2 / (4 * B ^ 2 / (L : ℝ)) = -(L : ℝ) * ε ^ 2 / (2 * B ^ 2) := by
    field_simp [hB.ne', hLp.ne']
    ring
  rw [he]

/-- The complex number formed from the deviations of the empirical real and imaginary means from
their expectations. -/
def complexDeviation (p : FinDist X) {L : ℕ} (re im : X → ℝ) (ω : Fin L → X) : ℂ :=
  (↑(FinDist.avg re ω - p.expect re) : ℂ) +
    (↑(FinDist.avg im ω - p.expect im) : ℂ) * Complex.I

/-- The complex estimate whose real and imaginary parts are the corresponding empirical means. -/
def complexEstimate {X : Type} {L : ℕ} (re im : X → ℝ) (ω : Fin L → X) : ℂ :=
  (↑(FinDist.avg re ω) : ℂ) + (↑(FinDist.avg im ω) : ℂ) * Complex.I

/-- Subtracting the complex expectation from `complexEstimate` gives `complexDeviation`. -/
theorem complexEstimate_sub (p : FinDist X) {L : ℕ} (re im : X → ℝ) (ω : Fin L → X) :
    complexEstimate re im ω -
        ((↑(p.expect re) : ℂ) + (↑(p.expect im) : ℂ) * Complex.I) =
      complexDeviation p re im ω := by
  unfold complexEstimate complexDeviation
  push_cast
  ring

/-- Inclusion of events implies an inequality between their probabilities under the finite
product sampling distribution. -/
theorem probEvent_mono {L : ℕ} (p : FinDist X) {E F : (Fin L → X) → Prop}
    [DecidablePred E] [DecidablePred F] (h : ∀ ω, E ω → F ω) :
    p.probEvent E ≤ p.probEvent F := by
  unfold FinDist.probEvent
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mp hω |>.1, h ω (Finset.mem_filter.mp hω).2⟩
  · intro ω _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- The probability of the union of two sampling events is at most the sum of their
probabilities. -/
theorem probEvent_or_le {L : ℕ} (p : FinDist X) (E1 E2 : (Fin L → X) → Prop)
    [DecidablePred E1] [DecidablePred E2] :
    p.probEvent (fun ω => E1 ω ∨ E2 ω) ≤ p.probEvent E1 + p.probEvent E2 := by
  classical
  simp only [FinDist.probEvent, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro ω _
  have hw : 0 ≤ p.probOf ω := Finset.prod_nonneg fun i _ => p.nonneg _
  by_cases h1 : E1 ω <;> by_cases h2 : E2 ω <;> simp [h1, h2] <;> linarith

/-- For positive L, B, and ε, real and imaginary observations in [−B, B] give complex deviation
probability at most 4 exp(−Lε²/(8B²)); see [AharonovJonesLandau2009]. -/
theorem complex_estimator_tail (p : FinDist X) (re im : X → ℝ) (L : ℕ) {B ε : ℝ}
    (hL : 0 < L) (hB : 0 < B) (hε : 0 < ε)
    (hre : ∀ x, re x ∈ Set.Icc (-B) B) (him : ∀ x, im x ∈ Set.Icc (-B) B) :
    p.probEvent (fun ω : Fin L → X => ε ≤ ‖complexDeviation p re im ω‖) ≤
      4 * Real.exp (-(L : ℝ) * ε ^ 2 / (8 * B ^ 2)) := by
  classical
  have htpos : 0 < ε / 2 := by linarith
  have hE1 := bounded_avg_tail p re L hL hB htpos hre
  have hE2 := bounded_avg_tail p im L hL hB htpos him
  have hexp : -(L : ℝ) * (ε / 2) ^ 2 / (2 * B ^ 2) =
      -(L : ℝ) * ε ^ 2 / (8 * B ^ 2) := by
    field_simp [hB.ne']
    ring
  rw [hexp] at hE1 hE2
  have hmono : p.probEvent (fun ω : Fin L → X => ε ≤ ‖complexDeviation p re im ω‖) ≤
      p.probEvent (fun ω : Fin L → X =>
        ε / 2 ≤ |FinDist.avg re ω - p.expect re| ∨
        ε / 2 ≤ |FinDist.avg im ω - p.expect im|) := by
    refine probEvent_mono p ?_
    intro ω hω
    by_contra hc
    simp only [not_or, not_le] at hc
    obtain ⟨h1, h2⟩ := hc
    have hle : ‖complexDeviation p re im ω‖ ≤
        |FinDist.avg re ω - p.expect re| + |FinDist.avg im ω - p.expect im| := by
      unfold complexDeviation
      calc ‖(↑(FinDist.avg re ω - p.expect re) : ℂ) +
              (↑(FinDist.avg im ω - p.expect im) : ℂ) * Complex.I‖
          ≤ ‖(↑(FinDist.avg re ω - p.expect re) : ℂ)‖ +
            ‖(↑(FinDist.avg im ω - p.expect im) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |FinDist.avg re ω - p.expect re| + |FinDist.avg im ω - p.expect im| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
              Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  calc p.probEvent (fun ω : Fin L → X => ε ≤ ‖complexDeviation p re im ω‖)
      ≤ p.probEvent (fun ω : Fin L → X =>
          ε / 2 ≤ |FinDist.avg re ω - p.expect re| ∨
          ε / 2 ≤ |FinDist.avg im ω - p.expect im|) := hmono
    _ ≤ p.probEvent (fun ω : Fin L → X => ε / 2 ≤ |FinDist.avg re ω - p.expect re|) +
        p.probEvent (fun ω : Fin L → X => ε / 2 ≤ |FinDist.avg im ω - p.expect im|) :=
        probEvent_or_le p _ _
    _ ≤ 2 * Real.exp (-(L : ℝ) * ε ^ 2 / (8 * B ^ 2)) +
        2 * Real.exp (-(L : ℝ) * ε ^ 2 / (8 * B ^ 2)) := add_le_add hE1 hE2
    _ = 4 * Real.exp (-(L : ℝ) * ε ^ 2 / (8 * B ^ 2)) := by ring

/-- For positive B, ε, and δ, some positive natural sample count makes 4 exp(−Lε²/(8B²)) at most
δ; see [AharonovJonesLandau2009]. -/
theorem exists_sample_budget {B ε δ : ℝ} (hB : 0 < B) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ L : ℕ, 0 < L ∧ 4 * Real.exp (-(L : ℝ) * ε ^ 2 / (8 * B ^ 2)) ≤ δ := by
  rcases le_or_gt 4 δ with h4 | h4
  · refine ⟨1, by norm_num, ?_⟩
    have h1 : Real.exp (-(1 : ℝ) * ε ^ 2 / (8 * B ^ 2)) ≤ 1 := by
      have harg : -(1 : ℝ) * ε ^ 2 / (8 * B ^ 2) ≤ 0 := by
        have hpos : (0 : ℝ) ≤ ε ^ 2 / (8 * B ^ 2) := by positivity
        have hneg : -(1 : ℝ) * ε ^ 2 / (8 * B ^ 2) =
            -(ε ^ 2 / (8 * B ^ 2)) := by ring
        rw [hneg]
        exact neg_nonpos.mpr hpos
      have h := Real.exp_le_exp.mpr harg
      rwa [Real.exp_zero] at h
    nlinarith
  · have hlogpos : 0 < Real.log (4 / δ) := by
      apply Real.log_pos
      rw [lt_div_iff₀ hδ]
      linarith
    obtain ⟨L, hL⟩ := exists_nat_gt ((8 * B ^ 2 / ε ^ 2) * Real.log (4 / δ))
    have hLpos : 0 < L := by
      have h0 : (0 : ℝ) < (8 * B ^ 2 / ε ^ 2) * Real.log (4 / δ) := by positivity
      have h1 : (0 : ℝ) < (L : ℝ) := lt_trans h0 hL
      exact_mod_cast h1
    refine ⟨L, hLpos, ?_⟩
    have hthreshold : Real.log (4 / δ) < (L : ℝ) * ε ^ 2 / (8 * B ^ 2) := by
      have hpos : 0 < ε ^ 2 / (8 * B ^ 2) := by positivity
      have hmul := mul_lt_mul_of_pos_right hL hpos
      have heq : (8 * B ^ 2 / ε ^ 2) * Real.log (4 / δ) * (ε ^ 2 / (8 * B ^ 2)) =
          Real.log (4 / δ) := by
        field_simp [hB.ne', hε.ne']
      rw [heq] at hmul
      have h2 : (L : ℝ) * (ε ^ 2 / (8 * B ^ 2)) = (L : ℝ) * ε ^ 2 / (8 * B ^ 2) := by
        ring
      linarith
    have hexp : Real.exp (-(L : ℝ) * ε ^ 2 / (8 * B ^ 2)) ≤ δ / 4 := by
      have harg : -(L : ℝ) * ε ^ 2 / (8 * B ^ 2) ≤ Real.log (δ / 4) := by
        have hlog : Real.log (δ / 4) = -Real.log (4 / δ) := by
          have hinv : δ / 4 = (4 / δ)⁻¹ := by
            field_simp [hδ.ne']
          rw [hinv, Real.log_inv]
        rw [hlog]
        have hneg : -(L : ℝ) * ε ^ 2 / (8 * B ^ 2) =
            -((L : ℝ) * ε ^ 2 / (8 * B ^ 2)) := by ring
        rw [hneg, neg_le_neg_iff]
        exact le_of_lt hthreshold
      calc Real.exp (-(L : ℝ) * ε ^ 2 / (8 * B ^ 2))
          ≤ Real.exp (Real.log (δ / 4)) := Real.exp_le_exp.mpr harg
        _ = δ / 4 := Real.exp_log (by positivity)
    linarith

end Qatlib.Papers.JonesPoly05.MainResults.Estimator
