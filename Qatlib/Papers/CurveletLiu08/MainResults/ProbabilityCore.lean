/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace Qatlib.Papers.CurveletLiu08.MainResults

variable {Ω : Type*} [MeasurableSpace Ω]

def PrScaleLe (P : Measure Ω) (a : Ω → ℝ) (η : ℝ) : ℝ :=
  P.real {ω | a ω ≤ η}

def condExpect (P : Measure Ω) (a : Ω → ℝ) (X : Ω → ℝ) (η : ℝ) : ℝ :=
  (∫ ω in {ω | a ω ≤ η}, X ω ∂P) / PrScaleLe P a η

theorem condExpect_eq_div (P : Measure Ω) (a X : Ω → ℝ) (η : ℝ) :
    condExpect P a X η = (∫ ω in {ω | a ω ≤ η}, X ω ∂P) / PrScaleLe P a η := rfl

theorem condExpect_le_of_setIntegral_le (P : Measure Ω) (a X : Ω → ℝ) (η K : ℝ)
    (hPr : 0 < PrScaleLe P a η)
    (h : ∫ ω in {ω | a ω ≤ η}, X ω ∂P ≤ K * PrScaleLe P a η) :
    condExpect P a X η ≤ K := by
  rw [condExpect, div_le_iff₀ hPr]
  exact h

theorem condExpect_const (P : Measure Ω) (a : Ω → ℝ) (η c : ℝ)
    (hPr : PrScaleLe P a η ≠ 0) :
    condExpect P a (fun _ => c) η = c := by
  rw [condExpect, setIntegral_const, PrScaleLe]
  simp only [smul_eq_mul]
  exact mul_div_cancel_left₀ c hPr

theorem condExpect_add (P : Measure Ω) (a X Y : Ω → ℝ) (η : ℝ)
    (hX : IntegrableOn X {ω | a ω ≤ η} P)
    (hY : IntegrableOn Y {ω | a ω ≤ η} P) :
    condExpect P a (fun ω => X ω + Y ω) η
      = condExpect P a X η + condExpect P a Y η := by
  rw [condExpect, condExpect, condExpect, integral_add hX hY]
  ring

theorem mul_prob_inter_le_setIntegral (P : Measure Ω) {A : Set Ω} {X : Ω → ℝ}
    (hXmeas : Measurable X) (hX0 : 0 ≤ᵐ[P.restrict A] X)
    (hXint : Integrable X (P.restrict A)) {t : ℝ} :
    t * P.real (A ∩ {ω | t ≤ X ω}) ≤ ∫ ω in A, X ω ∂P := by
  have hms : MeasurableSet {ω | t ≤ X ω} := measurableSet_le measurable_const hXmeas
  have h := mul_meas_ge_le_integral_of_nonneg (μ := P.restrict A) hX0 hXint t
  rw [measureReal_restrict_apply hms, Set.inter_comm] at h
  exact h

theorem prob_inter_ge_sub (P : Measure Ω) {A B : Set Ω}
    (hB : MeasurableSet B) (hfin : P A ≠ ∞) {x : ℝ} (h : P.real (A \ B) ≤ x) :
    P.real A - x ≤ P.real (A ∩ B) := by
  have hsum := measureReal_diff_add_inter (μ := P) (s := A) (t := B) hB hfin
  linarith

theorem prob_inter_inter_ge_sub (P : Measure Ω) {A B C : Set Ω}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hfin : P A ≠ ∞)
    {x y : ℝ} (hAB : P.real (A \ B) ≤ x) (hBC : P.real ((A ∩ B) \ C) ≤ y) :
    P.real A - x - y ≤ P.real (A ∩ B ∩ C) := by
  have h1 : P.real A - x ≤ P.real (A ∩ B) := prob_inter_ge_sub P hB hfin hAB
  have hfin' : P (A ∩ B) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have h2 : P.real (A ∩ B) - y ≤ P.real (A ∩ B ∩ C) :=
    prob_inter_ge_sub P hC hfin' hBC
  linarith

theorem prob_inter_inter_ge_of_relative (P : Measure Ω) [IsFiniteMeasure P]
    {A B C : Set Ω} (hB : MeasurableSet B) (hC : MeasurableSet C)
    {p q r : ℝ} (_hp : 0 < p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hA : p ≤ P.real A)
    (hAB : P.real (A \ B) ≤ (1 - q) * P.real A)
    (hBC : P.real ((A ∩ B) \ C) ≤ (1 - r) * P.real (A ∩ B)) :
    q * r * p ≤ P.real (A ∩ B ∩ C) := by
  have hfinA : P A ≠ ∞ := by finiteness
  have h1 : q * p ≤ P.real (A ∩ B) := by
    have hsplit := prob_inter_ge_sub P hB hfinA hAB
    nlinarith
  have hfinAB : P (A ∩ B) ≠ ∞ :=
    ne_top_of_le_ne_top hfinA (measure_mono Set.inter_subset_left)
  have h2 : r * (q * p) ≤ P.real (A ∩ B ∩ C) := by
    have hsplit := prob_inter_ge_sub P hC hfinAB hBC
    nlinarith
  calc q * r * p = r * (q * p) := by ring
    _ ≤ P.real (A ∩ B ∩ C) := h2

theorem prob_iInter_ge_sub (P : Measure Ω) [IsFiniteMeasure P]
    {ι : Type*} [Fintype ι] (good : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (good i))
    (ε : ι → ℝ) (h : ∀ i, P.real (good i)ᶜ ≤ ε i) :
    P.real Set.univ - ∑ i, ε i ≤ P.real (⋂ i, good i) := by
  have hmeasI : MeasurableSet (⋂ i, good i) := MeasurableSet.iInter hmeas
  have hcompl : (⋂ i, good i)ᶜ = ⋃ i, (good i)ᶜ := Set.compl_iInter good
  have h1 : P.real (⋂ i, good i) = P.real Set.univ - P.real (⋂ i, good i)ᶜ := by
    rw [measureReal_compl hmeasI]
    ring
  have h2 : P.real (⋂ i, good i)ᶜ ≤ ∑ i, ε i := by
    rw [hcompl]
    calc P.real (⋃ i, (good i)ᶜ) ≤ ∑ i, P.real (good i)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ i, ε i := Finset.sum_le_sum (fun i _ => h i)
  linarith

end Qatlib.Papers.CurveletLiu08.MainResults
