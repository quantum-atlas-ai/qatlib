/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchArith.TransposeAccess.FinDist

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt

open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces MeasureTheory
open scoped BigOperators Classical
set_option warningAsError false

variable {R Y : Type} [Fintype R] [DecidableEq R] [Fintype Y] [DecidableEq Y]

def observe (r : FinDist R) (read : R → Y) : FinDist Y :=
  ofPMF ((toPMF r).map read)

omit [DecidableEq R] [DecidableEq Y] in

theorem observe_toPMF (r : FinDist R) (read : R → Y) :
    toPMF (observe r read) = (toPMF r).map read := toPMF_ofPMF _

theorem observe_mass (r : FinDist R) (read : R → Y) (y : Y) :
    (observe r read).prob y = ∑ z, if read z = y then r.prob z else 0 := by
  obtain ⟨q, μ, ν, hq, hμ, hν, hmap, _⟩ :=
      (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pushforward_pmf r) read
  have he : (toPMF r).map read = toPMF q := by
    rw [toPMF_unique r μ hμ, hmap, toPMF_unique q ν hν]
  rw [observe, he, ofPMF_toPMF_prob, hq]

theorem observe_expect (r : FinDist R) (read : R → Y) (f : Y → ℝ) :
    (observe r read).expect f = r.expect (fun z => f (read z)) :=
  (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.expect_eq_of_pushforward r) (observe r read) read f (observe_mass r read)

theorem observe_variance (r : FinDist R) (read : R → Y) (f : Y → ℝ) :
    (observe r read).variance f = r.variance (fun z => f (read z)) :=
  (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.variance_eq_of_pushforward r) (observe r read) read f (observe_mass r read)

omit [DecidableEq R] in

private theorem eventMass_expect (r : FinDist R) (E : R → Prop) [DecidablePred E] :
    eventMass r E = r.expect (fun z => if E z then 1 else 0) := by
  simp [eventMass, FinDist.expect, Finset.sum_filter]

theorem observe_event (r : FinDist R) (read : R → Y) (E : Y → Prop) [DecidablePred E] :
    eventMass (observe r read) E = eventMass r (fun z => E (read z)) := by
  rw [eventMass_expect, observe_expect, eventMass_expect]

def statisticLaw (r : FinDist R) (stat : R → ℝ) : PMF ℝ := (toPMF r).map stat

theorem statistic_event (r : FinDist R) (stat : R → ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    letI : MeasurableSpace R := ⊤
    (statisticLaw r stat).toMeasure E = ENNReal.ofReal (eventMass r (fun z => stat z ∈ E)) := by
  letI : MeasurableSpace R := ⊤
  classical
  rw [statisticLaw, PMF.toMeasure_map_apply _ _ _ (measurable_of_countable stat) hE]
  exact eventMass_toMeasure r _

theorem statistic_integral (r : FinDist R) (stat : R → ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) :
    letI : MeasurableSpace R := ⊤
    ∫ x, f x ∂(statisticLaw r stat).toMeasure = r.expect (fun z => f (stat z)) := by
  letI : MeasurableSpace R := ⊤
  rw [statisticLaw, ← PMF.toMeasure_map stat (toPMF r) (measurable_of_countable stat),
    integral_map (measurable_of_countable stat).aemeasurable hf.aestronglyMeasurable]
  exact integral_eq_expect r _

theorem statistic_moment (r : FinDist R) (stat : R → ℝ) (k : ℕ) :
    letI : MeasurableSpace R := ⊤
    ∫ x, (x - r.expect stat) ^ k ∂(statisticLaw r stat).toMeasure =
      r.expect (fun z => (stat z - r.expect stat) ^ k) := by
  apply statistic_integral
  fun_prop

omit [DecidableEq R] [DecidableEq Y] in

theorem statistic_observe (r : FinDist R) (read : R → Y) (f : Y → ℝ) :
    statisticLaw (observe r read) f = statisticLaw r (fun z => f (read z)) := by
  simp only [statisticLaw, observe_toPMF, PMF.map_comp, Function.comp_def]

theorem statistic_chebyshev (r : FinDist R) (stat : R → ℝ) (eps : ℝ) (heps : 0 < eps) :
    (statisticLaw r stat).toMeasure {x | eps ≤ |x - r.expect stat|} ≤
      ENNReal.ofReal (r.variance stat / eps ^ 2) := by
  rw [statistic_event r stat _ (by measurability)]
  exact ENNReal.ofReal_le_ofReal (chebyshev r stat eps heps)

theorem statistic_chernoff (r : FinDist R) (stat : R → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    (statisticLaw r stat).toMeasure {x | a ≤ x} ≤
      ENNReal.ofReal (Real.exp (-(t * a)) * r.expect (fun z => Real.exp (t * stat z))) := by
  rw [statistic_event r stat {x | a ≤ x} (by measurability)]
  exact ENNReal.ofReal_le_ofReal (chernoff_upper r stat a t ht)

section ProductRecord

variable {I : Type} [Fintype I] [DecidableEq I]
  {X : I → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

def ProductRecord (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i)) : Prop :=
  ∀ ω, (∑ z, if read z = ω then r.prob z else 0) = ∏ i, (p i).prob (ω i)

theorem product_observe (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) : observe r read = independent p := by
  apply FinDist.ext
  intro ω
  rw [observe_mass]
  exact hjoint ω

theorem product_measure (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    ((toPMF r).map read).toMeasure = Measure.pi (fun i => (toPMF (p i)).toMeasure) := by
  rw [← observe_toPMF, product_observe r read p hjoint]
  exact independent_toMeasure p

theorem product_independent (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    ProbabilityTheory.iIndepFun (fun i (ω : ∀ i, X i) => ω i) ((toPMF r).map read).toMeasure := by
  rw [← observe_toPMF, product_observe r read p hjoint]
  exact independent_coordinates p

theorem product_raw_independent (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) [MeasurableSpace R] [MeasurableSingletonClass R]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    ProbabilityTheory.iIndepFun (fun i z => read z i) (toPMF r).toMeasure := by
  have h := product_independent r read p hjoint
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hm
  have ht := h S hm
  have he (E : Set (∀ i, X i)) : ((toPMF r).map read).toMeasure E =
      (toPMF r).toMeasure (read ⁻¹' E) :=
    PMF.toMeasure_map_apply read (toPMF r) E (measurable_of_countable read)
      (Set.to_countable E).measurableSet
  simp_rw [he] at ht
  simpa only [Set.preimage_iInter, Set.preimage_preimage, Function.comp_def] using! ht

theorem product_expect (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (f : (∀ i, X i) → ℝ) :
    r.expect (fun z => f (read z)) = (independent p).expect f := by
  rw [← observe_expect, product_observe r read p hjoint]

theorem product_variance (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (f : (∀ i, X i) → ℝ) :
    r.variance (fun z => f (read z)) = (independent p).variance f := by
  rw [← observe_variance, product_observe r read p hjoint]

theorem product_event (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (E : (∀ i, X i) → Prop) [DecidablePred E] :
    eventMass r (fun z => E (read z)) = eventMass (independent p) E := by
  rw [← observe_event, product_observe r read p hjoint]

theorem frontier1 (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (w : I → ℝ) (f : ∀ i, X i → ℝ) :
    (toPMF r).map read = toPMF (independent p) ∧
    r.expect (fun z => weightedSum w f (read z)) = ∑ i, w i * (p i).expect (f i) ∧
    r.variance (fun z => weightedSum w f (read z)) = ∑ i, (w i)^2 * (p i).variance (f i) ∧
    (∀ k : ℕ, r.expect (fun z =>
      (weightedSum w f (read z) - r.expect (fun z => weightedSum w f (read z))) ^ k) =
      (independent p).expect (fun ω =>
        (weightedSum w f ω - (independent p).expect (weightedSum w f)) ^ k)) := by
  have hm := product_expect r read p hjoint (weightedSum w f)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← observe_toPMF, product_observe r read p hjoint]
  · rw [hm,
      Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
  · rw [product_variance r read p hjoint,
      Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_variance]
  · intro k
    rw [hm]
    exact product_expect r read p hjoint (fun ω =>
      (weightedSum w f ω - (independent p).expect (weightedSum w f)) ^ k)

theorem product_hoeffding (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u : ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (hu : 0 < u)
    (hS : 0 < ∑ i, (w i)^2 * (b i - a i)^2) :
    eventMass r (fun z => u ≤ |weightedSum w f (read z) -
      r.expect (fun z => weightedSum w f (read z))|) ≤
        2 * Real.exp (-2 * u^2 / (∑ i, (w i)^2 * (b i-a i)^2)) := by
  rw [product_expect r read p hjoint (weightedSum w f),
    product_event r read p hjoint (fun ω =>
      u ≤ |weightedSum w f ω - (independent p).expect (weightedSum w f)|)]
  exact independent_weighted_hoeffding p w f a b u hab hf hu hS

theorem product_output_hoeffding (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u : ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (hu : 0 < u)
    (hS : 0 < ∑ i, (w i)^2 * (b i-a i)^2) :
    (statisticLaw r (fun z => weightedSum w f (read z))).toMeasure
      {x | u ≤ |x - r.expect (fun z => weightedSum w f (read z))|} ≤
      ENNReal.ofReal (2 * Real.exp (-2*u^2/(∑ i, (w i)^2*(b i-a i)^2))) := by
  rw [statistic_event r _ _ (by measurability)]
  exact ENNReal.ofReal_le_ofReal (product_hoeffding r read p hjoint w f a b u hab hf hu hS)

theorem product_zero_width (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u : ℝ) (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i))
    (hu : 0 < u) (hS : (∑ i, (w i)^2 * (b i-a i)^2) = 0) :
    eventMass r (fun z => u ≤ |weightedSum w f (read z) -
      r.expect (fun z => weightedSum w f (read z))|) = 0 := by
  rw [product_expect r read p hjoint (weightedSum w f),
    product_event r read p hjoint (fun ω =>
      u ≤ |weightedSum w f ω - (independent p).expect (weightedSum w f)|)]
  exact independent_weighted_zero_width p w f a b u hf hu hS

end ProductRecord

theorem record_bounded_differences {X : Type} [Fintype X] [DecidableEq X]
    (r : FinDist R) (n : ℕ) (read : R → Fin n → X) (p : Fin n → FinDist X)
    (hjoint : ProductRecord r read p) (f : (Fin n → X) → ℝ) (c : Fin n → ℝ)
    (u : ℝ) (hc : ∀ i, 0 ≤ c i) (hS : 0 < ∑ i, (c i)^2) (hu : 0 < u)
    (hd : ∀ i ω τ, (∀ j, j ≠ i → ω j = τ j) → |f ω - f τ| ≤ c i) :
    eventMass r (fun z => u ≤ |f (read z) - r.expect (fun z => f (read z))|) ≤
      2 * Real.exp (-2 * u^2 / (∑ i, (c i)^2)) := by
  rw [product_expect r read p hjoint f,
    product_event r read p hjoint (fun ω => u ≤ |f ω - (independent p).expect f|)]
  exact bounded_differences_tail n p f c u hc hS hu hd

theorem record_median_of_means {X : Type} [Fintype X] [DecidableEq X]
    (r : FinDist R) (p : FinDist X) (f : X → ℝ) (L M : ℕ)
    (read : R → Fin M → Fin L → X)
    (hjoint : ProductRecord r read (fun _ : Fin M => independent (fun _ : Fin L => p)))
    (hL : 0 < L) (hM : 0 < M) (eps : ℝ) (heps : 0 < eps)
    (hvar : 4 * p.variance f ≤ (L : ℝ) * eps^2) :
    eventMass r (fun z => eps < |p.medianOfMeans f (read z) - p.expect f|) ≤
      3^(M/2) / 2^M := by
  rw [product_event r read _ hjoint (fun ω => eps < |p.medianOfMeans f ω - p.expect f|)]
  exact median_of_means p f L M hL hM eps heps hvar

theorem record_median_output {X : Type} [Fintype X] [DecidableEq X]
    (r : FinDist R) (p : FinDist X) (f : X → ℝ) (L M : ℕ)
    (read : R → Fin M → Fin L → X)
    (hjoint : ProductRecord r read (fun _ : Fin M => independent (fun _ : Fin L => p)))
    (hL : 0 < L) (hM : 0 < M) (eps : ℝ) (heps : 0 < eps)
    (hvar : 4 * p.variance f ≤ (L : ℝ) * eps^2) :
    (statisticLaw r (fun z => p.medianOfMeans f (read z))).toMeasure
      {x | eps < |x - p.expect f|} ≤ ENNReal.ofReal (3^(M/2) / 2^M) := by
  rw [statistic_event r _ _ (by measurability)]
  exact ENNReal.ofReal_le_ofReal
    (record_median_of_means r p f L M read hjoint hL hM eps heps hvar)

end Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt
