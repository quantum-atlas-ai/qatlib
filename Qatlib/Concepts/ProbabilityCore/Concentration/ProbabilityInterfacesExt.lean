/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-!
# Probability laws of observed finite records

`observe` and `statisticLaw` turn deterministic readings of finite records into finite laws and
real valued output laws. `ProductRecord` specifies their full joint product distribution and
allows expectations, variances, central moments, and concentration bounds to be transported from
independent samples.

The resulting Hoeffding, bounded differences, and median of means interfaces supply record based
versions of the Monte Carlo estimates used in [Montanaro2015].

## Main statements

* `frontier1`: the product output law and weighted expectation, variance, and central moment
  identities.
* `product_hoeffding` and `product_output_hoeffding`: record and output measure concentration.
* `record_median_output`: a median of means error bound for the output law.

## References

* [Montanaro, 2015][Montanaro2015]
-/

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

variable {R Y : Type} [Fintype R] [DecidableEq R] [Fintype Y] [DecidableEq Y]

/-- The finite distribution of the value read from a random finite record. -/
def observe (r : FinDist R) (read : R → Y) : FinDist Y :=
  ofPMF ((toPMF r).map read)

omit [DecidableEq R] [DecidableEq Y] in

/-- The PMF of an observed finite law is the image of the original PMF under the reading
function. -/
theorem observe_toPMF (r : FinDist R) (read : R → Y) :
    toPMF (observe r read) = (toPMF r).map read := toPMF_ofPMF _

/-- An observed value has probability equal to the sum of the record probabilities in its
reading fiber. -/
theorem observe_mass (r : FinDist R) (read : R → Y) (y : Y) :
    (observe r read).prob y = ∑ z, if read z = y then r.prob z else 0 := by
  obtain ⟨q, μ, ν, hq, hμ, hν, hmap, _⟩ :=
      (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pushforward_pmf r) read
  have he : (toPMF r).map read = toPMF q := by
    rw [toPMF_unique r μ hμ, hmap, toPMF_unique q ν hν]
  rw [observe, he, ofPMF_toPMF_prob, hq]

/-- Expectation under the observed law equals expectation of the composed reading statistic
under the record law. -/
theorem observe_expect (r : FinDist R) (read : R → Y) (f : Y → ℝ) :
    (observe r read).expect f = r.expect (fun z => f (read z)) :=
  (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.expect_eq_of_pushforward r) (observe r read) read f (observe_mass r read)

/-- Variance under the observed law equals variance of the composed reading statistic under the
record law. -/
theorem observe_variance (r : FinDist R) (read : R → Y) (f : Y → ℝ) :
    (observe r read).variance f = r.variance (fun z => f (read z)) :=
  (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.variance_eq_of_pushforward r) (observe r read) read f (observe_mass r read)

omit [DecidableEq R] in

/-- The finite event mass is the expectation of its zero and one indicator. -/
private theorem eventMass_expect (r : FinDist R) (E : R → Prop) [DecidablePred E] :
    eventMass r E = r.expect (fun z => if E z then 1 else 0) := by
  simp [eventMass, FinDist.expect, Finset.sum_filter]

/-- The mass of an observed event equals the record mass of its preimage under the reading
function. -/
theorem observe_event (r : FinDist R) (read : R → Y) (E : Y → Prop) [DecidablePred E] :
    eventMass (observe r read) E = eventMass r (fun z => E (read z)) := by
  rw [eventMass_expect, observe_expect, eventMass_expect]

/-- The PMF on real outputs induced by a real statistic of a finite random record. -/
def statisticLaw (r : FinDist R) (stat : R → ℝ) : PMF ℝ := (toPMF r).map stat

/-- The output measure of a measurable real event equals the nonnegative real image of the
corresponding finite record event mass. -/
theorem statistic_event (r : FinDist R) (stat : R → ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    letI : MeasurableSpace R := ⊤
    (statisticLaw r stat).toMeasure E = ENNReal.ofReal (eventMass r (fun z => stat z ∈ E)) := by
  letI : MeasurableSpace R := ⊤
  classical
  rw [statisticLaw, PMF.toMeasure_map_apply _ _ _ (measurable_of_countable stat) hE]
  exact eventMass_toMeasure r _

/-- The integral of a measurable function against the statistic output law equals finite
expectation of its composition with the statistic. -/
theorem statistic_integral (r : FinDist R) (stat : R → ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) :
    letI : MeasurableSpace R := ⊤
    ∫ x, f x ∂(statisticLaw r stat).toMeasure = r.expect (fun z => f (stat z)) := by
  letI : MeasurableSpace R := ⊤
  rw [statisticLaw, ← PMF.toMeasure_map stat (toPMF r) (measurable_of_countable stat),
    integral_map (measurable_of_countable stat).aemeasurable hf.aestronglyMeasurable]
  exact integral_eq_expect r _

/-- The central moment integral of the statistic output law equals the corresponding finite
record central moment. -/
theorem statistic_moment (r : FinDist R) (stat : R → ℝ) (k : ℕ) :
    letI : MeasurableSpace R := ⊤
    ∫ x, (x - r.expect stat) ^ k ∂(statisticLaw r stat).toMeasure =
      r.expect (fun z => (stat z - r.expect stat) ^ k) := by
  apply statistic_integral
  fun_prop

omit [DecidableEq R] [DecidableEq Y] in

/-- Taking the real statistic law after observing a record equals taking the law of the composed
statistic directly. -/
theorem statistic_observe (r : FinDist R) (read : R → Y) (f : Y → ℝ) :
    statisticLaw (observe r read) f = statisticLaw r (fun z => f (read z)) := by
  simp only [statisticLaw, observe_toPMF, PMF.map_comp, Function.comp_def]

/-- The statistic output measure satisfies Chebyshev's inequality with the record expectation
and variance. -/
theorem statistic_chebyshev (r : FinDist R) (stat : R → ℝ) (eps : ℝ) (heps : 0 < eps) :
    (statisticLaw r stat).toMeasure {x | eps ≤ |x - r.expect stat|} ≤
      ENNReal.ofReal (r.variance stat / eps ^ 2) := by
  rw [statistic_event r stat _ (by measurability)]
  exact ENNReal.ofReal_le_ofReal (chebyshev r stat eps heps)

/-- For nonnegative exponential parameter, the statistic output upper tail is bounded by the
record exponential moment times the Chernoff factor. -/
theorem statistic_chernoff (r : FinDist R) (stat : R → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    (statisticLaw r stat).toMeasure {x | a ≤ x} ≤
      ENNReal.ofReal (Real.exp (-(t * a)) * r.expect (fun z => Real.exp (t * stat z))) := by
  rw [statistic_event r stat {x | a ≤ x} (by measurability)]
  exact ENNReal.ofReal_le_ofReal (chernoff_upper r stat a t ht)

section ProductRecord

variable {I : Type} [Fintype I] [DecidableEq I]
  {X : I → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The condition that every reading fiber has probability equal to the product of the
prescribed coordinate probabilities. -/
def ProductRecord (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i)) : Prop :=
  ∀ ω, (∑ z, if read z = ω then r.prob z else 0) = ∏ i, (p i).prob (ω i)

/-- A reading satisfying `ProductRecord` has exactly the specified independent product law. -/
theorem product_observe (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) : observe r read = independent p := by
  apply FinDist.ext
  intro ω
  rw [observe_mass]
  exact hjoint ω

/-- The measure of a product record reading is the product of the marginal PMF measures. -/
theorem product_measure (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    ((toPMF r).map read).toMeasure = Measure.pi (fun i => (toPMF (p i)).toMeasure) := by
  rw [← observe_toPMF, product_observe r read p hjoint]
  exact independent_toMeasure p

/-- Coordinate projections of a product record reading are mutually independent under its output
measure. -/
theorem product_independent (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    ProbabilityTheory.iIndepFun (fun i (ω : ∀ i, X i) => ω i) ((toPMF r).map read).toMeasure := by
  rw [← observe_toPMF, product_observe r read p hjoint]
  exact independent_coordinates p

/-- The coordinate readings are mutually independent on the original finite record probability
space. -/
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

/-- For a product record, expectation of a function of the reading equals expectation under the
specified independent law. -/
theorem product_expect (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (f : (∀ i, X i) → ℝ) :
    r.expect (fun z => f (read z)) = (independent p).expect f := by
  rw [← observe_expect, product_observe r read p hjoint]

/-- For a product record, variance of a function of the reading equals variance under the
specified independent law. -/
theorem product_variance (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (f : (∀ i, X i) → ℝ) :
    r.variance (fun z => f (read z)) = (independent p).variance f := by
  rw [← observe_variance, product_observe r read p hjoint]

/-- For a product record, event masses of reading predicates equal their masses under the
specified independent law. -/
theorem product_event (r : FinDist R) (read : R → ∀ i, X i) (p : ∀ i, FinDist (X i))
    (hjoint : ProductRecord r read p) (E : (∀ i, X i) → Prop) [DecidablePred E] :
    eventMass r (fun z => E (read z)) = eventMass (independent p) E := by
  rw [← observe_event, product_observe r read p hjoint]

/-- A product record has the prescribed joint PMF, weighted mean and variance formulas, and the
same weighted central moments as the independent law. -/
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

/-- A bounded weighted statistic read from a product record satisfies the two sided Hoeffding
bound with squared weighted interval widths. -/
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

/-- The output measure of a bounded weighted product record statistic satisfies the two sided
Hoeffding bound. -/
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

/-- If the total squared weighted interval width is zero, a product record weighted statistic
has zero probability of any positive centered deviation. -/
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

/-- A function of a product record reading satisfies the bounded differences tail bound for its
coordinate sensitivities. -/
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

/-- Under the product record condition and block variance bound, a median of means reading has
error probability at most `3 ^ (M / 2) / 2 ^ M`. -/
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

/-- The output law of a product record median of means has error mass at most `3 ^ (M / 2) / 2 ^
M` under the stated block size and variance assumptions. -/
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
