/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PilotVariance.PilotQuantumMeanConsumers
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Mathlib.Probability.ProductMeasure

/-!
# Certified Pilot Moments and Fresh Mean Estimates

Independent pilot samples are represented by `stageLaw`, and `badMoments` records failure of
either empirical first or second moment. Chebyshev bounds give `moments_failure`; a good pilot
record yields the variance upper bound `varianceCertificate`. The dependent law `freshJoint`
then supports a fresh main sample whose size is chosen from that certificate, with
`joint_failure` separating the pilot and conditional main failure terms.

The countable product `streamMeasure` and geometric allocation `stageBudget` provide
simultaneous guarantees across all scheduled stages. Rescaling by a positive payoff bound
extends the construction to bounded rational payoffs, while `quantumLaw` connects the pilot
certificate to a repeated signed quantum mean readout. This quantum consumer lies in the
variance-sensitive Monte Carlo estimation setting of [Montanaro2015], with its precise
finite-record bounds stated explicitly here.

## Main statements

* `certificate_good` and `certificate_bounds`: good pilot moments certify the variance, and
  every certificate lies in `[0, 4]` under the unit payoff assumptions.
* `joint_failure` and `worst_resources`: the main empirical mean has failure bound `2 / (N nu²)
  + δ` and uses at most `N + sampleCount 4 eps δ` observations.
* `frontier1`: the rescaled bounded-payoff readout has failure probability at most `δpilot +
  δmain`.
* `quantum_bounded_failure` and `quantum_precision`: the quantum readout has failure bound `2 /
  (N nu²) + (8/9)^r` and a certified precision range.
* `simultaneous_certificates`: all scheduled rescaled moment and variance certificates hold
  outside an event of measure at most `δ`.

## References

- [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.PilotVariance

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.CertifiedPilotCore
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces MeasureTheory
open scoped Classical BigOperators ENNReal

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Define the finite law of `N` independent observations, each with distribution `p`. -/
def stageLaw (p : FinDist I) (N : ℕ) : FinDist (Fin N → I) :=
  independentSampleLaw (fun _ : Fin N => p)

/-- Form the law of a dependent pair by assigning mass `p.prob h * (q h).prob x` to `⟨h, x⟩`.
The second record is drawn from the law selected by the first. -/
def freshJoint {H : Type} [Fintype H] {S : H → Type} [∀ h, Fintype (S h)]
    (p : FinDist H) (q : ∀ h, FinDist (S h)) : FinDist (Σ h, S h) where
  prob z := p.prob z.1 * (q z.1).prob z.2
  nonneg z := mul_nonneg (p.nonneg _) ((q _).nonneg _)
  sum_one := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ h, p.prob h := by
        apply Finset.sum_congr rfl
        intro h _
        change (∑ y : S h, p.prob h * (q h).prob y) = p.prob h
        rw [← Finset.mul_sum, (q h).sum_one, mul_one]
      _ = 1 := p.sum_one

/-- Compute an event's mass under `freshJoint` by summing its conditional event masses against
the first-record probabilities. -/
theorem fresh_event {H : Type} [Fintype H] {S : H → Type} [∀ h, Fintype (S h)]
    (p : FinDist H) (q : ∀ h, FinDist (S h)) (E : (Σ h, S h) → Prop) :
    eventMass (freshJoint p q) E = ∑ h, p.prob h * eventMass (q h) (fun x => E ⟨h,x⟩) := by
  simp only [eventMass, Finset.sum_filter, Fintype.sum_sigma, freshJoint,
    Finset.mul_sum, mul_ite, mul_zero]

/-- If the conditional event probability is at most a nonnegative `δmain` whenever the first
record is good, its joint probability is at most the first-record bad probability plus
`δmain`. -/
theorem fresh_failure {H : Type} [Fintype H] {S : H → Type} [∀ h, Fintype (S h)]
    (p : FinDist H) (q : ∀ h, FinDist (S h)) (bad : H → Prop)
    (E : (Σ h, S h) → Prop) (δmain : ℝ) (hδ : 0 ≤ δmain)
    (hmain : ∀ h, ¬bad h → eventMass (q h) (fun x => E ⟨h,x⟩) ≤ δmain) :
    eventMass (freshJoint p q) E ≤ eventMass p bad + δmain := by
  rw [fresh_event]
  have hpoint (h : H) : eventMass (q h) (fun x => E ⟨h,x⟩) ≤ (if bad h then 1 else δmain) := by
    by_cases hb : bad h
    · rw [if_pos hb]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => (q h).nonneg x)).trans_eq (q h).sum_one
    · rw [if_neg hb]
      exact hmain h hb
  calc
    _ ≤ ∑ h, p.prob h * (if bad h then 1 else δmain) :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hpoint h) (p.nonneg h)
    _ = eventMass p bad + (∑ h ∈ Finset.univ.filter (fun h => ¬bad h), p.prob h) * δmain := by
      simp only [mul_ite, mul_one, Finset.sum_ite, eventMass, Finset.sum_mul]
    _ ≤ _ := by
      have hsum : (∑ h ∈ Finset.univ.filter (fun h => ¬bad h), p.prob h) ≤ 1 :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun h _ _ => p.nonneg h)).trans_eq p.sum_one
      nlinarith

local instance (N : ℕ → ℕ) (j : ℕ) : MeasurableSpace (Fin (N j) → I) := ⊤
local instance (N : ℕ → ℕ) (j : ℕ) : MeasurableSingletonClass (Fin (N j) → I) := ⟨fun _ => trivial⟩

/-- Construct the countable product measure of independent stage records, where stage `j`
consists of `N j` observations from `p`. -/
def streamMeasure (p : FinDist I) (N : ℕ → ℕ) : Measure (∀ j : ℕ, Fin (N j) → I) :=
  Measure.infinitePi (fun j => (toPMF (stageLaw p (N j))).toMeasure)

instance stream_probability (p : FinDist I) (N : ℕ → ℕ) : IsProbabilityMeasure (streamMeasure p N) := by
  unfold streamMeasure
  infer_instance

/-- An event depending only on stage `j` has stream measure equal to the nonnegative
extended-real embedding of its mass under `stageLaw p (N j)`. -/
theorem stream_coordinate (p : FinDist I) (N : ℕ → ℕ)
    (E : ∀ j : ℕ, (Fin (N j) → I) → Prop) (j : ℕ) :
    streamMeasure p N {ω | E j (ω j)} = ENNReal.ofReal (eventMass (stageLaw p (N j)) (E j)) := by
  have hE : MeasurableSet {x : Fin (N j) → I | E j x} := (Set.toFinite _).measurableSet
  calc
    _ = ((streamMeasure p N).map (fun ω => ω j)) {x | E j x} :=
      (Measure.map_apply (measurable_pi_apply j) hE).symm
    _ = (toPMF (stageLaw p (N j))).toMeasure {x | E j x} := by
      rw [streamMeasure, Measure.infinitePi_map_eval]
    _ = _ := eventMass_toMeasure _ _

/-- Bound the measure of a failure at any stage by the sum of the nonnegative extended-real
embeddings of the supplied stagewise bounds. -/
theorem stream_union (p : FinDist I) (N : ℕ → ℕ)
    (E : ∀ j : ℕ, (Fin (N j) → I) → Prop) (δ : ℕ → ℝ)
    (hδ : ∀ j, eventMass (stageLaw p (N j)) (E j) ≤ δ j) :
    streamMeasure p N (⋃ j : ℕ, {ω | E j (ω j)}) ≤ ∑' j : ℕ, ENNReal.ofReal (δ j) := by
  exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => by
    rw [stream_coordinate]
    exact ENNReal.ofReal_le_ofReal (hδ j))

/-- Allocate the rational failure budget `δ / 2^(j + 1)` to stage `j`. -/
def stageBudget (δ : ℚ) (j : ℕ) : ℚ := (δ/2) * (1/2)^j

/-- For nonnegative `δ`, the extended-real sum of all geometric stage budgets is exactly the
embedding of `δ`. -/
theorem stageBudget_sum (δ : ℚ) (hδ : 0 ≤ δ) :
    (∑' j : ℕ, ENNReal.ofReal (stageBudget δ j : ℝ)) = ENNReal.ofReal (δ : ℝ) := by
  have hd : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  simp only [stageBudget, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (by linarith) (by positivity))
    (summable_geometric_two.mul_left ((δ:ℝ)/2)), tsum_mul_left, tsum_geometric_two]
  congr 1
  ring

/-- Declare a pilot record bad if either its empirical first moment or empirical second moment
differs from the corresponding population moment by more than `nu`. -/
def badMoments (p : FinDist I) (N : ℕ) (f : I → ℚ) (nu : ℚ) (ω : Fin N → I) : Prop :=
  (nu : ℝ) < |FinDist.avg (fun i => (f i : ℝ)) ω - p.expect (fun i => (f i : ℝ))| ∨
  (nu : ℝ) < |FinDist.avg (fun i => (f i : ℝ)^2) ω - p.expect (fun i => (f i : ℝ)^2)|

/-- Identify event mass under the independent stage law with the finite distribution's
sample-event probability. -/
theorem stage_event (p : FinDist I) (N : ℕ) (E : (Fin N → I) → Prop) :
    eventMass (stageLaw p N) E = p.probEvent E := rfl

/-- A real payoff bounded in absolute value by one has variance at most one under any finite
probability law. -/
theorem bounded_variance (p : FinDist I) (f : I → ℝ) (hf : ∀ i, |f i| ≤ 1) :
    p.variance f ≤ 1 := by
  rw [FinDist.variance_eq_expect_sq_sub]
  have hs : p.expect (fun i => f i^2) ≤ 1 := calc
    _ ≤ ∑ i, p.prob i := Finset.sum_le_sum fun i _ => by
      have hi := abs_le.mp (hf i)
      exact mul_le_of_le_one_right (p.nonneg i) (by nlinarith)
    _ = 1 := p.sum_one
  nlinarith [sq_nonneg (p.expect f)]

/-- For a payoff bounded in absolute value by one, positive sample size `N`, and positive
tolerance `nu`, the probability that either pilot moment fails is at most `2 / (N * nu^2)`. -/
theorem moments_failure (p : FinDist I) (N : ℕ) (f : I → ℚ) (nu : ℚ)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) :
    eventMass (stageLaw p N) (badMoments p N f nu) ≤ 2/((N : ℝ)*(nu : ℝ)^2) := by
  have hn : (0 : ℝ) < nu := by exact_mod_cast hnu
  have hd : (0 : ℝ) < (N : ℝ)*(nu : ℝ)^2 := by positivity
  have hfr : ∀ i, |(f i : ℝ)| ≤ 1 := fun i => by exact_mod_cast hf i
  have hfs : ∀ i, |(f i : ℝ)^2| ≤ 1 := by
    intro i
    rw [abs_of_nonneg (sq_nonneg _)]
    have := abs_le.mp (hfr i)
    nlinarith
  have h₁ := (p.chebyshev_avg (fun i => (f i : ℝ)) hN nu hn).trans
    (div_le_div_of_nonneg_right (bounded_variance p _ hfr) hd.le)
  have h₂ := (p.chebyshev_avg (fun i => (f i : ℝ)^2) hN nu hn).trans
    (div_le_div_of_nonneg_right (bounded_variance p _ hfs) hd.le)
  have hu := eventMass_or_le (stageLaw p N)
    (fun ω => (nu : ℝ) < |FinDist.avg (fun i => (f i : ℝ)) ω - p.expect (fun i => (f i : ℝ))|)
    (fun ω => (nu : ℝ) < |FinDist.avg (fun i => (f i : ℝ)^2) ω - p.expect (fun i => (f i : ℝ)^2)|)
  rw [stage_event, stage_event] at hu
  calc
    _ ≤ p.probEvent (fun ω : Fin N → I => (nu : ℝ) < |FinDist.avg (fun i => (f i : ℝ)) ω - p.expect (fun i => (f i : ℝ))|) +
        p.probEvent (fun ω : Fin N → I => (nu : ℝ) < |FinDist.avg (fun i => (f i : ℝ)^2) ω - p.expect (fun i => (f i : ℝ)^2)|) := by
      simpa only [eventMass, badMoments] using! hu
    _ ≤ 1/((N : ℝ)*(nu : ℝ)^2) + 1/((N : ℝ)*(nu : ℝ)^2) := add_le_add h₁ h₂
    _ = 2/((N : ℝ)*(nu : ℝ)^2) := by ring

/-- Define the rational variance certificate as the square of the scale selected from the pilot
record. -/
def varianceCertificate (N depth : ℕ) (f : I → ℚ) (nu : ℚ) (ω : Fin N → I) : ℚ :=
  (pilotScale N depth f nu ω)^2

/-- Under the unit payoff bound, positive sample size, and `0 < nu ≤ 1/4`, a good pilot record
approximates both population moments within `nu` and gives a variance certificate at least
as large as the true variance. -/
theorem certificate_good (p : FinDist I) (N depth : ℕ) (f : I → ℚ) (nu : ℚ)
    (ω : Fin N → I) (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (hg : ¬badMoments p N f nu ω) :
    |((pilotMoments N f ω).1 : ℝ) - p.expect (fun i => (f i : ℝ))| ≤ nu ∧
    |((pilotMoments N f ω).2.1 : ℝ) - p.expect (fun i => (f i : ℝ)^2)| ≤ nu ∧
    p.variance (fun i => (f i : ℝ)) ≤ (varianceCertificate N depth f nu ω : ℝ) := by
  have hgood := not_or.mp hg
  have hm := pilotMoments_cast_avg N f ω
  have h₁ : |((pilotMoments N f ω).1 : ℝ) - p.expect (fun i => (f i : ℝ))| ≤ nu := by
    rw [hm.1]; exact le_of_not_gt hgood.1
  have h₂ : |((pilotMoments N f ω).2.1 : ℝ) - p.expect (fun i => (f i : ℝ)^2)| ≤ nu := by
    rw [hm.2]; exact le_of_not_gt hgood.2
  exact ⟨h₁, h₂, by simpa [varianceCertificate] using!
    (unknown_variance_pilot_good_moments_certificate I p N depth f nu ω hN hf hnu hnu1 h₁ h₂).1⟩

/-- Under the unit payoff bound, positive sample size, and `0 < nu ≤ 1/4`, every pilot variance
certificate lies between zero and four. -/
theorem certificate_bounds (N depth : ℕ) (f : I → ℚ) (nu : ℚ) (ω : Fin N → I)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) :
    0 ≤ varianceCertificate N depth f nu ω ∧ varianceCertificate N depth f nu ω ≤ 4 := by
  have hs := unknown_variance_pilot_native_moments_and_scale I N depth f nu ω hN hf hnu hnu1
  have h₀ := hs.2.2.2.2.1
  have h₂ := hs.2.2.2.2.2.1
  unfold varianceCertificate
  exact ⟨sq_nonneg _, by nlinarith⟩

/-- Choose the sample size as the maximum of one and the natural ceiling of `U / (δ * eps^2)`. -/
def sampleCount (U eps δ : ℚ) : ℕ := max 1 ⌈U/(δ*eps^2)⌉₊

/-- The prescribed sample count is positive for every choice of its rational parameters. -/
theorem sampleCount_pos (U eps δ : ℚ) : 0 < sampleCount U eps δ :=
  lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)

/-- For positive `eps` and `δ`, the prescribed sample count makes `U / (sampleCount U eps δ *
eps^2)` at most `δ`. -/
theorem sampleCount_budget (U eps δ : ℚ) (heps : 0 < eps) (hδ : 0 < δ) :
    (U : ℝ) / ((sampleCount U eps δ : ℝ)*(eps : ℝ)^2) ≤ δ := by
  have hceil : U/(δ*eps^2) ≤ (sampleCount U eps δ : ℚ) :=
    (Nat.le_ceil _).trans (by
      change (⌈U/(δ*eps^2)⌉₊ : ℚ) ≤ (max 1 ⌈U/(δ*eps^2)⌉₊ : ℕ)
      exact_mod_cast (Nat.le_max_right 1 (Nat.ceil (U/(δ*eps^(2:ℕ))))))
  have hq : U ≤ (sampleCount U eps δ : ℚ)*(δ*eps^2) :=
    (div_le_iff₀ (by positivity)).mp hceil
  have hr : (U : ℝ) ≤ (sampleCount U eps δ : ℝ)*((δ : ℝ)*(eps : ℝ)^2) := by exact_mod_cast hq
  apply (div_le_iff₀ (by have := sampleCount_pos U eps δ; positivity)).mpr
  nlinarith

/-- For positive error tolerance and failure budget, increasing the variance proxy cannot
decrease the prescribed sample count. -/
theorem sampleCount_mono {U V : ℚ} (eps δ : ℚ) (heps : 0 < eps) (hδ : 0 < δ)
    (hUV : U ≤ V) : sampleCount U eps δ ≤ sampleCount V eps δ := by
  apply max_le_max le_rfl
  exact Nat.ceil_mono (div_le_div_of_nonneg_right hUV (by positivity))

/-- Choose stage `j`'s pilot size using variance proxy two, moment tolerance `nu`, and the
geometric failure budget `stageBudget δ j`. -/
def pilotCount (δ nu : ℚ) (j : ℕ) : ℕ := sampleCount 2 nu (stageBudget δ j)

/-- A positive total budget gives a positive geometric budget at every stage. -/
theorem stageBudget_pos (δ : ℚ) (hδ : 0 < δ) (j : ℕ) : 0 < stageBudget δ j := by
  unfold stageBudget
  positivity

/-- For a unit-bounded payoff and positive tolerance and budget, the stream probability that any
scheduled pilot record has a bad first or second moment is at most `δ`. -/
theorem simultaneous_moments (p : FinDist I) (f : I → ℚ) (nu δ : ℚ)
    (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hδ : 0 < δ) :
    streamMeasure p (pilotCount δ nu)
      (⋃ j : ℕ, {ω | badMoments p (pilotCount δ nu j) f nu (ω j)}) ≤ ENNReal.ofReal (δ : ℝ) := by
  rw [← stageBudget_sum δ hδ.le]
  apply stream_union
  intro j
  exact (moments_failure p _ f nu (sampleCount_pos _ _ _) hf hnu).trans
    (sampleCount_budget 2 nu (stageBudget δ j) hnu (stageBudget_pos δ hδ j))

/-- Choose the fresh main sample size from the pilot variance certificate, target error `eps`,
and failure budget `δ`. -/
def mainCount (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ) (ω : Fin N → I) : ℕ :=
  sampleCount (varianceCertificate N depth f nu ω) eps δ

/-- Represent a pilot record together with a fresh main record whose length is determined by
that pilot record's variance certificate. -/
abbrev MainRecord (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ) :=
  Σ ω : Fin N → I, Fin (mainCount N depth f nu eps δ ω) → I

/-- Draw an independent pilot sample from `p`, then draw a fresh independent sample from `p` of
the pilot-selected main length. -/
def mainLaw (p : FinDist I) (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ) :
    FinDist (MainRecord N depth f nu eps δ) :=
  freshJoint (stageLaw p N) (fun ω => stageLaw p (mainCount N depth f nu eps δ ω))

/-- Return the rational empirical mean of the main sample in a dependent pilot-and-main record. -/
def mainReadout (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ)
    (z : MainRecord N depth f nu eps δ) : ℚ := (pilotMoments _ f z.2).1

/-- Count the total observations as the fixed pilot size plus the main sample size selected by
the pilot record. -/
def resources (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ)
    (z : MainRecord N depth f nu eps δ) : ℕ := N + mainCount N depth f nu eps δ z.1

/-- Under the unit payoff bound and positive parameters with `nu ≤ 1/4`, the probability that
the main readout's error exceeds `eps` is at most `2 / (N * nu^2) + δ`. -/
theorem joint_failure (p : FinDist I) (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (hδ : 0 < δ) :
    eventMass (mainLaw p N depth f nu eps δ)
      (fun z => (eps : ℝ) < |(mainReadout N depth f nu eps δ z : ℝ) - p.expect (fun i => (f i : ℝ))|)
      ≤ 2/((N : ℝ)*(nu : ℝ)^2) + δ := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast hδ
  apply (fresh_failure (stageLaw p N) _ (badMoments p N f nu) _ δ hd.le ?_).trans
    (add_le_add (moments_failure p N f nu hN hf hnu) le_rfl)
  intro ω hg
  have hv := (certificate_good p N depth f nu ω hN hf hnu hnu1 hg).2.2
  have he : (0 : ℝ) < eps := by exact_mod_cast heps
  have hc : 0 < mainCount N depth f nu eps δ ω := sampleCount_pos _ _ _
  change eventMass (stageLaw p _) (fun x => (eps : ℝ) < |((pilotMoments _ f x).1 : ℝ) - _|) ≤ _
  simp_rw [pilotMoments_cast_avg]
  rw [stage_event]
  exact ((p.chebyshev_avg (fun i => (f i : ℝ)) hc eps he).trans
    (div_le_div_of_nonneg_right hv (by positivity))).trans
      (sampleCount_budget _ eps δ heps hδ)

/-- Under the unit payoff bound and positive parameters with `nu ≤ 1/4`, every pilot-and-main
record uses at most `N + sampleCount 4 eps δ` observations. -/
theorem worst_resources (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ)
    (z : MainRecord N depth f nu eps δ) (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) (hδ : 0 < δ) :
    resources N depth f nu eps δ z ≤ N + sampleCount 4 eps δ := by
  exact Nat.add_le_add_left (sampleCount_mono eps δ heps hδ
    (certificate_bounds N depth f nu z.1 hN hf hnu hnu1).2) N

/-- With stage-scheduled pilot size, a unit-bounded payoff, and positive parameters with `nu ≤
1/4`, the main readout exceeds error `eps` with probability at most `δpilot + δmain`. -/
theorem unit_frontier (p : FinDist I) (depth j : ℕ) (f : I → ℚ) (nu eps δpilot δmain : ℚ)
    (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (hp : 0 < δpilot) (hm : 0 < δmain) :
    eventMass (mainLaw p (pilotCount δpilot nu j) depth f nu eps δmain)
      (fun z => (eps : ℝ) < |(mainReadout _ depth f nu eps δmain z : ℝ) - p.expect (fun i => (f i : ℝ))|)
      ≤ (δpilot : ℝ) + δmain := by
  have hj := stageBudget_pos δpilot hp j
  have hb := sampleCount_budget 2 nu (stageBudget δpilot j) hnu hj
  have hstage : stageBudget δpilot j ≤ δpilot := by
    have hpow : (1/2 : ℚ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    unfold stageBudget
    nlinarith
  have hs : (stageBudget δpilot j : ℝ) ≤ δpilot := by exact_mod_cast hstage
  exact (joint_failure p _ depth f nu eps δmain (sampleCount_pos _ _ _) hf hnu hnu1 heps hm).trans
    (by linarith [hb])

/-- Normalize a rational payoff by dividing each of its values by the rational bound `B`. -/
def normalized (B : ℚ) (f : I → ℚ) (i : I) : ℚ := f i / B

/-- If `B` is positive and bounds the payoff's absolute value, the normalized payoff is bounded
in absolute value by one. -/
theorem normalized_bound (B : ℚ) (f : I → ℚ) (hB : 0 < B) (hf : ∀ i, |f i| ≤ B) :
    ∀ i, |normalized B f i| ≤ 1 := by
  intro i
  rw [normalized, abs_div, abs_of_pos hB, div_le_one hB]
  exact hf i

/-- For nonzero `B`, the original payoff expectation is `B` times the expectation of its
normalized payoff. -/
theorem expect_scaled (p : FinDist I) (B : ℚ) (f : I → ℚ) (hB : B ≠ 0) :
    p.expect (fun i => (f i : ℝ)) = (B : ℝ) * p.expect (fun i => (normalized B f i : ℝ)) := by
  unfold FinDist.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB
  simp only [normalized, Rat.cast_div]
  field_simp

/-- For nonzero `B`, the original payoff variance is `B^2` times the variance of its normalized
payoff. -/
theorem variance_scaled (p : FinDist I) (B : ℚ) (f : I → ℚ) (hB : B ≠ 0) :
    p.variance (fun i => (f i : ℝ)) = (B : ℝ)^2 * p.variance (fun i => (normalized B f i : ℝ)) := by
  rw [FinDist.variance_eq_expect_sq_sub, FinDist.variance_eq_expect_sq_sub, expect_scaled p B f hB]
  have he : p.expect (fun i => (f i : ℝ)^2) =
      (B : ℝ)^2 * p.expect (fun i => (normalized B f i : ℝ)^2) := by
    unfold FinDist.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    simp only [normalized, Rat.cast_div]
    field_simp
  rw [he]
  ring

/-- Return the pilot estimates of the original payoff's first and second moments and its
variance upper certificate, rescaling the normalized quantities by `B`, `B^2`, and `B^2`
respectively. -/
def boundedCertificate (B : ℚ) (N depth : ℕ) (f : I → ℚ) (nu : ℚ) (ω : Fin N → I) : ℚ × ℚ × ℚ :=
  (B*(pilotMoments N (normalized B f) ω).1,
   B^2*(pilotMoments N (normalized B f) ω).2.1,
   B^2*varianceCertificate N depth (normalized B f) nu ω)

/-- For a payoff bounded by positive `B`, positive sample size, and `0 < nu ≤ 1/4`, good
normalized pilot moments make the rescaled moment errors at most `B * nu` and `B^2 * nu`.
The third rescaled certificate then bounds the original payoff's variance from above. -/
theorem boundedCertificate_good (p : FinDist I) (B : ℚ) (N depth : ℕ) (f : I → ℚ) (nu : ℚ)
    (ω : Fin N → I) (hB : 0 < B) (hN : 0 < N) (hf : ∀ i, |f i| ≤ B)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (hg : ¬badMoments p N (normalized B f) nu ω) :
    |((boundedCertificate B N depth f nu ω).1 : ℝ) - p.expect (fun i => (f i : ℝ))| ≤ B*nu ∧
    |((boundedCertificate B N depth f nu ω).2.1 : ℝ) - p.expect (fun i => (f i : ℝ)^2)| ≤ B^2*nu ∧
    p.variance (fun i => (f i : ℝ)) ≤ (boundedCertificate B N depth f nu ω).2.2 := by
  have hc :=
      certificate_good p N depth (normalized B f) nu ω hN (normalized_bound B f hB hf) hnu hnu1 hg
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have he : p.expect (fun i => (f i : ℝ)^2) =
      (B : ℝ)^2 * p.expect (fun i => (normalized B f i : ℝ)^2) := by
    unfold FinDist.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hn : (B : ℝ) ≠ 0 := ne_of_gt hb
    simp only [normalized, Rat.cast_div]
    field_simp
  simp only [boundedCertificate, Rat.cast_mul, Rat.cast_pow]
  rw [expect_scaled p B f (ne_of_gt hB), he, variance_scaled p B f (ne_of_gt hB)]
  constructor
  · rw [← mul_sub, abs_mul, abs_of_pos hb]
    exact mul_le_mul_of_nonneg_left hc.1 hb.le
  constructor
  · rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hc.2.1 (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_left hc.2.2 (sq_nonneg _)

/-- Rescale by `B` the main empirical mean computed for the normalized payoff with error target
`eps / B`. -/
def boundedReadout (B : ℚ) (N depth : ℕ) (f : I → ℚ) (nu eps δ : ℚ)
    (z : MainRecord N depth (normalized B f) nu (eps/B) δ) : ℚ :=
  B * mainReadout N depth (normalized B f) nu (eps/B) δ z

/-- For a payoff bounded by positive `B` and positive parameters with `nu ≤ 1/4`, the rescaled
main readout with stage-scheduled pilot size exceeds error `eps` with probability at most
`δpilot + δmain`. -/
theorem frontier1 (p : FinDist I) (B : ℚ) (depth j : ℕ) (f : I → ℚ) (nu eps δpilot δmain : ℚ)
    (hB : 0 < B) (hf : ∀ i, |f i| ≤ B) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (hp : 0 < δpilot) (hm : 0 < δmain) :
    eventMass (mainLaw p (pilotCount δpilot nu j) depth (normalized B f) nu (eps/B) δmain)
      (fun z => (eps : ℝ) < |(boundedReadout B _ depth f nu eps δmain z : ℝ) - p.expect (fun i => (f i : ℝ))|)
      ≤ (δpilot : ℝ) + δmain := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  apply (eventMass_mono _ _ _ ?_).trans
    (unit_frontier p depth j (normalized B f) nu (eps/B) δpilot δmain
      (normalized_bound B f hB hf) hnu hnu1 (div_pos heps hB) hp hm)
  intro z hz
  simp only [boundedReadout, Rat.cast_mul] at hz
  rw [expect_scaled p B f (ne_of_gt hB), ← mul_sub, abs_mul, abs_of_pos hb] at hz
  change ((eps/B : ℚ) : ℝ) < _
  rw [Rat.cast_div, div_lt_iff₀ hb]
  simpa [mul_comm] using! hz

/-- A payoff bounded in absolute value by zero vanishes pointwise and has expectation zero under
the finite law. -/
theorem zero_payoff (p : FinDist I) (f : I → ℚ) (hf : ∀ i, |f i| ≤ 0) :
    (∀ i, f i = 0) ∧ p.expect (fun i => (f i : ℝ)) = 0 := by
  have hz : ∀ i, f i = 0 := fun i => abs_eq_zero.mp (le_antisymm (hf i) (abs_nonneg _))
  exact ⟨hz, by simp [FinDist.expect, hz]⟩

/-- Package the normalized joint masses `pilotMeanMass` as a finite distribution on pilot
records and their conditional repeated signed-mean records for a unitary source. -/
def quantumLaw (A : Matrix I I ℂ) (j : I) (N depth r : ℕ) (f : I → ℚ) (nu eps : ℚ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) : FinDist (PilotMeanRecord I N depth r f nu eps) where
  prob := pilotMeanMass A j N depth r f nu eps hA
  nonneg z := by
    unfold pilotMeanMass
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => FinDist.nonneg _ _)
      (Finset.prod_nonneg fun _ _ => FinDist.nonneg _ _)
  sum_one := pilotMeanMass_sum_one A j N depth r f nu eps hA

/-- For a unitary source and a payoff bounded by positive `B`, under the stated positivity and
pilot-tolerance assumptions the rescaled quantum mean readout exceeds error `eps` with
probability at most `2 / (N * nu^2) + (8/9)^r`. -/
theorem quantum_bounded_failure (A : Matrix I I ℂ) (j : I) (B : ℚ) (N depth r : ℕ)
    (f : I → ℚ) (nu eps : ℚ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hB : 0 < B) (hN : 0 < N) (hf : ∀ i, |f i| ≤ B)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) :
    eventMass (quantumLaw A j N depth r (normalized B f) nu (eps/B) hA)
      (fun z => (eps : ℝ) < |(B : ℝ)*pilotMeanReadout N depth r (normalized B f) nu (eps/B) z -
        (signedMeanSource A j hA).expect (fun i => (f i : ℝ))|) ≤
      2/((N : ℝ)*(nu : ℝ)^2) + (8/9 : ℝ)^r := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  apply (eventMass_mono _ _ _ ?_).trans
    (unknown_variance_pilot_same_joint_quantum_mean_probability I A j N depth r
      (normalized B f) nu (eps/B) hA hN (normalized_bound B f hB hf) hnu hnu1 (div_pos heps hB)).2.2
  intro z hz
  rw [expect_scaled (signedMeanSource A j hA) B f (ne_of_gt hB), ← mul_sub,
    abs_mul, abs_of_pos hb] at hz
  change ((eps/B : ℚ) : ℝ) < _
  rw [Rat.cast_div, div_lt_iff₀ hb]
  simpa [mul_comm] using! hz

/-- Under the bounded-payoff and positivity assumptions, the pilot-selected precision is at
least four and makes `8 * pilotScale * (1/2)^pilotPrecision ≤ eps / B`. It is at most `max 4
(Nat.clog 2 ((⌈16/(eps/B)⌉ : ℤ).toNat + 1))`. -/
theorem quantum_precision (B : ℚ) (N depth : ℕ) (f : I → ℚ) (nu eps : ℚ)
    (ω : Fin N → I) (hB : 0 < B) (hN : 0 < N) (hf : ∀ i, |f i| ≤ B)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) :
    4 ≤ pilotPrecision N depth (normalized B f) nu (eps/B) ω ∧
    8*(pilotScale N depth (normalized B f) nu ω : ℝ)*(1/2 : ℝ)^
      (pilotPrecision N depth (normalized B f) nu (eps/B) ω) ≤ ((eps/B : ℚ) : ℝ) ∧
    pilotPrecision N depth (normalized B f) nu (eps/B) ω ≤
      max 4 (Nat.clog 2 ((⌈16/(eps/B)⌉ : ℤ).toNat+1)) :=
  unknown_variance_pilot_computed_precision_and_worst_path I N depth (normalized B f)
    nu (eps/B) ω hN (normalized_bound B f hB hf) hnu hnu1 (div_pos heps hB)

/-- For a payoff bounded by positive `B` and positive tolerance and budget with `nu ≤ 1/4`, the
probability that any scheduled pilot certificate fails either rescaled moment bound or the
variance upper bound is at most `δ`. -/
theorem simultaneous_certificates (p : FinDist I) (B : ℚ) (depth : ℕ) (f : I → ℚ)
    (nu δ : ℚ) (hB : 0 < B) (hf : ∀ i, |f i| ≤ B)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (hδ : 0 < δ) :
    streamMeasure p (pilotCount δ nu) (⋃ j : ℕ, {ω | ¬(
      |((boundedCertificate B (pilotCount δ nu j) depth f nu (ω j)).1 : ℝ) - p.expect (fun i => (f i : ℝ))| ≤ B*nu ∧
      |((boundedCertificate B (pilotCount δ nu j) depth f nu (ω j)).2.1 : ℝ) - p.expect (fun i => (f i : ℝ)^2)| ≤ B^2*nu ∧
      p.variance (fun i => (f i : ℝ)) ≤ (boundedCertificate B (pilotCount δ nu j) depth f nu (ω j)).2.2)})
      ≤ ENNReal.ofReal (δ : ℝ) := by
  apply (measure_mono (Set.iUnion_mono fun j => ?_)).trans
    (simultaneous_moments p (normalized B f) nu δ (normalized_bound B f hB hf) hnu hδ)
  intro ω hbad
  by_contra hg
  exact hbad (boundedCertificate_good p B _ depth f nu (ω j) hB (sampleCount_pos _ _ _) hf hnu hnu1 hg)

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.CertifiedPilotCore
