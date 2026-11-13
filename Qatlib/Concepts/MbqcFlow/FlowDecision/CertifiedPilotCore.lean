/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CertifiedPilotCore
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Search

/-!
# Certified clipping bounds for pilot estimators

This module controls the bias introduced by clipping finite rational-valued observables, using
either second or fourth moments. `publicMoment` supplies distribution-independent rational
bounds, while `radius` computes a positive clipping threshold with a prescribed bias budget.
Quantum mean estimation provides the broader context; see [Montanaro2015] and
[BrassardEtAl2002].

The clipping estimates are combined with the imported pilot estimator to bound the probability
of exceeding the total readout error. `tableResources` adds the finite table size to the
estimator's resource count.

## Main statements

* `finite_clipping_bias` and `finite_clipping_bias4`: clipping bias bounds from second and
  fourth moments.
* `radius_bias`: the computed threshold meets the requested positive bias budget.
* `frontier1` and `computed_radius_frontier`: failure-probability bounds including clipping
  bias.
* `table_worst`: a worst-case bound on table and estimator resources.

## References

* [Montanaro, 2015][Montanaro2015]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.CertifiedPilotCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.CertifiedPilotCore
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open scoped BigOperators Classical

/-- For a positive clipping threshold, the pointwise clipping error is at most the fourth power
of the input divided by the cube of the threshold. -/
lemma clipping_fourth (T x : ℝ) (hT : 0 < T) :
    |x - Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T x| ≤ x^4 / T^3 := by
  by_cases h : |x| ≤ T
  · have hh := abs_le.mp h
    simp only [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip, min_eq_right hh.2, max_eq_right hh.1,
      sub_self, abs_zero]
    positivity
  · have hs : T^2 ≤ x^2 := by nlinarith [sq_abs x, abs_nonneg x]
    have h4 : x^2*T^2 ≤ x^4 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hs)]
    calc
      _ ≤ x^2/(4*T) := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip_error T x hT
      _ ≤ x^4/T^3 := by
        apply (div_le_div_iff₀ (by positivity : (0:ℝ)<4*T) (by positivity : (0:ℝ)<T^3)).mpr
        have hm := mul_le_mul_of_nonneg_right h4 hT.le
        nlinarith [mul_nonneg (pow_nonneg hT.le 1) (pow_nonneg (sq_nonneg x) 2)]

/-- The change in a finite expectation caused by clipping at a positive threshold is at most the
second moment divided by four times the threshold. -/
lemma finite_clipping_bias {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℝ) (T : ℝ) (hT : 0<T) :
    |p.expect f - p.expect (fun i => Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i))| ≤
      p.expect (fun i => f i^2)/(4*T) := by
  have he : p.expect f - p.expect (fun i => Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i)) =
      ∑ i, p.prob i * (f i-Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i)) := by
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_sub,
        Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, |p.prob i*(f i-Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p.prob i*|f i-Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i)| := by
      simp_rw [abs_mul, abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ i, p.prob i*(f i^2/(4*T)) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip_error T (f i) hT) (p.nonneg i)
    _ = _ := by simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_div_assoc, Finset.sum_div]

/-- The change in a finite expectation caused by clipping at a positive threshold is at most the
fourth moment divided by the cube of the threshold. -/
lemma finite_clipping_bias4 {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℝ) (T : ℝ) (hT : 0<T) :
    |p.expect f - p.expect (fun i => Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i))| ≤
      p.expect (fun i => f i^4)/T^3 := by
  have he : p.expect f - p.expect (fun i => Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i)) =
      ∑ i, p.prob i * (f i-Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i)) := by
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_sub,
        Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, |p.prob i*(f i-Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p.prob i*|f i-Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T (f i)| := by
      simp_rw [abs_mul, abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ i, p.prob i*(f i^4/T^3) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (clipping_fourth T (f i) hT) (p.nonneg i)
    _ = _ := by simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_div_assoc, Finset.sum_div]

/-- The rational clipping expression `max (-T) (min T x)`, which clamps to the interval from
`-T` to `T` when `T` is nonnegative. -/
def rationalClip (T x : ℚ) : ℚ := max (-T) (min T x)

/-- Casting rational clipping to the reals agrees with `boundedClip` at the cast threshold and
input. -/
lemma rationalClip_cast (T x : ℚ) :
    (rationalClip T x : ℝ) = Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip T x := by
  simp only [rationalClip, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip, Rat.cast_max,
      Rat.cast_neg, Rat.cast_min]

/-- The unweighted sum of the absolute `k`th powers of a finite rational-valued function. -/
def publicMoment {I : Type} [Fintype I] (f : I → ℚ) (k : ℕ) : ℚ :=
  ∑ i, |f i|^k

/-- Under any finite probability distribution, the absolute `k`th moment of a rational-valued
function is bounded by its unweighted `publicMoment`. -/
lemma publicMoment_bound {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℚ) (k : ℕ) :
    p.expect (fun i => |(f i : ℝ)|^k) ≤ (publicMoment f k : ℝ) := by
  have hp (i : I) : p.prob i ≤ 1 := by
    calc
      p.prob i ≤ ∑ j, p.prob j := Finset.single_le_sum (fun j _ => p.nonneg j) (Finset.mem_univ i)
      _ = 1 := p.sum_one
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect publicMoment
  push_cast
  exact Finset.sum_le_sum fun i _ => mul_le_of_le_one_left (by positivity) (hp i)

/-- The clipping bias of a rational-valued function is bounded by its public second moment
divided by four times the positive threshold. -/
lemma publicMoment_clipping2 {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℚ) (T : ℚ) (hT : 0<T) :
    |p.expect (fun i => (f i : ℝ)) - p.expect (fun i => (rationalClip T (f i) : ℝ))| ≤
      (publicMoment f 2 : ℝ)/(4*T) := by
  have hTr : (0:ℝ)<T := by exact_mod_cast hT
  simp only [rationalClip_cast]
  exact (finite_clipping_bias p (fun i => (f i : ℝ)) T hTr).trans
    (div_le_div_of_nonneg_right (by simpa only [sq_abs] using! publicMoment_bound p f 2) (by positivity))

/-- The clipping bias of a rational-valued function is bounded by its public fourth moment
divided by the cube of the positive threshold. -/
lemma publicMoment_clipping4 {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℚ) (T : ℚ) (hT : 0<T) :
    |p.expect (fun i => (f i : ℝ)) - p.expect (fun i => (rationalClip T (f i) : ℝ))| ≤
      (publicMoment f 4 : ℝ)/((T:ℝ)^3) := by
  have hTr : (0:ℝ)<T := by exact_mod_cast hT
  simp only [rationalClip_cast]
  exact (finite_clipping_bias4 p (fun i => (f i : ℝ)) T hTr).trans
    (div_le_div_of_nonneg_right (by simpa only [show (4:ℕ)=2*2 by rfl, pow_mul, sq_abs] using! publicMoment_bound p f 4) (by positivity))

/-- At a nonnegative threshold, the absolute value of a rational clipped value is at most the
threshold. -/
lemma rationalClip_bound (T x : ℚ) (hT : 0 ≤ T) : |rationalClip T x| ≤ T := by
  have h :=
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip_bound (T:ℝ) (x:ℝ)
      (by exact_mod_cast hT)
  rw [← rationalClip_cast] at h
  exact_mod_cast h

/-- The choice between second-moment and fourth-moment clipping-bias bounds. -/
inductive TailClass where
  | second
  | fourth
  deriving DecidableEq

/-- The rational clipping-bias bound selected from the public second or fourth moment by
`TailClass`. -/
def tailBias {I : Type} [Fintype I] (c : TailClass) (f : I → ℚ) (T : ℚ) : ℚ :=
  match c with
  | .second => publicMoment f 2 / (4*T)
  | .fourth => publicMoment f 4 / T^3

/-- For a positive threshold, `tailBias` bounds the change in expectation caused by rational
clipping under any finite distribution. -/
theorem tailBias_valid {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (c : TailClass) (f : I → ℚ) (T : ℚ) (hT : 0 < T) :
    |p.expect (fun i => (f i : ℝ)) - p.expect (fun i => (rationalClip T (f i) : ℝ))| ≤
      (tailBias c f T : ℝ) := by
  cases c
  · simpa [tailBias] using! publicMoment_clipping2 p f T hT
  · simpa [tailBias] using! publicMoment_clipping4 p f T hT

/-- A rational clipping threshold at least one, computed from the selected public moment and the
requested bias parameter. -/
def radius {I : Type} [Fintype I] (c : TailClass) (f : I → ℚ) (η : ℚ) : ℚ :=
  max 1 (match c with
    | .second => publicMoment f 2 / (4*η)
    | .fourth => publicMoment f 4 / η)

/-- The computed clipping radius is strictly positive for every moment class, function, and bias
parameter. -/
theorem radius_pos {I : Type} [Fintype I] (c : TailClass) (f : I → ℚ) (η : ℚ) :
    0 < radius c f η := lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (le_max_left _ _)

/-- For a positive requested bias, the computed clipping radius makes `tailBias` at most that
bias. -/
theorem radius_bias {I : Type} [Fintype I] (c : TailClass) (f : I → ℚ) (η : ℚ) (hη : 0 < η) :
    tailBias c f (radius c f η) ≤ η := by
  have ht := radius_pos c f η
  have h₁ : 1 ≤ radius c f η := le_max_left _ _
  cases c with
  | second =>
    have hm : publicMoment f 2 / (4*η) ≤ radius .second f η := le_max_right _ _
    have hx := (div_le_iff₀ (by positivity : (0 : ℚ) < 4*η)).mp hm
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4*radius .second f η)).mpr
    nlinarith
  | fourth =>
    have hm : publicMoment f 4 / η ≤ radius .fourth f η := le_max_right _ _
    have hx := (div_le_iff₀ hη).mp hm
    have hsq : 1 ≤ (radius .fourth f η)^2 := by nlinarith
    have hcube : radius .fourth f η ≤ (radius .fourth f η)^3 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq ht.le]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < (radius .fourth f η)^3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcube hη.le]

/-- Under the stated positivity assumptions and pilot parameter bound, the probability that the
clipped pilot readout error exceeds `eps + tailBias c f T` is at most `δpilot + δmain`. -/
theorem frontier1 {I : Type} [Fintype I] [DecidableEq I] (p : FinDist I)
    (c : TailClass) (f : I → ℚ) (T : ℚ) (depth j : ℕ) (nu eps δpilot δmain : ℚ)
    (hT : 0 < T) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (hp : 0 < δpilot) (hm : 0 < δmain) :
    eventMass (mainLaw p (pilotCount δpilot nu j) depth
      (normalized T (fun i => rationalClip T (f i))) nu (eps/T) δmain)
      (fun z => ((eps + tailBias c f T : ℚ) : ℝ) <
        |(boundedReadout T _ depth (fun i => rationalClip T (f i)) nu eps δmain z : ℝ) -
          p.expect (fun i => (f i : ℝ))|) ≤ (δpilot : ℝ) + δmain := by
  apply (eventMass_mono _ _ _ ?_).trans
    (Qatlib.Concepts.UnbiasedBases.ThreeBasis.CertifiedPilotCore.frontier1 p T depth j (fun i => rationalClip T (f i)) nu eps δpilot δmain
      hT (fun i => rationalClip_bound T (f i) hT.le) hnu hnu1 heps hp hm)
  intro z hz
  have hb := tailBias_valid p c f T hT
  have ht := abs_sub_le ((boundedReadout T _ depth (fun i => rationalClip T (f i)) nu eps δmain z : ℝ))
    (p.expect (fun i => (rationalClip T (f i) : ℝ))) (p.expect (fun i => (f i : ℝ)))
  rw [abs_sub_comm (p.expect (fun i => (rationalClip T (f i) : ℝ)))
    (p.expect (fun i => (f i : ℝ)))] at ht
  push_cast at hz
  linarith

/-- The finite table cardinality plus the estimator resource count for a clipped and normalized
observable on the given main record. -/
def tableResources {I : Type} [Fintype I] [DecidableEq I] (T : ℚ) (N depth : ℕ)
    (f : I → ℚ) (nu eps δ : ℚ)
    (z : MainRecord N depth (normalized T (fun i => rationalClip T (f i))) nu (eps/T) δ) : ℕ :=
  Fintype.card I + resources N depth (normalized T (fun i => rationalClip T (f i))) nu (eps/T) δ z

/-- Under the stated parameter bounds, the table resource count is at most the table cardinality
plus `N + sampleCount 4 (eps/T) δ`. -/
theorem table_worst {I : Type} [Fintype I] [DecidableEq I] (T : ℚ) (N depth : ℕ)
    (f : I → ℚ) (nu eps δ : ℚ)
    (z : MainRecord N depth (normalized T (fun i => rationalClip T (f i))) nu (eps/T) δ)
    (hT : 0 < T) (hN : 0 < N) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (hδ : 0 < δ) :
    tableResources T N depth f nu eps δ z ≤ Fintype.card I + (N + sampleCount 4 (eps/T) δ) := by
  exact Nat.add_le_add_left (worst_resources N depth _ nu (eps/T) δ z hN
    (normalized_bound T _ hT (fun i => rationalClip_bound T (f i) hT.le)) hnu hnu1
    (div_pos heps hT) hδ) _

/-- With the computed clipping radius and the stated parameter bounds, the probability that the
pilot readout error exceeds `eps + η` is at most `δpilot + δmain`. -/
theorem computed_radius_frontier {I : Type} [Fintype I] [DecidableEq I] (p : FinDist I)
    (c : TailClass) (f : I → ℚ) (η : ℚ) (depth j : ℕ) (nu eps δpilot δmain : ℚ)
    (hη : 0 < η) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (hp : 0 < δpilot) (hm : 0 < δmain) :
    let T := radius c f η
    eventMass (mainLaw p (pilotCount δpilot nu j) depth
      (normalized T (fun i => rationalClip T (f i))) nu (eps/T) δmain)
      (fun z => ((eps + η : ℚ) : ℝ) <
        |(boundedReadout T _ depth (fun i => rationalClip T (f i)) nu eps δmain z : ℝ) -
          p.expect (fun i => (f i : ℝ))|) ≤ (δpilot : ℝ) + δmain := by
  (try dsimp only)
  apply (eventMass_mono _ _ _ ?_).trans
    (frontier1 p c f (radius c f η) depth j nu eps δpilot δmain
      (radius_pos c f η) hnu hnu1 heps hp hm)
  intro z hz
  have hb : (tailBias c f (radius c f η) : ℝ) ≤ η := by exact_mod_cast radius_bias c f η hη
  push_cast at hz ⊢
  linarith

end Qatlib.Concepts.MbqcFlow.FlowDecision.CertifiedPilotCore
