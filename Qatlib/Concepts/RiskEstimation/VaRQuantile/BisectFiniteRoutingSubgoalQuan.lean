/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalStat

/-!
# Failure bounds for finite quantile bisection

This module proves the finite routing specification `BisectFiniteRoutingSubgoal` for
`riskBisect`. Conditional failure estimates accumulate over the bisection depth, while every
supported output records at most the supplied fuel in its call counter. This supports the
quantile search used in [WoernerEgger2019].

## Main statements

* `risk_bind_failure`: bound a composed failure probability using a bad intermediate event.
* `risk_route_failure`: propagate per-call error bounds through a finite search interval.
* `riskBisectFiniteRouting`: establish the quantile bracketing and call-count guarantees.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open scoped Classical BigOperators ENNReal
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The probability of an event under a bound PMF equals the expectation of its conditional
probability. -/
theorem risk_event_bind {X Y : Type} (p : PMF X) (f : X → PMF Y) (E : Y → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (p.bind f) E = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (f x) E) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]

/-- If the conditional probability of `E` is at most `a` outside `B`, its probability after
binding is at most the probability of `B` plus `a`. -/
theorem risk_bind_failure {X Y : Type} (p : PMF X) (f : X → PMF Y) (B : X → Prop)
    (E : Y → Prop) (a : ℝ≥0∞) (hgood : ∀ x, ¬B x → Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (f x) E ≤ a) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (p.bind f) E ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p B + a := by
  classical
  rw [risk_event_bind]
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x => (if B x then 1 else 0) + a) := by
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall
      intro x
      by_cases hx : B x
      · rw [if_pos hx]; exact
          (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _).trans
          (le_add_right le_rfl)
      · rw [if_neg hx, zero_add]; exact hgood x hx
    _ = _ := by rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]; rfl

/-- An event that fails at every point in the support of a PMF has probability zero. -/
theorem risk_event_zero_support {X : Type} (p : PMF X) (E : X → Prop)
    (h : ∀ x ∈ p.support, ¬E x) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E = 0 := by
  classical
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · simp only [if_neg (h x ((PMF.mem_support_iff p x).mpr hx)), mul_zero]

/-- Every supported output of `riskBisect` has a call counter at most the supplied fuel. -/
theorem riskBisect_support_calls (sample : ℚ → PMF ℝ) (xs : List ℚ) (q : ℝ)
    (fuel lo hi : ℕ) : ∀ z ∈ (riskBisect sample xs q fuel lo hi).support, z.2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => intro z hz; have hh := (PMF.mem_support_pure_iff _ _).mp hz; subst z; simp
  | succ fuel ih =>
    intro z hz
    dsimp only [riskBisect] at hz
    split_ifs at hz with hstop
    · have hh := (PMF.mem_support_pure_iff _ _).mp hz; subst z; simp
    · obtain ⟨x, _, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
      obtain ⟨w, hw, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      subst z
      split_ifs at hw with hx
      · have hh := ih lo ((lo+hi)/2) w hw; (try dsimp only); omega
      · have hh := ih ((lo+hi)/2+1) hi w hw; (try dsimp only); omega

/-- The event that the output index is out of range or violates either approximate
quantile-bracketing inequality for `F`. -/
private def riskBadIndex (xs : List ℚ) (q eps : ℝ) (F : ℚ → ℝ) (z : ℕ × ℕ) : Prop :=
  z.1 ≥ xs.length ∨ F (xs.getD z.1 0) < q-eps ∨ (z.1 ≠ 0 ∧ q+eps < F (xs.getD (z.1-1) 0))

/-- A collapsed interval satisfying the endpoint bracket conditions returns an index outside
`riskBadIndex`. -/
private theorem riskBadIndex_pure (xs : List ℚ) (q eps : ℝ) (F : ℚ → ℝ) (lo hi : ℕ)
    (hhi : hi < xs.length) (hu : q-eps ≤ F (xs.getD hi 0))
    (hl : lo ≠ 0 → F (xs.getD (lo-1) 0) ≤ q+eps) (heq : lo = hi) : ¬riskBadIndex xs q eps F (lo,0) := by
  dsimp only [riskBadIndex]
  intro hb
  rcases hb with hb | hb | ⟨hlo, hb⟩
  · omega
  · rw [← heq] at hu; linarith
  · have hh := hl hlo; linarith

/-- For an in-range interval of width less than `2^fuel` satisfying the endpoint bracket
conditions, the bad-index probability is at most `fuel` times the per-sample failure bound. -/
private theorem risk_route_failure (sample : ℚ → PMF ℝ) (xs : List ℚ) (q eps delta : ℝ)
    (F : ℚ → ℝ) (_heps : 0 ≤ eps) (_hdelta : 0 ≤ delta)
    (hsample : ∀ t, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sample t) (fun z => eps < |z-F t|) ≤ ENNReal.ofReal delta)
    (fuel lo hi : ℕ) (hlh : lo ≤ hi) (hhi : hi < xs.length) (hwidth : hi-lo < 2^fuel)
    (hu : q-eps ≤ F (xs.getD hi 0))
    (hl : lo ≠ 0 → F (xs.getD (lo-1) 0) ≤ q+eps) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskBisect sample xs q fuel lo hi) (riskBadIndex xs q eps F) ≤
      (fuel : ℝ≥0∞)*ENNReal.ofReal delta := by
  classical
  induction fuel generalizing lo hi with
  | zero =>
    have hh : lo = hi := by norm_num at hwidth; omega
    simp only [riskBisect, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, if_neg
        (riskBadIndex_pure xs q eps F lo hi hhi hu hl hh), Nat.cast_zero, zero_mul, le_refl]
  | succ fuel ih =>
    rw [riskBisect]
    split_ifs with hstop
    · have hh : lo = hi := by omega
      simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, if_neg
          (riskBadIndex_pure xs q eps F lo hi hhi hu hl hh), zero_le]
    · let mid := (lo+hi)/2
      have hmidlo : lo ≤ mid := by dsimp [mid]; omega
      have hmidhi : mid < hi := by dsimp [mid]; omega
      have hwL : mid-lo < 2^fuel := by rw [pow_succ] at hwidth; dsimp [mid]; omega
      have hwR : hi-(mid+1) < 2^fuel := by rw [pow_succ] at hwidth; dsimp [mid]; omega
      have hcont : ∀ z : ℝ, ¬eps < |z-F (xs.getD mid 0)| →
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event ((if q ≤ z then riskBisect sample xs q fuel lo mid
            else riskBisect sample xs q fuel (mid+1) hi).map (fun out => (out.1,out.2+1)))
            (riskBadIndex xs q eps F) ≤ (fuel : ℝ≥0∞)*ENNReal.ofReal delta := by
        intro z hz
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
        change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (if q ≤ z then riskBisect sample xs q fuel lo mid
            else riskBisect sample xs q fuel (mid+1) hi) (riskBadIndex xs q eps F) ≤ _
        have hgood := abs_le.mp (le_of_not_gt hz)
        split_ifs with hzq
        · exact ih lo mid hmidlo (by omega) hwL (by linarith) hl
        · apply ih (mid+1) hi (by omega) hhi hwR hu
          intro _
          simp only [Nat.add_sub_cancel]
          have hzq' : z < q := lt_of_not_ge hzq
          linarith
      have hh := risk_bind_failure (sample (xs.getD mid 0))
        (fun z => (if q ≤ z then riskBisect sample xs q fuel lo mid else riskBisect sample xs q fuel (mid+1) hi).map
          (fun out => (out.1,out.2+1)))
        (fun z => eps < |z-F (xs.getD mid 0)|) (riskBadIndex xs q eps F)
        ((fuel : ℝ≥0∞)*ENNReal.ofReal delta) hcont
      calc
        _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sample (xs.getD mid 0)) (fun z => eps < |z-F (xs.getD mid 0)|) +
          (fuel : ℝ≥0∞)*ENNReal.ofReal delta := hh
        _ ≤ ENNReal.ofReal delta+(fuel : ℝ≥0∞)*ENNReal.ofReal delta := add_le_add (hsample _) le_rfl
        _ = _ := by rw [Nat.cast_succ, add_mul, one_mul, add_comm]

/-- Finite bisection satisfies the approximate quantile-bracketing failure bound and the depth
bound on its call counter. -/
theorem riskBisectFiniteRouting : BisectFiniteRoutingSubgoal := by
  intro sample xs q eps delta F hxs _hqsorted hq0 hq1 heps hdelta _hF hlast hsample
  (try dsimp only)
  have hlen : 0 < xs.length := List.length_pos_of_ne_nil hxs
  have hlast' : F (xs.getD (xs.length-1) 0) = 1 := by
    have hh : xs.getD (xs.length-1) 0 = xs.getLastD 0 := by
      simp only [List.getD, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    rw [hh]
    exact hlast
  have hd : xs.length-1 < 2^(Nat.clog 2 xs.length+1) := by
    have hh := Nat.le_pow_clog (by norm_num : 1 < 2) xs.length
    rw [pow_succ]; omega
  refine ⟨?_, ?_⟩
  · have hh := risk_route_failure sample xs q eps delta F heps hdelta hsample
      (Nat.clog 2 xs.length+1) 0 (xs.length-1) (by omega) (by omega) (by simpa using! hd)
      (by rw [hlast']; linarith) (by simp)
    simpa only [riskBadIndex,
        ENNReal.ofReal_mul
        (by positivity : (0:ℝ) ≤ ↑(Nat.clog 2 xs.length+1)), ENNReal.ofReal_natCast] using! hh
  · apply risk_event_zero_support
    intro z hz
    exact not_lt_of_ge (riskBisect_support_calls sample xs q _ _ _ z hz)
end Qatlib.Concepts.RiskEstimation.VaRQuantile
