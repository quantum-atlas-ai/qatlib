/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.StatisticalConfidenceDefs

/-!
# Pilot and median-of-means confidence bounds

This module proves unbiasedness of the pilot variance quantity and bounds pilot failure using a
fourth moment. It combines this with a median-of-means bound for the main phase and a union
bound to verify `ConfidenceBudget` record and failure accounting. See [Montanaro2015] for the
quantum Monte Carlo context.

## Main statements

* `pilot_failure_le`: bounds pilot failure by a fourth moment.
* `main_failure_le`: bounds median-of-means failure.
* `confidence_budget`: combines phase failure and record budgets.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel

set_option autoImplicit false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open scoped Classical BigOperators ComplexOrder

variable {X : Type} [Fintype X]

/-- A finite sum over a predicate equals the unrestricted sum weighted by its real-valued
indicator. -/
private theorem sum_filter_eq_indicator {ι : Type} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (f : ι → ℝ) :
    (∑ ω ∈ Finset.univ.filter p, f ω)
      = ∑ ω : ι, f ω * (if p ω then (1 : ℝ) else 0) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : p ω
  · rw [if_pos h]
    rw [if_pos h]
    ring
  · rw [if_neg h]
    rw [if_neg h]
    ring

/-- A weighted finite sum distributes over the sum of two functions. -/
private theorem sum_split_two {ι : Type} [Fintype ι] (w : ι → ℝ) (g h : ι → ℝ) :
    (∑ x, w x * (g x + h x)) = (∑ x, w x * g x) + (∑ x, w x * h x) := by
  calc (∑ x, w x * (g x + h x))
      = ∑ x, (w x * g x + w x * h x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = (∑ x, w x * g x) + (∑ x, w x * h x) := Finset.sum_add_distrib

/-- For a positive pilot sample count, the expectation of `pilotVariance` equals the variance of
`f` under `q`. -/
theorem pilotVariance_unbiased (q : FinDist X) (f : X → ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ ω : Fin n → X, q.probOf ω * pilotVariance q f ω = q.variance f := by
  have h := q.expect_avg (centeredSq q f) hn
  show (∑ ω : Fin n → X, q.probOf ω * FinDist.avg (centeredSq q f) ω) = q.variance f
  rw [h]
  show (∑ x, q.prob x * (f x - q.expect f) ^ 2) = (∑ x, q.prob x * (f x - FinDist.expect q f) ^ 2)
  rfl

/-- The variance of a real-valued function under a finite distribution is at most its second
moment. -/
private theorem variance_le_secondMoment (q : FinDist X) (g : X → ℝ) :
    q.variance g ≤ q.expect (fun x => g x ^ 2) := by
  set E : ℝ := q.expect g with hE
  have hEg : E = ∑ x : X, q.prob x * g x := by
    show q.expect g = ∑ x : X, q.prob x * g x
    rfl
  have hsq : (∑ x : X, q.prob x * (g x - E) ^ 2)
      = (∑ x : X, q.prob x * g x ^ 2) - E ^ 2 := by
    calc (∑ x : X, q.prob x * (g x - E) ^ 2)
        = ∑ x : X, ((q.prob x * g x ^ 2 - 2 * E * (q.prob x * g x)) + E ^ 2 * q.prob x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
      _ = (∑ x : X, (q.prob x * g x ^ 2 - 2 * E * (q.prob x * g x))) + (∑ x : X, E ^ 2 * q.prob x) := by
            rw [Finset.sum_add_distrib]
      _ = ((∑ x : X, q.prob x * g x ^ 2) - (∑ x : X, 2 * E * (q.prob x * g x)))
            + (∑ x : X, E ^ 2 * q.prob x) := by
            rw [Finset.sum_sub_distrib]
      _ = ((∑ x : X, q.prob x * g x ^ 2) - 2 * E * (∑ x : X, q.prob x * g x))
            + E ^ 2 * (∑ x : X, q.prob x) := by
            congr 1
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
      _ = ((∑ x : X, q.prob x * g x ^ 2) - 2 * E * E) + E ^ 2 * 1 := by
            rw [hEg, q.sum_one]
      _ = (∑ x : X, q.prob x * g x ^ 2) - E ^ 2 := by ring
  have hvar : q.variance g = ∑ x : X, q.prob x * (g x - E) ^ 2 := by
    show (∑ x : X, q.prob x * (g x - q.expect g) ^ 2) = ∑ x : X, q.prob x * (g x - E) ^ 2
    rfl
  have hsecond : q.expect (fun x => g x ^ 2) = ∑ x : X, q.prob x * g x ^ 2 := by
    show (∑ x : X, q.prob x * (fun x => g x ^ 2) x) = ∑ x : X, q.prob x * g x ^ 2
    rfl
  rw [hvar, hsq, hsecond]
  have hsq' : 0 ≤ E ^ 2 := sq_nonneg _
  linarith

/-- The probability of the pilot failure event, expressed as an indicator-weighted sum over
independent pilot samples. -/
noncomputable def pilotFailureMass (q : FinDist X) (f : X → ℝ) {n : ℕ} (tol : ℝ) : ℝ :=
  ∑ ω : Fin n → X, q.probOf ω * (if pilotBad q f tol ω then (1 : ℝ) else 0)

/-- For a positive pilot sample count and tolerance, the pilot failure probability is at most
`pilotFourthMoment q f / (n * tol²)`. -/
theorem pilot_failure_le (q : FinDist X) (f : X → ℝ) {n : ℕ} (hn : 0 < n)
    (tol : ℝ) (htol : 0 < tol) :
    pilotFailureMass q f (n := n) tol ≤ pilotFourthMoment q f / ((n : ℝ) * tol ^ 2) := by
  have hvar : q.expect (centeredSq q f) = q.variance f := by
    show (∑ x, q.prob x * (f x - q.expect f) ^ 2) = (∑ x, q.prob x * (f x - FinDist.expect q f) ^ 2)
    rfl
  have hvar2 : q.variance (centeredSq q f) ≤ pilotFourthMoment q f := by
    show q.variance (centeredSq q f) ≤ q.expect (fun x => (centeredSq q f x) ^ 2)
    exact variance_le_secondMoment q (centeredSq q f)
  have hcheb : q.probEvent (L := n) (fun ω : Fin n → X => pilotBad q f tol ω)
      ≤ q.variance (centeredSq q f) / ((n : ℝ) * tol ^ 2) := by
    have h := q.chebyshev_avg (centeredSq q f) hn tol htol
    show q.probEvent (L := n)
      (fun ω : Fin n → X => tol < |FinDist.avg (centeredSq q f) ω
        - q.expect (centeredSq q f)|)
      ≤ q.variance (centeredSq q f) / ((n : ℝ) * tol ^ 2)
    exact h
  have hprob : q.probEvent (L := n) (fun ω : Fin n → X => pilotBad q f tol ω)
      = pilotFailureMass q f (n := n) tol := by
    unfold FinDist.probEvent pilotFailureMass
    rw [sum_filter_eq_indicator]
  rw [hprob] at hcheb
  exact hcheb.trans (div_le_div_of_nonneg_right hvar2 (by positivity))

/-- The pilot failure probability is at most `δ` whenever the fourth-moment sample-size bound is
at most `δ`. -/
theorem pilot_size_sufficient (q : FinDist X) (f : X → ℝ) {n : ℕ} (hn : 0 < n)
    (tol : ℝ) (htol : 0 < tol) (δ : ℝ) (hδ : 0 < δ)
    (hn_size : pilotFourthMoment q f / ((n : ℝ) * tol ^ 2) ≤ δ) :
    pilotFailureMass q f (n := n) tol ≤ δ :=
  (pilot_failure_le q f hn tol htol).trans hn_size

/-- The probability of the main-phase failure event under the product distribution of its
independent sample blocks. -/
noncomputable def mainFailureMass (q : FinDist X) (f : X → ℝ) {M L : ℕ} (ε : ℝ) : ℝ :=
  ∑ ω : MainPhase M L X, (∏ m, q.probOf (ω m)) * (if mainBad q f ε ω then (1 : ℝ) else 0)

/-- For positive block size, block count, and error tolerance, the median-of-means failure
probability is at most `3 ^ (M / 2) / 2 ^ M` under the stated variance bound. -/
theorem main_failure_le (q : FinDist X) (f : X → ℝ) {M L : ℕ} (hL : 0 < L)
    (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (hvar : 4 * q.variance f ≤ (L : ℝ) * ε ^ 2) :
    mainFailureMass q f (M := M) (L := L) ε ≤ 3 ^ (M / 2) / 2 ^ M := by
  have hconc : (∑ ω ∈ Finset.univ.filter (fun ω : MainPhase M L X => mainBad q f ε ω),
      ∏ m, q.probOf (ω m)) ≤ 3 ^ (M / 2) / 2 ^ M := by
    show (∑ ω ∈ Finset.univ.filter
      (fun ω : MainPhase M L X => mainBad q f ε ω),
      ∏ m, q.probOf (ω m)) ≤ 3 ^ (M / 2) / 2 ^ M
    exact q.median_of_means_concentration f hL hM ε hε hvar
  have hprob : mainFailureMass q f (M := M) (L := L) ε
      = (∑ ω ∈ Finset.univ.filter (fun ω : MainPhase M L X => mainBad q f ε ω),
          ∏ m, q.probOf (ω m)) := by
    unfold mainFailureMass
    rw [sum_filter_eq_indicator]
  rw [hprob]
  exact hconc

/-- The real-valued indicator of a disjunction is at most the sum of the two indicators. -/
private theorem indicator_or_le (p q : Prop) [Decidable p] [Decidable q] :
    ((if p ∨ q then (1 : ℝ) else 0))
      ≤ ((if p then (1 : ℝ) else 0)) + ((if q then (1 : ℝ) else 0)) := by
  by_cases hp : p
  · by_cases hq : q
    · rw [if_pos (Or.inl hp), if_pos hp, if_pos hq]
      norm_num
    · rw [if_pos (Or.inl hp), if_pos hp, if_neg hq]
      norm_num
  · by_cases hq : q
    · rw [if_pos (Or.inr hq), if_neg hp, if_pos hq]
      norm_num
    · have hnq : ¬(p ∨ q) := fun h => h.elim (fun hp' => hp hp') (fun hq' => hq hq')
      rw [if_neg hnq, if_neg hp, if_neg hq]
      norm_num

/-- The probability of a pilot or main-phase failure is at most the sum of their individual
failure probabilities. -/
theorem merged_failure_le (q : FinDist X) (f : X → ℝ) {n M L : ℕ} (tol ε : ℝ) :
    mergedFailureMass q f (n := n) (M := M) (L := L) tol ε
      ≤ pilotFailureMass q f (n := n) tol + mainFailureMass q f (M := M) (L := L) ε := by
  have hsplit : ∀ (w : (Fin n → X) × MainPhase M L X),
      ((if pilotBad q f tol w.1 ∨ mainBad q f ε w.2 then (1 : ℝ) else 0))
        ≤ ((if pilotBad q f tol w.1 then (1 : ℝ) else 0))
          + ((if mainBad q f ε w.2 then (1 : ℝ) else 0)) :=
    fun w => indicator_or_le _ _
  have hjoint : ∀ (w : (Fin n → X) × MainPhase M L X),
      (jointPilotMainLaw q n M L).prob w = (q.probOf w.1) * (∏ m, q.probOf (w.2 m)) := by
    intro w
    rfl
  have hpilot : (∑ w : (Fin n → X) × MainPhase M L X,
      ((q.probOf w.1) * (∏ m, q.probOf (w.2 m)) *
        (if pilotBad q f tol w.1 then (1 : ℝ) else 0) : ℝ))
      = (∑ x : Fin n → X, q.probOf x *
          (if pilotBad q f tol x then (1 : ℝ) else 0)) *
        (∑ y : MainPhase M L X, ∏ m, q.probOf (y m)) := by
    calc (∑ w : (Fin n → X) × MainPhase M L X,
          ((q.probOf w.1) * (∏ m, q.probOf (w.2 m)) *
            (if pilotBad q f tol w.1 then (1 : ℝ) else 0) : ℝ))
        = ∑ x : Fin n → X, ∑ y : MainPhase M L X,
            ((q.probOf x * (∏ m, q.probOf (y m)) *
              (if pilotBad q f tol x then (1 : ℝ) else 0) : ℝ)) :=
          Fintype.sum_prod_type _
      _ = ∑ x : Fin n → X, (q.probOf x *
            (if pilotBad q f tol x then (1 : ℝ) else 0)) *
            (∑ y : MainPhase M L X, ∏ m, q.probOf (y m)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = (∑ x : Fin n → X, q.probOf x *
            (if pilotBad q f tol x then (1 : ℝ) else 0)) *
            (∑ y : MainPhase M L X, ∏ m, q.probOf (y m)) := by
          rw [← Finset.sum_mul]
  have hmain : (∑ w : (Fin n → X) × MainPhase M L X,
      ((q.probOf w.1) * (∏ m, q.probOf (w.2 m)) *
        (if mainBad q f ε w.2 then (1 : ℝ) else 0) : ℝ))
      = (∑ x : Fin n → X, q.probOf x) *
          (∑ y : MainPhase M L X, (∏ m, q.probOf (y m)) *
            (if mainBad q f ε y then (1 : ℝ) else 0)) := by
    calc (∑ w : (Fin n → X) × MainPhase M L X,
          ((q.probOf w.1) * (∏ m, q.probOf (w.2 m)) *
            (if mainBad q f ε w.2 then (1 : ℝ) else 0) : ℝ))
        = ∑ x : Fin n → X, ∑ y : MainPhase M L X,
            ((q.probOf x * (∏ m, q.probOf (y m)) *
              (if mainBad q f ε y then (1 : ℝ) else 0) : ℝ)) :=
          Fintype.sum_prod_type _
      _ = ∑ x : Fin n → X, q.probOf x *
            (∑ y : MainPhase M L X, (∏ m, q.probOf (y m)) *
              (if mainBad q f ε y then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = (∑ x : Fin n → X, q.probOf x) *
            (∑ y : MainPhase M L X, (∏ m, q.probOf (y m)) *
              (if mainBad q f ε y then (1 : ℝ) else 0)) := by
          rw [← Finset.sum_mul]
  have h1 : (∑ x : Fin n → X, q.probOf x *
        (if pilotBad q f tol x then (1 : ℝ) else 0))
      = pilotFailureMass q f (n := n) tol := rfl
  have h2 : (∑ y : MainPhase M L X, (∏ m, q.probOf (y m)) *
        (if mainBad q f ε y then (1 : ℝ) else 0))
      = mainFailureMass q f (M := M) (L := L) ε := rfl
  calc mergedFailureMass q f (n := n) (M := M) (L := L) tol ε
      = ∑ w : (Fin n → X) × MainPhase M L X,
          ((q.probOf w.1) * (∏ m, q.probOf (w.2 m))) *
            (if pilotBad q f tol w.1 ∨ mainBad q f ε w.2 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hjoint]
      _ ≤ ∑ w : (Fin n → X) × MainPhase M L X,
          ((q.probOf w.1) * (∏ m, q.probOf (w.2 m))) *
            ((if pilotBad q f tol w.1 then (1 : ℝ) else 0)
              + (if mainBad q f ε w.2 then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun w _ => ?_
        have hnonneg : 0 ≤ q.probOf w.1 * (∏ m, q.probOf (w.2 m)) := by
          have h1' : 0 ≤ q.probOf w.1 :=
            Finset.prod_nonneg fun i _ => q.nonneg _
          have h2' : 0 ≤ (∏ m, q.probOf (w.2 m)) :=
            Finset.prod_nonneg fun m _ => Finset.prod_nonneg fun i _ => q.nonneg _
          exact mul_nonneg h1' h2'
        exact mul_le_mul_of_nonneg_left (hsplit w) hnonneg
      _ = (∑ x : Fin n → X, q.probOf x *
            (if pilotBad q f tol x then (1 : ℝ) else 0)) *
            (∑ y : MainPhase M L X, ∏ m, q.probOf (y m))
        + (∑ x : Fin n → X, q.probOf x) *
            (∑ y : MainPhase M L X, (∏ m, q.probOf (y m)) *
              (if mainBad q f ε y then (1 : ℝ) else 0)) := by
        rw [sum_split_two
          (fun w : (Fin n → X) × MainPhase M L X => q.probOf w.1 * (∏ m, q.probOf (w.2 m)))
          (fun w : (Fin n → X) × MainPhase M L X => if pilotBad q f tol w.1 then (1 : ℝ) else 0)
          (fun w : (Fin n → X) × MainPhase M L X => if mainBad q f ε w.2 then (1 : ℝ) else 0)]
        rw [hpilot, hmain]
      _ = pilotFailureMass q f (n := n) tol + mainFailureMass q f (M := M) (L := L) ε := by
        rw [h1, h2, sum_mainBlockMass q M L, q.sum_probOf n]
        ring

/-- Under the stated phase failure bounds and positive sample counts, the merged failure mass is
within the total failure budget, the record count is additive, and the total count exceeds
the pilot count. -/
theorem confidence_budget (q : FinDist X) (f : X → ℝ) (b : ConfidenceBudget)
    (tol : ℝ) (htol : 0 < tol)
    (hpos : 0 < b.pilotRecords ∧ 0 < b.blockSize ∧ 0 < b.blockCount)
    (hvar : 4 * q.variance f ≤ (b.blockSize : ℝ) * b.epsilon ^ 2)
    (hpilot : pilotFailureMass q f (n := b.pilotRecords) tol ≤ b.pilotFailure)
    (hmain : mainFailureMass q f (M := b.blockCount) (L := b.blockSize) b.epsilon
      ≤ b.mainFailure) :
    mergedFailureMass q f (n := b.pilotRecords) (M := b.blockCount) (L := b.blockSize)
        tol b.epsilon ≤ b.totalFailure ∧
      b.totalRecords = b.pilotRecords + b.blockSize * b.blockCount ∧
      b.pilotRecords < b.totalRecords := by
  have hmerged := merged_failure_le q f (n := b.pilotRecords)
    (M := b.blockCount) (L := b.blockSize) tol b.epsilon
  refine ⟨hmerged.trans (add_le_add hpilot hmain), rfl, ?_⟩
  show b.pilotRecords < b.pilotRecords + b.blockSize * b.blockCount
  have hmul : 0 < b.blockSize * b.blockCount :=
    Nat.mul_pos hpos.2.1 hpos.2.2
  omega

/-- Collects pilot unbiasedness, the pilot fourth-moment bound, the main median-of-means bound,
the merged failure budget, and the total record identity under the stated budget hypotheses. -/
theorem clause33_complete (q : FinDist X) (f : X → ℝ) (b : ConfidenceBudget)
    (tol : ℝ) (htol : 0 < tol)
    (hpos : 0 < b.pilotRecords ∧ 0 < b.blockSize ∧ 0 < b.blockCount)
    (hvar : 4 * q.variance f ≤ (b.blockSize : ℝ) * b.epsilon ^ 2)
    (hpilot : pilotFailureMass q f (n := b.pilotRecords) tol ≤ b.pilotFailure)
    (hmain : mainFailureMass q f (M := b.blockCount) (L := b.blockSize) b.epsilon
      ≤ b.mainFailure) :
    (∀ {n : ℕ}, 0 < n →
      (∑ ω : Fin n → X, q.probOf ω * pilotVariance q f ω = q.variance f)) ∧
      (∀ {n : ℕ}, 0 < n → pilotFailureMass q f (n := n) tol ≤
        pilotFourthMoment q f / ((n : ℝ) * tol ^ 2)) ∧
      (∀ {M L : ℕ}, 0 < L → 0 < M → 0 < b.epsilon →
        4 * q.variance f ≤ (L : ℝ) * b.epsilon ^ 2 →
        mainFailureMass q f (M := M) (L := L) b.epsilon ≤ 3 ^ (M / 2) / 2 ^ M) ∧
      mergedFailureMass q f (n := b.pilotRecords) (M := b.blockCount) (L := b.blockSize)
        tol b.epsilon ≤ b.totalFailure ∧
      b.totalRecords = b.pilotRecords + b.blockSize * b.blockCount := by
  have hunbiased : ∀ {n : ℕ}, 0 < n →
      (∑ ω : Fin n → X, q.probOf ω * pilotVariance q f ω = q.variance f) := by
    intro n hn
    exact pilotVariance_unbiased q f hn
  refine ⟨hunbiased, ?_, ?_, ?_, rfl⟩
  · intro n hn
    exact pilot_failure_le q f hn tol htol
  · intro M L hL hM hε hvar'
    exact main_failure_le q f hL hM b.epsilon hε hvar'
  · exact (merged_failure_le q f (n := b.pilotRecords) (M := b.blockCount)
      (L := b.blockSize) tol b.epsilon).trans (add_le_add hpilot hmain)

end Qatlib.Concepts.MixedInstrument.ClockBridge
