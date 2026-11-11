/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstructionDefs

/-!
# Independent repetition and a longer minimum search

This module compares independent charged minimum-search runs with a single run given the same
aggregate budget. `independentRunsLaw` combines the candidate indices of repeated runs and adds
their remaining-budget coordinates; `chargedSuccessEvent` and `chargedFailureEvent` express
whether the retained candidate minimizes the table.

The comparison is expressed through exact failure probabilities and equivalent tail
inequalities. The minimum-finding setting follows [DurrHoyer1996]; the results here do not
establish an unconditional ordering between the success probabilities of repetition and a longer
run.

## Main statements

* `independent_runs_failure_exact` and `independent_runs_failure_real` identify the failure
  probability of a positive number of independent runs as a power of the one-run failure
  probability.
* `independent_runs_bounded` and `single_long_run_bounded` bound the remaining-budget
  coordinates by the aggregate charged budget.
* `amplification_domination_condition` and `amplification_domination_strict` reformulate success
  comparisons as failure-tail comparisons.
* `independent_bound_strictly_exceeds_long_bound` compares the two numerical guarantees for at
  least three repetitions.

## References

- [Dürr and Høyer, 1996][DurrHoyer1996]. *A quantum algorithm for finding the minimum*. 1996.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

open Qatlib
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
open scoped ENNReal BigOperators Classical

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The probabilities of two pointwise complementary events sum to one under any PMF. -/
theorem event_total' {α : Type*} (p : PMF α) (E E' : α → Prop)
    (h : ∀ x, E x ↔ ¬E' x) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E' = 1 := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  calc
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x => if E x then (1 : ℝ≥0∞) else 0) +
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x => if E' x then (1 : ℝ≥0∞) else 0)
        = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x =>
            (if E x then (1 : ℝ≥0∞) else 0) + (if E' x then (1 : ℝ≥0∞) else 0)) := by
          rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun _ => (1 : ℝ≥0∞)) := by
          congr 1
          funext x
          by_cases hx : E x
          · have hx' : ¬E' x := (h x).mp hx
            simp [hx, hx']
          · have hx' : E' x := not_not.mp ((h x).not.mp hx)
            simp [hx, hx']
    _ = 1 := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const p 1

/-- The probability of an event plus the probability of its complement equals one. -/
theorem event_total {α : Type*} (p : PMF α) (E : α → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬E x) = 1 :=
  event_total' p E (fun x => ¬E x) (fun x => by simp)

/-- The event that the index in a charged run's output pair is not a global minimum of `T`. The
remaining-budget coordinate does not affect this predicate. -/
def chargedFailureEvent {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) :
    Fin N × ℕ → Prop := fun x => ¬∀ j, T x.1 ≤ T j

/-- The event that the index in a charged run's output pair is a global minimum of `T`. The
remaining-budget coordinate does not affect this predicate. -/
def chargedSuccessEvent {N : ℕ} {α : Type*} [LinearOrder α] (T : Fin N → α) :
    Fin N × ℕ → Prop := fun x => ∀ j, T x.1 ≤ T j

/-- Applies `amplifiedStep` exactly `c` times to a supplied base law, combining retained
candidates and adding remaining-budget coordinates. -/
noncomputable def independentRunsLawAux {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) : (c : ℕ) → PMF (Fin N × ℕ) → PMF (Fin N × ℕ)
  | 0, base => base
  | c + 1, base => amplifiedStep T hN (independentRunsLawAux T hN c base)

/-- The law obtained from `c` independent charged-budget runs by retaining the better candidate
and adding their remaining-budget coordinates. At `c = 0`, it is the pure law at index zero
with second coordinate zero. -/
noncomputable def independentRunsLaw {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) : PMF (Fin N × ℕ) :=
  if c = 0 then PMF.pure (⟨0, hN⟩, 0)
  else independentRunsLawAux T hN (c - 1) (chargedInitialPMF T hN (chargedBudget N))

/-- The real probability that a charged initial run fails equals one minus
`chargedInitialSuccess` at the same budget. -/
theorem charged_run_failure_real {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (chargedFailureEvent T)).toReal
      = 1 - chargedInitialSuccess T budget := by
  have hsucc := chargedInitialPMF_success T hN budget
  have htot := event_total (chargedInitialPMF T hN budget) (chargedSuccessEvent T)
  have hsucc' : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (chargedSuccessEvent T) =
      ENNReal.ofReal (chargedInitialSuccess T budget) := by
    simpa [chargedSuccessEvent] using! hsucc
  have hsne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (chargedSuccessEvent T) ≠ ∞ := by
    rw [hsucc']
    simp
  have hfne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (chargedFailureEvent T) ≠ ∞ := by
    intro hc
    have h2 := htot
    rw [show (fun x : Fin N × ℕ => ¬ chargedSuccessEvent T x) = chargedFailureEvent T from rfl,
      hc] at h2
    simp at h2
  have hreal := congrArg ENNReal.toReal htot
  rw [show (fun x : Fin N × ℕ => ¬ chargedSuccessEvent T x) = chargedFailureEvent T from rfl] at hreal
  rw [ENNReal.toReal_add hsne hfne, ENNReal.toReal_one] at hreal
  have hsucc'' : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (chargedSuccessEvent T)).toReal
      = chargedInitialSuccess T budget := by
    rw [hsucc', ENNReal.toReal_ofReal (by
      exact (chargedInitialSuccess_bounds T hN budget).1)]
  linarith

/-- For `c ≥ 1`, the law of `c + 1` independent runs is one amplification step applied to the
law of `c` runs. -/
theorem independentRunsLaw_step {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (h : 1 ≤ c) :
    independentRunsLaw T hN (c + 1) = amplifiedStep T hN (independentRunsLaw T hN c) := by
  have h1 : independentRunsLaw T hN (c + 1) =
      independentRunsLawAux T hN c (chargedInitialPMF T hN (chargedBudget N)) := by
    rw [independentRunsLaw, if_neg (by omega), Nat.add_sub_cancel]
  have h2 : independentRunsLawAux T hN c (chargedInitialPMF T hN (chargedBudget N)) =
      amplifiedStep T hN
        (independentRunsLawAux T hN (c - 1) (chargedInitialPMF T hN (chargedBudget N))) := by
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    rfl
  have h3 : independentRunsLawAux T hN (c - 1) (chargedInitialPMF T hN (chargedBudget N)) =
      independentRunsLaw T hN c := by
    rw [independentRunsLaw, if_neg (by omega)]
  rw [h1, h2, h3]

/-- For a positive number `c` of independent runs, the failure-event probability is exactly the
`c`th power of the one-run charged-budget failure probability. -/
theorem independent_runs_failure_exact {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 0 < c) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (independentRunsLaw T hN c) (chargedFailureEvent T) =
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN (chargedBudget N)) (chargedFailureEvent T)) ^ c := by
  have hstep : ∀ (p : PMF (Fin N × ℕ)),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (amplifiedStep T hN p) (chargedFailureEvent T) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (chargedFailureEvent T) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN (chargedBudget N)) (chargedFailureEvent T) := by
    intro p
    have h := amplifiedStep_failure T hN p
    rwa [show (fun x : Fin N × ℕ => ¬∀ j, T x.1 ≤ T j) = chargedFailureEvent T by rfl] at h
  induction c using Nat.strong_induction_on with
  | h c ih =>
      by_cases hc1 : c = 1
      · subst hc1
        have hred : independentRunsLaw T hN 1 =
            chargedInitialPMF T hN (chargedBudget N) := by
          rw [independentRunsLaw, if_neg (by norm_num)]
          rfl
        rw [hred]
        simp
      · have hgt : 1 < c := by omega
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have hred := independentRunsLaw_step T hN c' (by omega)
        rw [hred, hstep]
        have hlow : c' < c' + 1 := by omega
        have hpos : 0 < c' := by omega
        rw [ih c' hlow hpos]
        rw [pow_succ]

/-- For positive `c`, the real failure probability of `c` independent runs equals `(1 -
chargedInitialSuccess T (chargedBudget N)) ^ c`. -/
theorem independent_runs_failure_real {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 0 < c) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (independentRunsLaw T hN c) (chargedFailureEvent T)).toReal
      = (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  have hex := independent_runs_failure_exact T hN c hc
  have hrun := charged_run_failure_real T hN (chargedBudget N)
  rw [hex, ENNReal.toReal_pow, hrun]

/-- Every supported output of `c` independent runs has remaining-budget coordinate at most `c *
chargedBudget N`. -/
theorem independent_runs_bounded {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    ∀ x ∈ (independentRunsLaw T hN c).support, x.2 ≤ c * chargedBudget N := by
  have hrun : ∀ (b : ℕ) (x : Fin N × ℕ),
      x ∈ (chargedInitialPMF T hN b).support → x.2 ≤ b := by
    intro b x hx
    rw [chargedInitialPMF] at hx
    obtain ⟨i, hi, hxy⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
    exact minimumBudgetPMFWithInit_remaining T (initCharge N) hN b i x hxy
  induction c using Nat.strong_induction_on with
  | h c ih =>
      by_cases hc0 : c = 0
      · subst hc0
        intro x hx
        rw [independentRunsLaw, if_pos (by norm_num)] at hx
        have hx' : x = (⟨0, hN⟩, 0) := (PMF.mem_support_pure_iff (⟨0, hN⟩, 0) x).mp hx
        rw [hx']
        simp
      · by_cases hc1 : c = 1
        · subst hc1
          intro x hx
          rw [independentRunsLaw, if_neg (by norm_num)] at hx
          have h1 := hrun (chargedBudget N) x hx
          omega
        · have hgt : 1 < c := by omega
          obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
          intro x hx
          have hred := independentRunsLaw_step T hN c' (by omega)
          rw [hred] at hx
          obtain ⟨p, hp, hxy⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
          obtain ⟨f, hf, hxf⟩ := (PMF.mem_support_bind_iff _ _ x).mp hxy
          have hxf' : x = (amplifiedCombine T p.1 f.1, p.2 + f.2) :=
            (PMF.mem_support_pure_iff (amplifiedCombine T p.1 f.1, p.2 + f.2) x).mp hxf
          rw [hxf']
          have h1 : p.2 ≤ c' * chargedBudget N := ih c' (by omega) p hp
          have h2 : f.2 ≤ chargedBudget N := hrun (chargedBudget N) f hf
          have h3 : p.2 + f.2 ≤ c' * chargedBudget N + chargedBudget N := Nat.add_le_add h1 h2
          have h4 : c' * chargedBudget N + chargedBudget N = (c' + 1) * chargedBudget N :=
            (Nat.succ_mul c' (chargedBudget N)).symm
          omega

/-- Every supported output of a single charged run with budget `c * chargedBudget N` has
remaining-budget coordinate at most that budget. -/
theorem single_long_run_bounded {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) :
    ∀ x ∈ (chargedInitialPMF T hN (c * chargedBudget N)).support, x.2 ≤ c * chargedBudget N := by
  intro x hx
  rw [chargedInitialPMF] at hx
  obtain ⟨i, hi, hxy⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
  exact minimumBudgetPMFWithInit_remaining T (initCharge N) hN (c * chargedBudget N) i x hxy

/-- A long run's success probability is at least the independent-repetition expression exactly
when its failure probability is at most the corresponding power of the short-run failure
probability. -/
theorem amplification_domination_condition {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (c : ℕ) :
    chargedInitialSuccess T (c * chargedBudget N) ≥
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c
      ↔ (1 - chargedInitialSuccess T (c * chargedBudget N))
          ≤ (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  constructor <;> intro h <;> linarith

/-- At one repetition, the long-run success probability satisfies the independent-repetition
comparison. -/
theorem amplification_condition_at_one {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    chargedInitialSuccess T (1 * chargedBudget N) ≥
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ 1 := by
  have hle := (chargedInitialSuccess_bounds T hN (chargedBudget N)).2
  simp only [Nat.one_mul, pow_one]
  nlinarith

/-- For every natural number `c ≥ 3`, the power `2 ^ c` strictly exceeds `2 * c`. -/
theorem two_pow_gt_two_mul_nat (c : ℕ) (hc : 3 ≤ c) : (2 : ℕ) ^ c > 2 * c := by
  induction c with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hc with h3 | hk
      · have hk2 : k = 2 := by omega
        subst hk2
        norm_num
      · have hk3 : 3 ≤ k := by omega
        have h1 := ih hk3
        have h2 : 2 * 2 ^ k > 2 * (2 * k) := by nlinarith [h1]
        have h3 : 2 * (2 * k) ≥ 2 * (k + 1) := by omega
        rw [pow_succ]
        omega

/-- For positive table size and repetition count, the success comparison between a long run and
the repetition expression is equivalent to the corresponding failure-tail inequality. -/
theorem amplification_comparison_is_a_tail_condition {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (_hN : 0 < N) (c : ℕ) (_hc : 0 < c) :
    chargedInitialSuccess T (c * chargedBudget N) ≥
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c
      ↔ (1 - chargedInitialSuccess T (c * chargedBudget N))
          ≤ (1 - chargedInitialSuccess T (chargedBudget N)) ^ c :=
  amplification_domination_condition T c

/-- For `c ≥ 3`, the numerical guarantee `1 - (1 / 2) ^ c` strictly exceeds `1 - 1 / (2 * c)`. -/
theorem independent_bound_strictly_exceeds_long_bound (c : ℕ) (hc : 3 ≤ c) :
    (1 - 1 / (2 * c : ℝ)) < 1 - (1 / 2 : ℝ) ^ c := by
  have hnat := two_pow_gt_two_mul_nat c hc
  have hnat' : (2 : ℝ) ^ c > 2 * (c : ℝ) := by exact_mod_cast hnat
  have hdiv : (1 / 2 : ℝ) ^ c = 1 / (2 : ℝ) ^ c := by
    rw [div_pow, one_pow]
  have hlt : 1 / (2 : ℝ) ^ c < 1 / (2 * (c : ℝ)) := by
    exact one_div_lt_one_div_of_lt (by positivity) hnat'
  rw [hdiv]
  linarith

/-- Strict superiority of the long-run success probability over the independent-repetition
expression is equivalent to a strict inequality between their failure expressions. -/
theorem amplification_domination_strict {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (_hN : 0 < N) (c : ℕ) (_hc : 0 < c) :
    (chargedInitialSuccess T (c * chargedBudget N) >
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c)
      ↔ (1 - chargedInitialSuccess T (c * chargedBudget N))
          < (1 - chargedInitialSuccess T (chargedBudget N)) ^ c := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- For `c ≥ 3`, a long run that strictly exceeds the independent-repetition success expression
also strictly exceeds `1 - 1 / (2 * c)`. -/
theorem amplification_comparison_exceeds_frozen_long_bound {N : ℕ} {α : Type*}
    [LinearOrder α] (T : Fin N → α) (hN : 0 < N) (c : ℕ) (hc : 3 ≤ c) :
    (chargedInitialSuccess T (c * chargedBudget N) >
        1 - (1 - chargedInitialSuccess T (chargedBudget N)) ^ c)
      → 1 - 1 / (2 * c : ℝ) < chargedInitialSuccess T (c * chargedBudget N) := by
  have hhalf := charged_initial_success_half T hN
  have hbounds := chargedInitialSuccess_bounds T hN (chargedBudget N)
  have hgap := independent_bound_strictly_exceeds_long_bound c hc
  have hshort : (1 - chargedInitialSuccess T (chargedBudget N)) ^ c
      ≤ (1 / 2 : ℝ) ^ c := by
    have hq : 0 ≤ 1 - chargedInitialSuccess T (chargedBudget N) := by linarith
    have hq2 : 1 - chargedInitialSuccess T (chargedBudget N) ≤ (1 / 2 : ℝ) := by linarith
    exact pow_le_pow_left₀ hq hq2 c
  intro h
  linarith
end Qatlib.Concepts.AmplitudeSearch.Amplification
