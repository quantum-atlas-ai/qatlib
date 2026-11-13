/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Finite sampling of counted search circuits

`finiteCoinThenAttempt` composes finite fair-bit rejection sampling with a family of costed
trials. Its expectation and event identities keep sampling costs separate from trial costs.
`finiteCoinSearch` specializes this construction to Born measurements after a sampled number of
oracle queries.

The mathematical background is described in [BoyerEtAl1998].

## Main statements

* `finite_coin_attempt_joint_cost`: separates expected sampler and trial costs.
* `finite_coin_counted_search_event`: computes the marked-event probability.
* `finite_coin_counted_search_resources`: gives expected queries and support bounds.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

/-- Expectation is the infinite sum of the observable weighted by the probability mass function. -/
private theorem expectation_tsum {α : Type} (p : PMF α) (f : α → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f = ∑' a, p a * f a := rfl

/-- The probability of returning `Sum.inl i` is the sum of its joint masses over all costs. -/
private theorem event_outcome_inl {m : ℕ}
    (p : PMF (RandomizedExecution.Configuration Unit (Fin m) × ℕ)) (i : Fin m) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => x.1 = Sum.inl i) = ∑' n, p ((Sum.inl i : RandomizedExecution.Configuration Unit (Fin m)), n) := by
  have hU : (∑' t : Unit, (∑' n : ℕ, p ((Sum.inr t : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inr t : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inl i) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0)) = 0 := by
    refine Eq.trans (tsum_eq_single () fun t ht => by
      cases t
      exact absurd rfl ht) ?_
    refine ENNReal.tsum_eq_zero.mpr fun n => ?_
    rcases em (((Sum.inr () : RandomizedExecution.Configuration Unit (Fin m)), n).1
        = Sum.inl i) with hcond | hcond
    · exfalso
      exact absurd hcond (by simp)
    · rw [if_neg hcond, mul_zero]
  have hzero : ∀ a : Fin m, a ≠ i → (∑' n : ℕ, p ((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inl i) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0) = 0 := by
    intro a ha
    refine ENNReal.tsum_eq_zero.mpr fun n => ?_
    rcases em (((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n).1
        = Sum.inl i) with hcond | hcond
    · exfalso
      exact ha (by simpa using hcond)
    · rw [if_neg hcond, mul_zero]
  have hF : (∑' a : Fin m, (∑' n : ℕ, p ((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inl i) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0))
      = ∑' n : ℕ, p ((Sum.inl i : RandomizedExecution.Configuration Unit (Fin m)), n) := by
    refine Eq.trans (tsum_eq_single i fun a ha => hzero a ha) ?_
    have hinner : ∀ n : ℕ, p ((Sum.inl i : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inl i : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inl i) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0 = p ((Sum.inl i : RandomizedExecution.Configuration Unit (Fin m)), n) := fun n => by
      rw [if_pos rfl, mul_one]
    exact tsum_congr hinner
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => x.1 = Sum.inl i) = _
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, expectation_tsum, tsum_prod_type', tsum_sum_type',
    hU, add_zero, hF]

/-- The probability of the pending configuration `Sum.inr ()` is the sum of its joint masses
over all costs. -/
private theorem event_outcome_inr {m : ℕ}
    (p : PMF (RandomizedExecution.Configuration Unit (Fin m) × ℕ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => x.1 = Sum.inr ()) = ∑' n, p ((Sum.inr () : RandomizedExecution.Configuration Unit (Fin m)), n) := by
  have hF : (∑' a : Fin m, (∑' n : ℕ, p ((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inr ()) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0)) = 0 := by
    refine (ENNReal.tsum_eq_zero).mpr fun a => by
      refine ENNReal.tsum_eq_zero.mpr fun n => ?_
      rcases em (((Sum.inl a : RandomizedExecution.Configuration Unit (Fin m)), n).1
        = Sum.inr ()) with hcond | hcond
      · exfalso
        exact absurd hcond (by simp)
      · rw [if_neg hcond, mul_zero]
  have hzeroU : ∀ t : Unit, t ≠ () → (∑' n : ℕ, p ((Sum.inr t : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inr t : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inr ()) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0) = 0 := by
    intro t ht
    cases t
    exact absurd rfl ht
  have hU : (∑' t : Unit, (∑' n : ℕ, p ((Sum.inr t : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inr t : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inr ()) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0))
      = ∑' n : ℕ, p ((Sum.inr () : RandomizedExecution.Configuration Unit (Fin m)), n) := by
    refine Eq.trans (tsum_eq_single () fun t ht => hzeroU t ht) ?_
    have hinner : ∀ n : ℕ, p ((Sum.inr () : RandomizedExecution.Configuration Unit (Fin m)), n)
        * @ite ℝ≥0∞ (((Sum.inr () : RandomizedExecution.Configuration Unit (Fin m)), n).1 = Sum.inr ()) (Classical.propDecidable _)
            (1 : ℝ≥0∞) 0 = p ((Sum.inr () : RandomizedExecution.Configuration Unit (Fin m)), n) := fun n => by
      rw [if_pos rfl, mul_one]
    exact tsum_congr hinner
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => x.1 = Sum.inr ()) = _
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, expectation_tsum, tsum_prod_type', tsum_sum_type',
    hF, zero_add, hU]

/-- The expectation of a configuration observable splits into the finite sum over returned
indices and the pending contribution. -/
private theorem expectation_outcome {m : ℕ}
    (p : PMF (RandomizedExecution.Configuration Unit (Fin m) × ℕ))
    (V : RandomizedExecution.Configuration Unit (Fin m) → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x => V x.1)
      = ∑ i : Fin m, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => x.1 = Sum.inl i)) * V (Sum.inl i)
        + (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => x.1 = Sum.inr ())) * V (Sum.inr ()) := by
  have hfac : ∀ c : RandomizedExecution.Configuration Unit (Fin m),
      (∑' n : ℕ, p (c, n) * V c) = (∑' n : ℕ, p (c, n)) * V c := fun c => by
    rw [ENNReal.tsum_mul_right]
  show (∑' x, p x * V x.1) = _
  rw [tsum_prod_type', tsum_sum_type']
  simp only [hfac]
  rw [tsum_eq_single () (fun t ht => by
    cases t
    exact absurd rfl ht), tsum_fintype]
  simp only [event_outcome_inl, event_outcome_inr]

/-- The continuation that runs the selected costed trial, or returns `none` for a pending
sample, preserving the sampling cost separately. -/
private noncomputable def attemptCont {A : Type} {m : ℕ} (F : Fin m → CostedLaw A)
    (x : RandomizedExecution.Configuration Unit (Fin m) × ℕ) :
    PMF (Option A × ℕ × ℕ) :=
  match x.1 with
  | Sum.inl i => (F i).map fun y => (some y.1, x.2, y.2)
  | Sum.inr _ => PMF.pure (none, x.2, 0)

/-- The joint law of a finite fair-bit sample followed by the corresponding costed trial, with
an optional outcome and separate sampling and trial costs. -/
noncomputable def finiteCoinThenAttempt {A : Type} (k m fuel : ℕ)
    (F : Fin m → CostedLaw A) : PMF (Option A × ℕ × ℕ) :=
  PMF.bind (finiteCoinRun k m fuel) (attemptCont F)

/-- The continuation preserves the given sampling cost in expectation. -/
private theorem expectation_attemptCont_fst {A : Type} {m : ℕ} (F : Fin m → CostedLaw A)
    (x : RandomizedExecution.Configuration Unit (Fin m) × ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (attemptCont F x) (fun z => (z.2.1 : ℕ))
      = ((x.2 : ℕ) : ℝ≥0∞) := by
  rcases x with ⟨c, bits⟩
  cases c with
  | inl i =>
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((F i).map fun y => (some y.1, bits, y.2))
          (fun z => (z.2.1 : ℕ)) = _
      rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F i)
            (fun a => (((some a.1, bits, a.2).2.1 : ℕ) : ℝ≥0∞))
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F i)
              (fun _ => (((Sum.inl i, bits).2 : ℕ) : ℝ≥0∞)) :=
            congrArg _ (funext fun a => rfl)
        _ = (((Sum.inl i, bits).2 : ℕ) : ℝ≥0∞) := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const _ _
  | inr t =>
      cases t
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
          (PMF.pure (none, bits, 0)) (fun z => (z.2.1 : ℕ)) = _
      rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]

/-- An observable of the optional trial output and its cost decomposes into the selected-trial
expectations and the pending contribution. -/
theorem finite_coin_attempt_observable {A : Type} (k m fuel : ℕ)
    (F : Fin m → CostedLaw A) (g : Option A → ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (finiteCoinThenAttempt k m fuel F) (fun z => g z.1 z.2.2) =
      (∑ i : Fin m, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun z => z.1 = Sum.inl i) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F i) (fun y => g (some y.1) y.2)) +
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun z => z.1 = Sum.inr ()) * g none 0 := by
  rw [finiteCoinThenAttempt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hsplit : ∀ x : RandomizedExecution.Configuration Unit (Fin m) × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (attemptCont F x) (fun z => g z.1 z.2.2) =
        (fun c : RandomizedExecution.Configuration Unit (Fin m) =>
          match c with
          | Sum.inl i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F i) (fun y => g (some y.1) y.2)
          | Sum.inr _ => g none 0) x.1 := by
    rintro ⟨c, bits⟩
    cases c <;> simp [attemptCont]
  refine Eq.trans (congrArg _ (funext hsplit)) ?_
  exact expectation_outcome (finiteCoinRun k m fuel)
    (fun c => match c with
      | Sum.inl i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F i) (fun y => g (some y.1) y.2)
      | Sum.inr _ => g none 0)

/-- The joint execution preserves expected sampling cost and expresses expected trial cost as
the selection-probability-weighted sum of trial costs. -/
theorem finite_coin_attempt_joint_cost {A : Type} (k m fuel : ℕ) (F : Fin m → CostedLaw A) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (finiteCoinThenAttempt k m fuel F) (fun x => (x.2.1 : ℕ))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (finiteCoinRun k m fuel) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (finiteCoinThenAttempt k m fuel F) (fun x => (x.2.2 : ℕ))
        = ∑ i, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun x => x.1 = Sum.inl i)
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (F i) := by
  constructor
  · rw [finiteCoinThenAttempt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    exact congrArg _ (funext fun x => expectation_attemptCont_fst F x)
  · simpa [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost] using
      finite_coin_attempt_observable k m fuel F (fun _ n => (n : ℝ≥0∞))

/-- The probability of a successful trial event is the sum of each selection probability times
the corresponding trial event probability. -/
theorem finite_coin_attempt_event {A : Type} (k m fuel : ℕ) (F : Fin m → CostedLaw A)
    (E : A → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinThenAttempt k m fuel F) (fun x => ∃ a, x.1 = some a ∧ E a)
      = ∑ i, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun x => x.1 = Sum.inl i)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (F i) (fun y => E y.1) := by
  classical
  have h := finite_coin_attempt_observable k m fuel F
    (fun a _ => @ite ℝ≥0∞ (∃ x, a = some x ∧ E x) (Classical.propDecidable _) 1 0)
  simpa [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event] using h

/-- The composite execution returns `none` with exactly the probability that finite coin
sampling remains pending. -/
theorem finite_coin_attempt_pending {A : Type} (k m fuel : ℕ)
    (F : Fin m → CostedLaw A) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinThenAttempt k m fuel F) (fun x => x.1 = none) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun x => x.1 = Sum.inr ()) := by
  classical
  have h := finite_coin_attempt_observable k m fuel F
    (fun a _ => @ite ℝ≥0∞ (a = none) (Classical.propDecidable _) 1 0)
  simpa [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event] using h

/-- A circuit consisting only of repeated query steps contains no gate step. -/
private theorem gates_repeat_query {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (m : ℕ) (hU : Step.gate U ∈ RepeatCircuit [Step.query] m) : False := by
  induction m with
  | zero => simp [RepeatCircuit] at hU
  | succ m ih =>
      rw [RepeatCircuit] at hU
      rcases List.mem_append.mp hU with h | h
      · simp at h
      · exact ih h

/-- Repeating a single query step `m` times has query count `m`. -/
private theorem queryCount_repeat_query {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) :
    QueryCount ((RepeatCircuit [Step.query] m : Circuit I)) = m := by
  rw [queryCount_repeatCircuit]
  simp

/-- The Born measurement law after `i` oracle applications to a normalized state, with the
actual circuit query count attached. -/
noncomputable def countedSearchStep {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) (hψ : Normalized ψ)
    (i : Fin m) : CostedLaw I :=
  (bornDistribution (Run O (RepeatCircuit [Step.query] (i : ℕ)) ψ)
      (normalized_run O hO (RepeatCircuit [Step.query] (i : ℕ))
        (fun U hU => (gates_repeat_query U _ hU).elim) hψ)).map
    fun y => (y, QueryCount ((RepeatCircuit [Step.query] (i : ℕ) : Circuit I)))

/-- The joint law of finite fair-bit sampling and the selected counted search trial, recording
an optional outcome, bit cost, and query cost. -/
noncomputable def finiteCoinSearch {I : Type} [Fintype I] [DecidableEq I]
    (k m fuel : ℕ) (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (hψ : Normalized ψ) : PMF (Option I × ℕ × ℕ) :=
  finiteCoinThenAttempt k m fuel
    (countedSearchStep O hO ψ hψ)

/-- The probability of membership in a finite set is the sum of its point masses. -/
private theorem event_pmf_mem_sum {α : Type} [Fintype α] (p : PMF α) (S : Finset α) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun b => b ∈ S) = ∑ b ∈ S, p b := by
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, expectation_tsum,
      tsum_fintype]
  have hEq : ∀ b ∈ Finset.univ, (p b
      * @ite ℝ≥0∞ (b ∈ S) (Classical.propDecidable (b ∈ S)) (1 : ℝ≥0∞) 0)
    = @ite ℝ≥0∞ (b ∈ S) (Classical.propDecidable (b ∈ S)) (p b) 0 := by
    intro b _
    rcases em (b ∈ S) with hb | hb
    · rw [if_pos hb, if_pos hb, mul_one]
    · rw [if_neg hb, if_neg hb, mul_zero]
  have hS : ∑ b ∈ S, (@ite ℝ≥0∞ (b ∈ S) (Classical.propDecidable (b ∈ S)) (p b) 0)
      = ∑ b ∈ S, p b :=
    Finset.sum_congr rfl fun b hb => by rw [if_pos hb]
  have hsub : ∑ b ∈ S, (@ite ℝ≥0∞ (b ∈ S) (Classical.propDecidable (b ∈ S)) (p b) 0)
      = ∑ b ∈ Finset.univ, (@ite ℝ≥0∞ (b ∈ S) (Classical.propDecidable (b ∈ S)) (p b) 0) :=
    Finset.sum_subset (Finset.subset_univ S) fun b _ hb => if_neg hb
  rw [Finset.sum_congr rfl hEq]
  exact hsub.symm.trans hS

/-- The sum of the natural indices in `Fin n`, cast to extended nonnegative reals, is `n * (n -
1) / 2`. -/
private theorem sum_fin_val (n : ℕ) :
    (∑ i : Fin n, ((i : ℕ) : ℝ≥0∞))
      = (((n : ℕ) : ℝ≥0∞) * ((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hsummap : ∑ i : Fin n, (((i.castSucc : Fin (n + 1)) : ℕ) : ℝ≥0∞)
          = ∑ i : Fin n, ((i : ℕ) : ℝ≥0∞) :=
        Finset.sum_congr rfl fun i _ => by rw [Fin.val_castSucc]
      have hlast : (((Fin.last n : Fin (n + 1)) : ℕ) : ℝ≥0∞)
          = ((n : ℕ) : ℝ≥0∞) := by simp
      rw [hsummap, ih, hlast]
      by_cases hn : n = 0
      · subst hn
        simp
      · have hnp : (((n - 1 : ℕ) : ℝ≥0∞)) + 1 = ((n : ℕ) : ℝ≥0∞) := by
          have h1 : n - 1 + 1 = n := by omega
          exact_mod_cast h1
        have h2 : ((2 : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by simp)
        calc ((n : ℕ) : ℝ≥0∞) * ((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)
                + ((n : ℕ) : ℝ≥0∞)
            = ((n : ℕ) : ℝ≥0∞) * ((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)
                + ((n : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹) := by
                rw [h2, mul_one]
          _ = (((n : ℕ) : ℝ≥0∞)) * (((((n - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)
                + (((2 : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹)) := (mul_add _ _ _).symm
          _ = (((n : ℕ) : ℝ≥0∞)) * (((((n - 1 : ℕ) : ℝ≥0∞)) + ((2 : ℝ≥0∞)))
                * ((2 : ℝ≥0∞))⁻¹) := by
                rw [add_mul]
          _ = ((n : ℕ) : ℝ≥0∞)
                * (((((n : ℕ) : ℝ≥0∞)) + ((1 : ℝ≥0∞))) * ((2 : ℝ≥0∞))⁻¹) := by
                have hb2 : (((n - 1 : ℕ) : ℝ≥0∞)) + ((2 : ℝ≥0∞))
                    = (((n : ℕ) : ℝ≥0∞)) + ((1 : ℝ≥0∞)) := by
                  rw [← hnp]
                  ring
                rw [hb2]
          _ = (((n : ℕ) : ℝ≥0∞) + ((1 : ℝ≥0∞)))
                * (((n : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞))⁻¹) := by ring
        rw [show (n + 1 - 1 : ℕ) = n from by omega, Nat.cast_add, Nat.cast_one]

/-- For a nonempty window fitting in `k` bits, the marked-event probability is the average
circuit Born success multiplied by the sampler acceptance probability. -/
theorem finite_coin_counted_search_event {I : Type} [Fintype I] [DecidableEq I]
    (k m fuel : ℕ) (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) (hm0 : 0 < m) (hm : m ≤ 2 ^ k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinSearch k m fuel O hO ψ hψ) (fun x => ∃ i ∈ S, x.1 = some i)
      = ((1 - (coinRejectMass k m) ^ fuel) / ((m : ℕ) : ℝ≥0∞))
          * ∑ i : Fin m, ENNReal.ofReal
              (MeasureProb (Run O (RepeatCircuit [Step.query] (i : ℕ)) ψ) S) := by
  have hmass : ∀ i : Fin m, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun x => x.1 = Sum.inl i)
      = (1 - (coinRejectMass k m) ^ fuel) / ((m : ℕ) : ℝ≥0∞) :=
    fun i => (finite_coin_return_and_pending k m fuel hm0 hm).2 i
  have hborn : ∀ i : Fin m,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (countedSearchStep O hO ψ hψ i) (fun y => y.1 ∈ S)
        = ENNReal.ofReal (MeasureProb (Run O (RepeatCircuit [Step.query] (i : ℕ)) ψ) S) := by
    intro i
    show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event ((bornDistribution
          (Run O (RepeatCircuit [Step.query] (i : ℕ)) ψ)
          (normalized_run O hO (RepeatCircuit [Step.query] (i : ℕ))
            (fun U hU => (gates_repeat_query U _ hU).elim) hψ)).map
        fun y => (y, QueryCount (RepeatCircuit [Step.query] (i : ℕ))))
        (fun z => z.1 ∈ S) = _
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
    show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (bornDistribution
        (Run O (RepeatCircuit [Step.query] (i : ℕ)) ψ)
        (normalized_run O hO (RepeatCircuit [Step.query] (i : ℕ))
          (fun U hU => (gates_repeat_query U _ hU).elim) hψ)) (fun b => b ∈ S) = _
    rw [event_pmf_mem_sum, bornDistribution_event]
  have hiff : ∀ z : Option I × ℕ × ℕ,
      (∃ i ∈ S, z.1 = some i) ↔ (∃ a, z.1 = some a ∧ a ∈ S) := by
    intro z
    constructor
    · rintro ⟨i, hi, hz⟩
      exact ⟨i, hz, hi⟩
    · rintro ⟨a, hz, ha⟩
      exact ⟨a, ha, hz⟩
  rw [finiteCoinSearch, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hiff,
    finite_coin_attempt_event k m fuel (countedSearchStep O hO ψ hψ) fun j => j ∈ S,
    Finset.sum_congr rfl fun i _ => by rw [hmass i, hborn i], ← Finset.mul_sum]

/-- The expected query count is `(1 - coinRejectMass k m ^ fuel) * (m - 1) / 2`; every supported
execution uses at most `fuel * k` bits and fewer than `m` queries. -/
theorem finite_coin_counted_search_resources {I : Type} [Fintype I] [DecidableEq I]
    (k m fuel : ℕ) (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (hψ : Normalized ψ) (hm0 : 0 < m) (hm : m ≤ 2 ^ k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (finiteCoinSearch k m fuel O hO ψ hψ) (fun x => (x.2.2 : ℕ))
      = (1 - (coinRejectMass k m) ^ fuel) * (((m - 1 : ℕ) : ℝ≥0∞)) / 2 ∧
      ∀ x ∈ (finiteCoinSearch k m fuel O hO ψ hψ).support,
        x.2.1 ≤ fuel * k ∧ x.2.2 < m := by
  have hmass : ∀ i : Fin m, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteCoinRun k m fuel) (fun x => x.1 = Sum.inl i)
      = (1 - (coinRejectMass k m) ^ fuel) / ((m : ℕ) : ℝ≥0∞) :=
    fun i => (finite_coin_return_and_pending k m fuel hm0 hm).2 i
  have hne : ((m : ℕ) : ℝ≥0∞) ≠ 0 := by
    intro h
    have h0 := Nat.cast_eq_zero.mp h
    omega
  constructor
  · rw [finiteCoinSearch, (finite_coin_attempt_joint_cost k m fuel
        (countedSearchStep O hO ψ hψ)).2]
    have hcost : ∀ i : Fin m,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (countedSearchStep O hO ψ hψ i) = ((i : ℕ) : ℝ≥0∞) := by
      intro i
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((bornDistribution
            (Run O (RepeatCircuit [Step.query] (i : ℕ)) ψ)
            (normalized_run O hO (RepeatCircuit [Step.query] (i : ℕ))
              (fun U hU => (gates_repeat_query U _ hU).elim) hψ)).map
          fun y => (y, QueryCount (RepeatCircuit [Step.query] (i : ℕ))))
          (fun z => (z.2 : ℕ)) = _
      rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      have hcongr : ∀ a : I,
          (((((a, QueryCount ((RepeatCircuit [Step.query] (i : ℕ) : Circuit I))) :
              I × ℕ).2 : ℕ) : ℝ≥0∞))
            = ((QueryCount ((RepeatCircuit [Step.query] (i : ℕ) : Circuit I)) : ℕ) : ℝ≥0∞) :=
        fun a => rfl
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hcongr, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const,
        queryCount_repeat_query]
    rw [Finset.sum_congr rfl fun i _ => by rw [hmass i, hcost i], ← Finset.mul_sum,
      sum_fin_val]
    have hfinal : (((1 - (coinRejectMass k m) ^ fuel) / ((m : ℕ) : ℝ≥0∞)))
        * ((((m : ℕ) : ℝ≥0∞)) * ((((m - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹))
      = (1 - (coinRejectMass k m) ^ fuel) * ((((m - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹) := by
      rw [div_eq_mul_inv, mul_assoc,
        ← mul_assoc (((m : ℕ) : ℝ≥0∞)⁻¹) (((m : ℕ) : ℝ≥0∞))
          ((((m - 1 : ℕ) : ℝ≥0∞)) * ((2 : ℝ≥0∞))⁻¹),
        mul_comm (((m : ℕ) : ℝ≥0∞)⁻¹) (((m : ℕ) : ℝ≥0∞)),
        ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _), one_mul]
    rw [hfinal, div_eq_mul_inv, mul_assoc]
  · intro z hz
    have hz' : z ∈ (PMF.bind (finiteCoinRun k m fuel)
        (attemptCont (countedSearchStep O hO ψ hψ))).support := hz
    obtain ⟨x, hx, hzx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz'
    have hbits := (finite_coin_actual_bit_cost k m fuel hm).1 x hx
    obtain ⟨c, bits⟩ := x
    cases c with
    | inl i =>
        obtain ⟨pair, hpair, hzpair⟩ := (PMF.mem_support_map_iff _ _ _).mp
          (hzx : z ∈ ((countedSearchStep O hO ψ hψ i).map
            fun w => (some w.1, bits, w.2)).support)
        obtain ⟨rfl⟩ := hzpair
        refine ⟨hbits, ?_⟩
        obtain ⟨w, -, hw2⟩ := (PMF.mem_support_map_iff _ _ _).mp hpair
        obtain ⟨rfl⟩ := hw2
        show (QueryCount ((RepeatCircuit [Step.query] (i : ℕ) : Circuit I))) < m
        rw [queryCount_repeat_query]
        exact i.isLt
    | inr t =>
        cases t
        have hz0 : z = (none, bits, 0) := by
          have hzp := hzx
          rw [show attemptCont (countedSearchStep O hO ψ hψ) (Sum.inr (), bits)
              = PMF.pure (none, bits, 0) from rfl] at hzp
          simpa [PMF.mem_support_pure_iff] using hzp
        obtain ⟨rfl⟩ := hz0
        exact ⟨hbits, hm0⟩
