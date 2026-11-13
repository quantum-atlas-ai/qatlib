/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Survival tails and finite stopping costs

This module defines `finiteSurvival` for a probability-mass-function transition system and
relates finite stopping costs to survival probabilities. It proves that first-stop probabilities
are successive survival differences and that expected truncated cost is the finite sum of
survival tails.

The event and expectation identities support a geometric bound when every transition continues
with probability at most `q ≤ 1`. Such bounds provide cost estimates for finite truncations of
randomized quantum search as studied in [BoyerEtAl1998].

## Main statements

* `finite_first_stop_mass`: first-stop mass as a survival difference.
* `finite_stopping_cost_tail_sum`: the finite tail-sum identity for expected cost.
* `finite_survival_geometric_bound`: geometric survival and truncated-cost bounds.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

section Helpers

variable {α β ι : Type}

namespace CostedLaw

/-- Pointwise equal functions have equal expectations under the same probability mass function. -/
theorem expectation_congr {p : PMF α} {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) :
    expectation p f = expectation p g :=
  tsum_congr fun a => by rw [h a]

/-- A pointwise inequality between extended nonnegative real functions gives the corresponding
inequality between their expectations. -/
theorem expectation_le_of_forall {p : PMF α} {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) :
    expectation p f ≤ expectation p g := by
  show ∑' a, p a * f a ≤ ∑' a, p a * g a
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hp : p a = 0
  · simp [hp]
  · exact (ENNReal.mul_le_mul_iff_right hp
        (fun h => absurd (PMF.coe_le_one p a) (by rw [h]; simp))).mpr (h a)

/-- The probability of an event equals the expectation of its zero-one indicator. -/
theorem event_eq (p : PMF α) (Q : α → Prop) :
    event p Q = expectation p fun x => if Q x then 1 else 0 := rfl

/-- The probability of an event under `ret a` is the indicator of that event at the zero-cost
output `(a, 0)`. -/
theorem event_ret (a : α) (Q : α × ℕ → Prop) :
    event (ret a) Q = if Q (a, 0) then 1 else 0 := by
  show expectation (PMF.pure (a, 0)) (fun x => if Q x then 1 else 0) = _
  rw [expectation_pure]

/-- An event containing the zero-cost output `(a, 0)` has probability one under `ret a`. -/
theorem event_ret_one (a : α) {Q : α × ℕ → Prop} (h : Q (a, 0)) : event (ret a) Q = 1 := by
  rw [event_ret, ite_eq_left h]

/-- An event excluding the zero-cost output `(a, 0)` has probability zero under `ret a`. -/
theorem event_ret_zero (a : α) {Q : α × ℕ → Prop} (h : ¬Q (a, 0)) : event (ret a) Q = 0 := by
  rw [event_ret, ite_eq_right h]

/-- The probability of an event after monadic binding equals the expectation of its conditional
event probabilities. -/
theorem event_bind_general (p : CostedLaw α) (g : α × ℕ → PMF (β × ℕ)) (Q : β × ℕ → Prop) :
    event (PMF.bind p g) Q = expectation p fun x => event (g x) Q := by
  rw [event_eq (PMF.bind p g) Q, expectation_bind]
  exact expectation_congr fun x => event_eq (g x) Q

/-- The probability of an event under a mapped probability mass function equals the probability
of its preimage. -/
theorem event_map (p : PMF α) (g : α → β) (E : β → Prop) :
    event (PMF.map g p) E = event p fun x => E (g x) := by
  rw [event_eq (PMF.map g p) E, event_eq p fun x => E (g x), expectation_map]

/-- Charging cost `n` transforms an event by adding `n` to the recorded cost. -/
theorem event_charge_general (n : ℕ) (q : CostedLaw α) (Q : α × ℕ → Prop) :
    event (charge n q) Q = event q fun y => Q (y.1, n + y.2) := by
  rw [show charge n q = PMF.map (fun x => (x.1, n + x.2)) q from rfl, event_map]

/-- The probability of any event under a probability mass function is at most one. -/
theorem event_le_one (p : PMF α) (E : α → Prop) : event p E ≤ 1 := by
  show ∑' a, p a * (if E a then 1 else 0) ≤ 1
  calc ∑' a, p a * (if E a then 1 else 0) ≤ ∑' a, p a * 1 :=
        ENNReal.tsum_le_tsum fun a => by by_cases hE : E a <;> simp [hE]
    _ = 1 := by simp [PMF.tsum_coe]

/-- Pointwise equivalent event predicates have equal probabilities. -/
theorem event_congr {p : PMF α} {E E' : α → Prop} (h : ∀ a, E a ↔ E' a) :
    event p E = event p E' := by
  show ∑' a, p a * (if E a then 1 else 0) = ∑' a, p a * (if E' a then 1 else 0)
  exact expectation_congr fun a => by
    by_cases h1 : E a
    · simp [h1, (h a).mp h1]
    · have h2 : ¬E' a := fun hx => h1 ((h a).mpr hx)
      simp [h1, h2]

/-- An event that holds for no outcome has probability zero. -/
theorem event_zero (p : PMF α) (E : α → Prop) (h : ∀ a, ¬E a) : event p E = 0 := by
  have h0 : ∀ a, p a * (if E a then 1 else 0) = 0 := fun a => by rw [ite_eq_right (h a), mul_zero]
  show ∑' a, p a * (if E a then 1 else 0) = 0
  rw [tsum_congr h0]
  exact tsum_zero

/-- Multiplication by a constant in `ℝ≥0∞` commutes with expectation. -/
theorem expectation_const_mul (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expectation p (fun a => c * f a) = c * expectation p f := by
  show ∑' a, p a * (c * f a) = c * ∑' a, p a * f a
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by ring

/-- Expectation commutes with a finite sum of extended nonnegative real functions. -/
theorem expectation_sum (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    expectation p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expectation p (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    have hL : expectation p (fun a => ∑ j ∈ insert i s, f j a)
        = expectation p (f i) + expectation p (fun a => ∑ j ∈ s, f j a) := by
      simp only [Finset.sum_insert hi]
      exact expectation_add p (f i) (fun a => ∑ j ∈ s, f j a)
    rw [hL, ih, Finset.sum_insert hi]

end CostedLaw

/-- The equivalence between a sum type and a Boolean-indexed dependent pair, with `false`
selecting the left summand. -/
private def sumSigmaEquivAux (α β : Type) :
    (α ⊕ β) ≃ ((b : Bool) × Bool.rec (motive := fun _ => Type) α β b) where
  toFun
    | Sum.inl a => ⟨false, a⟩
    | Sum.inr b => ⟨true, b⟩
  invFun s :=
    match s with
    | ⟨false, x⟩ => Sum.inl x
    | ⟨true, x⟩ => Sum.inr x
  left_inv z := by cases z <;> rfl
  right_inv s := by
    match s with
    | ⟨false, x⟩ => rfl
    | ⟨true, x⟩ => rfl

/-- An extended nonnegative real sum over a sum type splits into the sums over its two summands. -/
theorem tsum_sum_type' {α β : Type} (F : α ⊕ β → ℝ≥0∞) :
    ∑' z : α ⊕ β, F z = (∑' a, F (Sum.inl a)) + ∑' b, F (Sum.inr b) := by
  have htrue : (∑' x : (Bool.rec (motive := fun _ => Type) α β true),
      F ((sumSigmaEquivAux α β).symm ⟨true, x⟩)) = ∑' b : β, F (Sum.inr b) := rfl
  have hfalse : (∑' x : (Bool.rec (motive := fun _ => Type) α β false),
      F ((sumSigmaEquivAux α β).symm ⟨false, x⟩)) = ∑' a : α, F (Sum.inl a) := rfl
  have hconv : ∑' s : ((b : Bool) × Bool.rec (motive := fun _ => Type) α β b),
      F ((sumSigmaEquivAux α β).symm s)
      = ∑' (b : Bool) (x : Bool.rec (motive := fun _ => Type) α β b),
        F ((sumSigmaEquivAux α β).symm ⟨b, x⟩) :=
    ENNReal.tsum_sigma fun b x => F ((sumSigmaEquivAux α β).symm ⟨b, x⟩)
  have h0 : ∑' s : ((b : Bool) × Bool.rec (motive := fun _ => Type) α β b),
      F ((sumSigmaEquivAux α β).symm s)
      = (∑' a, F (Sum.inl a)) + ∑' b, F (Sum.inr b) := by
    rw [hconv, tsum_fintype, Fintype.sum_bool, htrue, hfalse, add_comm]
  have hs : HasSum (fun s : ((b : Bool) × Bool.rec (motive := fun _ => Type) α β b) =>
      F ((sumSigmaEquivAux α β).symm s)) ((∑' a, F (Sum.inl a)) + ∑' b, F (Sum.inr b)) := by
    rw [← h0]
    exact ENNReal.summable.hasSum
  exact ((Equiv.hasSum_iff (sumSigmaEquivAux α β).symm).mp hs).tsum_eq

/-- An extended nonnegative real sum over a product type equals the iterated sum over its two
factors. -/
theorem tsum_prod_type' {α β : Type} (F : α × β → ℝ≥0∞) :
    ∑' p : α × β, F p = ∑' a, ∑' b, F (a, b) :=
  Summable.tsum_prod' ENNReal.summable fun _ => ENNReal.summable

end Helpers

section Survival

variable {S A : Type}

/-- The probability that a configuration is still running after `n` steps of `runFor`. -/
noncomputable def finiteSurvival (next : S → PMF (Configuration S A))
    (n : ℕ) (cfg : Configuration S A) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next n cfg) fun x => ∃ s, x.1 = Sum.inr s

/-- A running initial configuration survives zero steps with probability one. -/
theorem finiteSurvival_zero_running (next : S → PMF (Configuration S A)) (s : S) :
    finiteSurvival next 0 (Sum.inr s) = 1 := by
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next 0 (Sum.inr s))
      (fun x => ∃ t, x.1 = Sum.inr t) = 1
  rw [runFor_zero]
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_one _ ⟨s, rfl⟩

/-- A halted initial configuration has survival probability zero at every finite horizon. -/
theorem finiteSurvival_halted (next : S → PMF (Configuration S A)) (n : ℕ) (a : A) :
    finiteSurvival next n (Sum.inl a) = 0 := by
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next n (Sum.inl a))
      (fun x => ∃ t, x.1 = Sum.inr t) = 0
  rw [runFor_halted]
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_zero _ fun h => Exists.elim h fun t ht => Sum.inl_ne_inr ht

/-- The finite-horizon survival probability is at most one. -/
theorem finiteSurvival_le_one (next : S → PMF (Configuration S A)) (n : ℕ)
    (cfg : Configuration S A) : finiteSurvival next n cfg ≤ 1 :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _

/-- Survival for `j + 1` steps from a running state equals the expected `j`-step survival after
one transition. -/
theorem finiteSurvival_succ_running (next : S → PMF (Configuration S A)) (j : ℕ) (s : S) :
    finiteSurvival next (j + 1) (Sum.inr s) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s) fun cfg => finiteSurvival next j cfg := by
  have h1 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (PMF.bind (tick next (Sum.inr s)) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next j x.1))
        (fun y => ∃ t, y.1 = Sum.inr t)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (tick next (Sum.inr s))
        (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next j x.1))
          (fun y => ∃ t, y.1 = Sum.inr t)) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general _ _ _
  have h2 : tick next (Sum.inr s) = PMF.map (fun c => (c, 1)) (next s) := rfl
  have h3 : ∀ c : Configuration S A,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor next j c)) (fun y => ∃ t, y.1 = Sum.inr t)
        = finiteSurvival next j c := fun c =>
    (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general 1 (runFor next j c)
      (fun y => ∃ t, y.1 = Sum.inr t) : _)
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next (j + 1) (Sum.inr s)) (fun x => ∃ t, x.1 = Sum.inr t)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s) (fun cfg => finiteSurvival next j cfg)
  rw [show runFor next (j + 1) (Sum.inr s)
      = PMF.bind (tick next (Sum.inr s)) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next j x.1) from rfl,
    h1, h2, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun c => h3 c

/-- Finite-horizon survival probability is nonincreasing in the number of steps. -/
theorem finiteSurvival_succ_le (next : S → PMF (Configuration S A)) (n : ℕ)
    (cfg : Configuration S A) : finiteSurvival next (n + 1) cfg ≤ finiteSurvival next n cfg := by
  have h1 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (PMF.bind (runFor next n cfg) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next 1 x.1))
        (fun y => ∃ t, y.1 = Sum.inr t)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor next n cfg)
        (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next 1 x.1))
          (fun y => ∃ t, y.1 = Sum.inr t)) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general _ _ _
  show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next (n + 1) cfg) (fun x => ∃ t, x.1 = Sum.inr t)
      ≤ finiteSurvival next n cfg
  rw [runFor_add next n 1 cfg,
    show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (runFor next n cfg) (runFor next 1)
      = PMF.bind (runFor next n cfg) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next 1 x.1) from rfl,
    h1]
  calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor next n cfg)
          (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next 1 x.1))
            (fun y => ∃ t, y.1 = Sum.inr t))
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (runFor next n cfg)
          (fun x => if (∃ t, x.1 = Sum.inr t) then 1 else 0) :=
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall fun x => by
          have hEq : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next 1 x.1))
              (fun y => ∃ t, y.1 = Sum.inr t)
              = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next 1 x.1) (fun y => ∃ t, y.1 = Sum.inr t) :=
            Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general x.2 (runFor next 1 x.1)
              (fun y => ∃ t, y.1 = Sum.inr t)
          rw [hEq]
          rcases x with ⟨c, _⟩
          cases c with
          | inl a =>
              rw [runFor_halted]
              exact le_trans
                (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_zero _ fun h => Exists.elim h fun t ht => Sum.inl_ne_inr ht).le
                zero_le
          | inr t =>
              exact le_trans
                  (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _)
                  (by simp)
    _ = finiteSurvival next n cfg := rfl

/-- Successive survival probabilities are nonincreasing and at most one, and halted
configurations have zero survival probability. -/
theorem finiteSurvival_bounds (next : S → PMF (Configuration S A))
    (cfg : Configuration S A) (n : ℕ) :
    finiteSurvival next (n + 1) cfg ≤ finiteSurvival next n cfg ∧
      finiteSurvival next n cfg ≤ 1 ∧
      ∀ a, finiteSurvival next n (Sum.inl a) = 0 :=
  ⟨finiteSurvival_succ_le next n cfg, finiteSurvival_le_one next n cfg,
    fun a => finiteSurvival_halted next n a⟩

/-- Starting from a running state, the probability of halting with recorded cost zero is zero
for every finite fuel bound. -/
theorem runFor_no_halt_at_cost_zero (next : S → PMF (Configuration S A))
    (fuel : ℕ) (t : S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr t))
      (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = 0) = 0 := by
  induction fuel generalizing t with
  | zero =>
      rw [runFor_zero]
      exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_zero _ fun h => absurd h.1 (by simp)
  | succ fuel _ =>
      have h1 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (PMF.bind (tick next (Sum.inr t)) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next fuel x.1))
            (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = 0)
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (tick next (Sum.inr t))
            (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next fuel x.1))
              (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = 0)) :=
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general _ _ _
      have h2 : ∀ c : Configuration S A,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor next fuel c))
              (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = 0) = 0 := by
        intro c
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general]
        exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_zero _ _ fun y hy => absurd hy.2 (by simp)
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next (fuel + 1) (Sum.inr t))
          (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = 0) = 0
      rw [show runFor next (fuel + 1) (Sum.inr t)
          = PMF.bind (tick next (Sum.inr t)) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next fuel x.1)
          from rfl, h1, show tick next (Sum.inr t) = PMF.map (fun c => (c, 1)) (next t) from rfl,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      exact (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun c => h2 c).trans
        (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const (next t) 0)

/-- Within the fuel bound, the probability of halting at cost `j + 1` plus survival through `j +
1` steps equals survival through `j` steps. -/
private theorem first_stop_add_aux (next : S → PMF (Configuration S A)) :
    ∀ (fuel : ℕ) (s : S) (j : ℕ), j + 1 ≤ fuel →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr s))
          (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = j + 1) +
        finiteSurvival next (j + 1) (Sum.inr s) = finiteSurvival next j (Sum.inr s) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ hj; omega
  | succ fuel ih =>
      intro s j hj
      have hbind : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (PMF.bind (tick next (Sum.inr s)) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next fuel x.1))
            (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = j + 1)
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (tick next (Sum.inr s))
            (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next fuel x.1))
              (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = j + 1)) :=
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general _ _ _
      have hshift : ∀ c : Configuration S A,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor next fuel c))
              (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = j + 1) =
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel c)
              (fun y => (∃ a, y.1 = Sum.inl a) ∧ 1 + y.2 = j + 1) := fun c =>
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general 1 (runFor next fuel c)
          (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = j + 1)
      have hA : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (tick next (Sum.inr s))
            (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next fuel x.1))
              (fun y => (∃ a, y.1 = Sum.inl a) ∧ y.2 = j + 1))
          = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s)
            (fun c => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel c)
              (fun y => (∃ a, y.1 = Sum.inl a) ∧ 1 + y.2 = j + 1)) := by
        rw [show tick next (Sum.inr s) = PMF.map (fun c => (c, 1)) (next s) from rfl,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
        exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun c => hshift c
      show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next (fuel + 1) (Sum.inr s))
          (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = j + 1) +
        finiteSurvival next (j + 1) (Sum.inr s) = finiteSurvival next j (Sum.inr s)
      rw [show runFor next (fuel + 1) (Sum.inr s)
          = PMF.bind (tick next (Sum.inr s)) fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor next fuel x.1)
          from rfl, hbind, hA, finiteSurvival_succ_running,
        ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add (next s)
          (fun c => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel c)
            (fun y => (∃ a, y.1 = Sum.inl a) ∧ 1 + y.2 = j + 1))
          (fun c => finiteSurvival next j c)]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        rw [finiteSurvival_zero_running,
            ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const (next s) 1]
        refine Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun c => ?_
        cases c with
        | inl a =>
            have hp : (fun y : Configuration S A × ℕ => (∃ a', y.1 = Sum.inl a') ∧ 1 + y.2 = 0 + 1)
                (Sum.inl a, 0) := ⟨(⟨a, rfl⟩ : ∃ a' : A, Sum.inl a = Sum.inl a'), by omega⟩
            rw [runFor_halted, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_one (Sum.inl a) hp,
              finiteSurvival_halted]
            norm_num
        | inr t =>
            have h0 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr t))
                (fun y => (∃ a', y.1 = Sum.inl a') ∧ 1 + y.2 = 0 + 1) = 0 := by
              have hiff : ∀ y : Configuration S A × ℕ,
                  ((∃ a', y.1 = Sum.inl a') ∧ 1 + y.2 = 0 + 1) ↔
                    ((∃ a, y.1 = Sum.inl a) ∧ y.2 = 0) :=
                fun y => ⟨fun hy => ⟨hy.1, by omega⟩, fun hy => ⟨hy.1, by omega⟩⟩
              rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hiff]
              exact runFor_no_halt_at_cost_zero next fuel t
            rw [h0, finiteSurvival_zero_running]
            norm_num
      · have hjm : j - 1 + 1 = j := by omega
        have hR : finiteSurvival next j (Sum.inr s)
            = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s) (fun c => finiteSurvival next (j - 1) c) := by
          rw [← finiteSurvival_succ_running next (j - 1) s, hjm]
        rw [hR]
        refine Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun c => ?_
        cases c with
        | inl a =>
            have hne : ¬ ((∃ a' : A, (Sum.inl a : Configuration S A) = Sum.inl a') ∧
                (1 : ℕ) + 0 = j + 1) := fun h => by omega
            have hn : ¬ (fun y : Configuration S A × ℕ => (∃ a', y.1 = Sum.inl a') ∧ 1 + y.2 = j + 1)
                (Sum.inl a, 0) := hne
            rw [runFor_halted, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret_zero (Sum.inl a) hn,
              finiteSurvival_halted, finiteSurvival_halted]
            norm_num
        | inr t =>
            have hgoal : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr t))
                  (fun y => (∃ a', y.1 = Sum.inl a') ∧ 1 + y.2 = j + 1) +
                finiteSurvival next j (Sum.inr t) = finiteSurvival next (j - 1) (Sum.inr t) := by
              have htarget := ih t (j - 1) (by omega)
              have hshift2 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr t))
                  (fun y => (∃ a', y.1 = Sum.inl a') ∧ 1 + y.2 = j + 1) =
                  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr t))
                    (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = (j - 1) + 1) := by
                have hiff : ∀ y : Configuration S A × ℕ,
                    ((∃ a', y.1 = Sum.inl a') ∧ 1 + y.2 = j + 1) ↔
                      ((∃ a, y.1 = Sum.inl a) ∧ y.2 = (j - 1) + 1) :=
                  fun y => ⟨fun hy => ⟨hy.1, by omega⟩, fun hy => ⟨hy.1, by omega⟩⟩
                rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hiff]
              have hS : finiteSurvival next ((j - 1) + 1) (Sum.inr t)
                  = finiteSurvival next j (Sum.inr t) := by rw [hjm]
              rw [hshift2, ← hS]
              exact htarget
            exact hgoal

/-- For `1 ≤ k ≤ fuel`, the probability of halting at cost `k` plus survival through `k` steps
equals survival through `k - 1` steps. -/
theorem first_stop_mass_add (next : S → PMF (Configuration S A)) (fuel k : ℕ) (s : S)
    (hk : 1 ≤ k) (hkf : k ≤ fuel) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr s))
        (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = k) +
      finiteSurvival next k (Sum.inr s) = finiteSurvival next (k - 1) (Sum.inr s) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact first_stop_add_aux next fuel s j (by omega)

/-- For `1 ≤ k ≤ fuel`, the probability of halting at cost `k` is the difference between the
survival probabilities at `k - 1` and `k`. -/
theorem finite_first_stop_mass (next : S → PMF (Configuration S A)) (s : S)
    (fuel k : ℕ) (h1 : 1 ≤ k) (hk : k ≤ fuel) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr s))
        (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = k) =
      finiteSurvival next (k - 1) (Sum.inr s) - finiteSurvival next k (Sum.inr s) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hadd := first_stop_add_aux next fuel s j (by omega)
  rw [Nat.add_sub_cancel]
  have hle : finiteSurvival next (j + 1) (Sum.inr s) ≤ finiteSurvival next j (Sum.inr s) :=
    finiteSurvival_succ_le next j _
  have hkey : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next fuel (Sum.inr s))
        (fun x => (∃ a, x.1 = Sum.inl a) ∧ x.2 = j + 1) +
      finiteSurvival next (j + 1) (Sum.inr s) =
      (finiteSurvival next j (Sum.inr s) - finiteSurvival next (j + 1) (Sum.inr s)) +
        finiteSurvival next (j + 1) (Sum.inr s) := by
    rw [tsub_add_cancel_of_le hle]
    exact hadd
  refine WithTop.add_right_cancel ?_ hkey
  intro h
  have hle1 := finiteSurvival_le_one next (j + 1) (Sum.inr s)
  rw [h] at hle1
  exact absurd hle1 (not_le.2 (by simp : (1 : ℝ≥0∞) < ⊤))

/-- The expected cost of a finite run equals the sum of its survival probabilities at times
strictly below the fuel bound. -/
theorem finite_stopping_cost_tail_sum (next : S → PMF (Configuration S A))
    (cfg : Configuration S A) (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor next fuel cfg)
      = ∑ k ∈ Finset.range fuel, finiteSurvival next k cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
      cases cfg with
      | inl a =>
          show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
              (runFor next (fuel + 1) (Sum.inl a)) = _
          rw [runFor_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost_ret]
          simp [finiteSurvival_halted]
      | inr s =>
          have htick : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (tick next (Sum.inr s)) = 1 := by
            show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
                (tick next (Sum.inr s)) (fun x => (x.2 : ℝ≥0∞)) = 1
            rw [show tick next (Sum.inr s) = PMF.map (fun c => (c, 1)) (next s) from rfl,
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const (next s) 1]
            exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun a => by simp
          have hexp : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (tick next (Sum.inr s))
              (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor next fuel x.1))
              = ∑ k ∈ Finset.range fuel, finiteSurvival next (k + 1) (Sum.inr s) := by
            rw [show tick next (Sum.inr s) = PMF.map (fun c => (c, 1)) (next s) from rfl,
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
            have hinner : ∀ a : Configuration S A,
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor next fuel (a, 1).1)
                  = ∑ k ∈ Finset.range fuel, finiteSurvival next k a :=
              fun a => ih ((a, 1).1)
            rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hinner,
                Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_sum]
            exact Finset.sum_congr rfl fun k _ => (finiteSurvival_succ_running next k s).symm
          show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
              (runFor next (fuel + 1) (Sum.inr s)) = _
          rw [runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost_bind, htick, hexp,
            Finset.sum_range_succ', finiteSurvival_zero_running, add_comm]

/-- If every transition remains running with probability at most `q ≤ 1`, survival through
`fuel` steps is at most `q^fuel`. The expected truncated cost is at most the corresponding
finite geometric sum. -/
theorem finite_survival_geometric_bound (next : S → PMF (Configuration S A))
    (s : S) (q : ℝ≥0∞) (fuel : ℕ) (hq : q ≤ 1)
    (hstep : ∀ t, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (next t) (fun cfg => ∃ u, cfg = Sum.inr u) ≤ q) :
    finiteSurvival next fuel (Sum.inr s) ≤ q ^ fuel ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor next fuel (Sum.inr s))
        ≤ ∑ k ∈ Finset.range fuel, q ^ k := by
  have hqpow : ∀ f : ℕ, q ^ f ≤ 1 := by
    intro f
    induction f with
    | zero => simp
    | succ f ih =>
        calc q ^ (f + 1) = q ^ f * q := pow_succ q f
          _ ≤ 1 * 1 := mul_le_mul' ih hq
          _ = 1 := by simp
  have hmain : ∀ (f : ℕ) (t : S), finiteSurvival next f (Sum.inr t) ≤ q ^ f := by
    intro f
    induction f with
    | zero => intro t; rw [finiteSurvival_zero_running]; simp
    | succ f ih =>
        intro t
        rw [finiteSurvival_succ_running]
        calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next t) (fun c => finiteSurvival next f c)
            ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next t) (fun c => if (∃ u, c = Sum.inr u) then q ^ f else 0) :=
              Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall fun c => by
                cases c with
                | inl a => rw [finiteSurvival_halted]; simp
                | inr u => simp [ih u]
          _ = q ^ f * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (next t) (fun cfg => ∃ u, cfg = Sum.inr u) := by
              have hc : ∀ c : Configuration S A,
                  (if (∃ u, c = Sum.inr u) then q ^ f else 0)
                    = q ^ f * (if (∃ u, c = Sum.inr u) then 1 else 0) := by
                intro c
                by_cases hc : ∃ u, c = Sum.inr u <;> simp [hc]
              rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hc,
                  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
              rfl
          _ ≤ q ^ f * q := by
              by_cases hq0 : q ^ f = 0
              · simp [hq0]
              · refine (ENNReal.mul_le_mul_iff_right hq0 ?_).mpr (hstep t)
                exact fun h => absurd (hqpow f) (by rw [h]; simp)
          _ = q ^ (f + 1) := by rw [pow_succ]
  refine ⟨hmain fuel s, ?_⟩
  rw [finite_stopping_cost_tail_sum]
  exact Finset.sum_le_sum fun k _ => hmain k s

end Survival

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
