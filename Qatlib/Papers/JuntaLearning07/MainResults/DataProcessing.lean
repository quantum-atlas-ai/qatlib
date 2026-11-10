/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {α β : Type} [Fintype α] [Fintype β]

def IsProb (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def IsStochastic (K : α → β → ℝ) : Prop :=
  (∀ a b, 0 ≤ K a b) ∧ ∀ a, ∑ b, K a b = 1

def tv (p q : α → ℝ) : ℝ := ∑ a, |p a - q a|

def pushLaw (p : α → ℝ) (K : α → β → ℝ) : β → ℝ := fun b => ∑ a, p a * K a b

theorem tv_nonneg (p q : α → ℝ) : 0 ≤ tv p q := by
  unfold tv
  exact Finset.sum_nonneg (fun a _ => abs_nonneg _)

theorem tv_comm (p q : α → ℝ) : tv p q = tv q p := by
  unfold tv
  apply Finset.sum_congr rfl
  intro a _
  rw [abs_sub_comm]

theorem isProb_pushLaw (p : α → ℝ) (hp : IsProb p) (K : α → β → ℝ)
    (hK : IsStochastic K) : IsProb (pushLaw p K) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hK0, hK1⟩ := hK
  constructor
  · intro b
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp0 a) (hK0 a b))
  · unfold pushLaw
    rw [Finset.sum_comm]
    have hrow : ∀ a, (∑ b, p a * K a b) = p a := by
      intro a
      rw [← Finset.mul_sum, hK1 a, mul_one]
    rw [Finset.sum_congr rfl (fun a _ => hrow a), hp1]

theorem tv_pushLaw_le (p q : α → ℝ) (K : α → β → ℝ) (hK : IsStochastic K) :
    tv (pushLaw p K) (pushLaw q K) ≤ tv p q := by
  obtain ⟨hK0, hK1⟩ := hK
  have hpoint : ∀ b, |pushLaw p K b - pushLaw q K b| ≤
      ∑ a, |p a - q a| * K a b := by
    intro b
    have hdiff : pushLaw p K b - pushLaw q K b = ∑ a, (p a - q a) * K a b := by
      unfold pushLaw
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hdiff]
    calc |∑ a, (p a - q a) * K a b| ≤ ∑ a, |(p a - q a) * K a b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, |p a - q a| * K a b := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul, abs_of_nonneg (hK0 a b)]
  calc tv (pushLaw p K) (pushLaw q K)
      = ∑ b, |pushLaw p K b - pushLaw q K b| := rfl
    _ ≤ ∑ b, ∑ a, |p a - q a| * K a b := Finset.sum_le_sum (fun b _ => hpoint b)
    _ = ∑ a, |p a - q a| * ∑ b, K a b := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ a, |p a - q a| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hK1 a, mul_one]
    _ = tv p q := rfl

theorem event_prob_pushLaw_le (p q : α → ℝ) (K : α → β → ℝ) (hK : IsStochastic K)
    (E : β → Prop) [DecidablePred E] :
    |(∑ b, if E b then pushLaw p K b else 0) -
      (∑ b, if E b then pushLaw q K b else 0)| ≤ tv p q := by
  have hK0 : ∀ a b, 0 ≤ K a b := hK.1
  set c : α → ℝ := fun a => p a - q a with hc
  have hterm : ∀ b,
      (if E b then pushLaw p K b else 0) -
        (if E b then pushLaw q K b else 0) =
      if E b then ∑ a, c a * K a b else 0 := by
    intro b
    by_cases hb : E b
    · rw [if_pos hb, if_pos hb, if_pos hb]
      unfold pushLaw
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      simp only [hc]
      ring
    · rw [if_neg hb, if_neg hb, if_neg hb]
      ring
  have hdiff : (∑ b, if E b then pushLaw p K b else 0) -
      (∑ b, if E b then pushLaw q K b else 0) =
      ∑ b, if E b then ∑ a, c a * K a b else 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun b _ => hterm b)
  rw [hdiff]
  calc |∑ b, if E b then ∑ a, c a * K a b else 0|
      ≤ ∑ b, |if E b then ∑ a, c a * K a b else 0| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, if E b then |∑ a, c a * K a b| else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : E b <;> simp [hb]
    _ ≤ ∑ b, if E b then (∑ a, |c a| * K a b) else 0 := by
          apply Finset.sum_le_sum
          intro b _
          by_cases hb : E b
          · rw [if_pos hb, if_pos hb]
            calc |∑ a, c a * K a b| ≤ ∑ a, |c a * K a b| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ a, |c a| * K a b := by
                  apply Finset.sum_congr rfl
                  intro a _
                  rw [abs_mul, abs_of_nonneg (hK0 a b)]
          · simp [hb]
    _ ≤ ∑ b, ∑ a, |c a| * K a b := by
          apply Finset.sum_le_sum
          intro b _
          by_cases hb : E b
          · rw [if_pos hb]
          · simp only [hb, if_false]
            exact Finset.sum_nonneg (fun a _ => mul_nonneg (abs_nonneg _) (hK0 a b))
    _ = ∑ a, |c a| * ∑ b, K a b := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ a, |c a| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hK.2 a, mul_one]
    _ = tv p q := by
          unfold tv
          apply Finset.sum_congr rfl
          intro a _
          rw [hc]

theorem success_prob_le (p q : α → ℝ) (hq : IsProb q)
    (K : α → β → ℝ) (hK : IsStochastic K)
    (E : β → Prop) [DecidablePred E] (s : ℝ)
    (hpE : (∑ b, if E b then pushLaw p K b else 0) = s)
    (hqE : (∑ b, if ¬ E b then pushLaw q K b else 0) = s) :
    2 * s - 1 ≤ tv p q := by
  have hqE' : (∑ b, if E b then pushLaw q K b else 0) = 1 - s := by
    have htot : (∑ b, if E b then pushLaw q K b else 0) +
        (∑ b, if ¬ E b then pushLaw q K b else 0) =
        ∑ b, pushLaw q K b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : E b <;> simp [hb]
    have hone : (∑ b, pushLaw q K b) = 1 := (isProb_pushLaw q hq K hK).2
    rw [hqE, hone] at htot
    linarith
  have hbound := event_prob_pushLaw_le p q K hK E
  rw [hpE, hqE'] at hbound
  have h := abs_le.mp hbound
  linarith [h.1, h.2]

end Qatlib.Papers.JuntaLearning07.MainResults
