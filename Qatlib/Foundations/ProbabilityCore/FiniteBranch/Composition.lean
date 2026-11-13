/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree

/-!
# Composition and probability bounds for finite trees

This module composes finite sampling trees using `Tree.bind` and proves the corresponding laws
for distributions, means, and structural branch predicates. Complement, union, and Markov bounds
then support probability and cost estimates for finite randomized algorithms
[AticiServedio2007].

## Main statements

* `law_bind`: Tree composition agrees with PMF bind.
* `mean_bind`: Means obey iterated expectation.
* `probability_overflow_le`: Expected nonnegative cost bounds the probability of exceeding a
  positive budget.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
open scoped Classical
variable {α β ι : Type}

/-- Compose finite sampling trees by replacing every leaf with the tree selected by its value. -/
def bind : Tree α → (α → Tree β) → Tree β
  | .pure a, f => f a
  | .sample m p c, f => .sample m p (fun i => bind (c i) f)

/-- The law of tree composition is the PMF bind of the initial law and continuation laws. -/
theorem law_bind (t : Tree α) (f : α → Tree β) :
    (t.bind f).law=t.law.bind (fun a => (f a).law) := by
  induction t with
  | pure a => simp [bind,law]
  | sample m p c ih => simp only [bind,law,ih,PMF.bind_bind]

/-- The mean after tree composition equals the initial tree's mean of the continuation means. -/
theorem mean_bind (t : Tree α) (g : α → Tree β) (f : β → ℝ) :
    (t.bind g).mean f=t.mean (fun a => (g a).mean f) := by
  induction t with
  | pure a => rfl
  | sample m p c ih => simp only [bind,mean,ih]

/-- A predicate holds on every branch of a bound tree exactly when every initial branch
satisfies the corresponding continuation predicate. -/
theorem all_bind (t : Tree α) (g : α → Tree β) (P : β → Prop) :
    (t.bind g).All P ↔ t.All (fun a => (g a).All P) := by
  induction t with
  | pure a => rfl
  | sample m p c ih => simp only [bind,All,ih]

/-- A tree mean commutes with a finite sum of real-valued functions. -/
theorem mean_sum (t : Tree α) (s : Finset ι) (f : ι → α → ℝ) :
    t.mean (fun a => ∑ i ∈ s, f i a)=∑ i ∈ s, t.mean (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [mean_const]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,mean_add,ih]

/-- The probabilities of a predicate and its complement sum to one. -/
theorem probability_compl (t : Tree α) (P : α → Prop) :
    t.probability P+t.probability (fun a => ¬P a)=1 := by
  rw [probability,probability,← mean_add]
  calc
    _ = t.mean (fun _ => 1) := by
      apply mean_congr t
      apply all_of_forall
      intro a
      by_cases h : P a <;> simp [h]
    _ = 1 := mean_const t 1

/-- The probability of the union of two predicates is at most the sum of their probabilities. -/
theorem probability_union_le (t : Tree α) (P Q : α → Prop) :
    t.probability (fun a => P a∨Q a)≤t.probability P+t.probability Q := by
  rw [probability,probability,probability,← mean_add]
  apply mean_mono t
  apply all_of_forall
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq]

/-- For globally nonnegative cost and a positive budget `B`, the probability that cost exceeds
`B` is at most the mean cost divided by `B`. -/
theorem probability_overflow_le (t : Tree α) (cost : α → ℝ) (hcost : ∀ a,0≤cost a)
    (B : ℝ) (hB : 0<B) :
    t.probability (fun a => B<cost a)≤t.mean cost/B := by
  have h : t.mean (fun a => if B<cost a then 1 else 0)≤
      t.mean (fun a => B⁻¹*cost a) := by
    apply mean_mono t
    apply all_of_forall
    intro a
    by_cases ha : B<cost a
    · simp only [ha,if_true]
      rw [← div_eq_inv_mul,le_div_iff₀ hB]
      simpa using ha.le
    · simp only [ha,if_false]
      exact mul_nonneg (inv_nonneg.2 hB.le) (hcost a)
  simpa only [probability,mean_mul,div_eq_inv_mul] using h
end Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
