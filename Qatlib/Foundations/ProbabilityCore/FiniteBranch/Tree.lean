/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# Finite sampling trees and their probability laws

The inductive type `Tree` represents finite probabilistic branching with value-labelled leaves.
It carries a PMF law, real-valued means, and the structural predicate `All`, which includes
every syntactic branch regardless of its probability; this provides a simple semantics for
finite randomized algorithms [AticiServedio2007].

The module proves linearity and monotonicity of means and relates nonnegative means and event
probabilities to expectations under the induced PMF.

## Main statements

* `law_map`: Mapping leaves pushes forward the output law.
* `mean_law`: The recursive mean of a nonnegative function agrees with its PMF expectation.
* `probability_law`: Predicate probability agrees with the indicator expectation under the law.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch
open scoped ENNReal Classical

/-- Finite probabilistic trees with deterministic leaves and finitely indexed PMF sampling
nodes. -/
inductive Tree (α : Type) where
  | pure : α → Tree α
  | sample (m : ℕ) (p : PMF (Fin m)) : (Fin m → Tree α) → Tree α

namespace Tree
variable {α β : Type}

/-- The PMF law of the output of a finite sampling tree. -/
def law : Tree α → PMF α
  | .pure a => PMF.pure a
  | .sample _ p children => p.bind (fun i => law (children i))

/-- The recursively computed weighted mean of a real-valued function over a finite sampling
tree. -/
def mean : Tree α → (α → ℝ) → ℝ
  | .pure a, f => f a
  | .sample _ p children, f => ∑ i, (p i).toReal * mean (children i) f

/-- The structural predicate that `P` holds at every syntactic leaf, including leaves reached
with probability zero. -/
def All (P : α → Prop) : Tree α → Prop
  | .pure a => P a
  | .sample _ _ children => ∀ i, All P (children i)

/-- Map each leaf value of a finite sampling tree, retaining its sampling structure. -/
def map (f : α → β) : Tree α → Tree β
  | .pure a => .pure (f a)
  | .sample m p children => .sample m p (fun i => map f (children i))

/-- A predicate holds throughout a mapped tree exactly when its precomposition with the map
holds throughout the original tree. -/
theorem all_map (t : Tree α) (g : α → β) (P : β → Prop) :
    (t.map g).All P ↔ t.All (fun a => P (g a)) := by
  induction t with
  | pure a => rfl
  | sample m p c ih => simp only [map,All,ih]

/-- A predicate true of every possible value holds at every leaf of a tree. -/
theorem all_of_forall (t : Tree α) {P : α → Prop} (h : ∀ a, P a) : t.All P := by
  induction t with
  | pure a => exact h a
  | sample m p c ih => exact ih

/-- A conjunction holds at every leaf exactly when both conjuncts hold at every leaf. -/
theorem all_and (t : Tree α) (P Q : α → Prop) :
    t.All (fun a => P a∧Q a) ↔ t.All P∧t.All Q := by
  induction t with
  | pure a => rfl
  | sample m p c ih => simp only [All,ih,forall_and]

/-- Pointwise implication on leaf predicates preserves `Tree.All`. -/
theorem all_mono (t : Tree α) {P Q : α → Prop} (h : t.All P)
    (hpq : ∀ a, P a → Q a) : t.All Q := by
  induction t with
  | pure a => exact hpq a h
  | sample m p c ih => exact fun i => ih i (h i)

/-- Functions agreeing at every leaf have equal tree means. -/
theorem mean_congr (t : Tree α) {f g : α → ℝ} (h : t.All (fun a => f a=g a)) :
    t.mean f=t.mean g := by
  induction t with
  | pure a => exact h
  | sample m p c ih =>
    unfold mean
    apply Finset.sum_congr rfl
    intro i _
    rw [ih i (h i)]

/-- The real-valued weights of a PMF on a finite index type sum to one. -/
theorem weights_sum {m : ℕ} (p : PMF (Fin m)) : ∑ i, (p i).toReal=1 := by
  rw [← ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top p i)]
  simpa only [tsum_fintype,ENNReal.toReal_one] using congrArg ENNReal.toReal p.tsum_coe

/-- The law of a tree with mapped leaves is the pushforward of its original law. -/
theorem law_map (t : Tree α) (g : α → β) : (t.map g).law=t.law.map g := by
  induction t with
  | pure a => simp only [map,law,PMF.pure_map]
  | sample m p children ih => simp only [map,law,ih,PMF.map_bind]

/-- Taking a mean after mapping leaves is the same as taking the mean of the precomposed
function. -/
theorem mean_map (t : Tree α) (g : α → β) (f : β → ℝ) :
    (t.map g).mean f=t.mean (fun a => f (g a)) := by
  induction t with
  | pure a => rfl
  | sample m p children ih => simp only [map,mean,ih]

/-- The tree mean of a constant function is that constant. -/
theorem mean_const (t : Tree α) (c : ℝ) : t.mean (fun _ => c)=c := by
  induction t with
  | pure a => rfl
  | sample m p children ih => simp only [mean,ih,← Finset.sum_mul,weights_sum,one_mul]

/-- The tree mean of a sum is the sum of the tree means. -/
theorem mean_add (t : Tree α) (f g : α → ℝ) :
    t.mean (fun a => f a+g a)=t.mean f+t.mean g := by
  induction t with
  | pure a => rfl
  | sample m p children ih => simp only [mean,ih,mul_add,Finset.sum_add_distrib]

/-- Multiplication of a function by a real constant commutes with taking its tree mean. -/
theorem mean_mul (t : Tree α) (c : ℝ) (f : α → ℝ) :
    t.mean (fun a => c*f a)=c*t.mean f := by
  induction t with
  | pure a => rfl
  | sample m p children ih =>
    simp only [mean,ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- An inequality holding at every leaf gives the corresponding inequality between tree means. -/
theorem mean_mono (t : Tree α) {f g : α → ℝ} (h : t.All (fun a => f a≤g a)) :
    t.mean f≤t.mean g := by
  induction t with
  | pure a => exact h
  | sample m p children ih =>
    exact Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (ih i (h i)) ENNReal.toReal_nonneg)

/-- A function nonnegative at every leaf has a nonnegative tree mean. -/
theorem mean_nonneg (t : Tree α) {f : α → ℝ} (h : t.All (fun a => 0≤f a)) : 0≤t.mean f := by
  have h' := mean_mono t h
  rwa [mean_const] at h'

/-- The extended nonnegative expectation of a function under a PMF, computed by summing
probability-weighted values. -/
def pmfMean (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a*f a

/-- The PMF expectation of a bound distribution equals the iterated expectation over the initial
distribution and the continuations. -/
theorem pmfMean_bind (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    pmfMean (p.bind q) f=pmfMean p (fun a => pmfMean (q a) f) := by
  simp only [pmfMean,PMF.bind_apply,← ENNReal.tsum_mul_right,← ENNReal.tsum_mul_left,mul_assoc]
  exact ENNReal.tsum_comm

/-- For a globally nonnegative real-valued function, the recursive tree mean converted to `ℝ≥0∞`
equals its expectation under the tree law. -/
theorem mean_law (t : Tree α) (f : α → ℝ) (hf : ∀ a, 0≤f a) :
    ENNReal.ofReal (t.mean f)=pmfMean t.law (fun a => ENNReal.ofReal (f a)) := by
  induction t with
  | pure a => simp [mean,law,pmfMean,PMF.pure_apply]
  | sample m p children ih =>
    rw [mean,ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg ENNReal.toReal_nonneg
      (mean_nonneg _ (all_of_forall _ hf)))]
    simp only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ih,ENNReal.ofReal_toReal (PMF.apply_ne_top p _)]
    rw [law,pmfMean_bind,pmfMean,tsum_fintype]

/-- The real probability of a predicate, defined as the tree mean of its indicator. -/
def probability (t : Tree α) (P : α → Prop) : ℝ := t.mean (fun a => if P a then 1 else 0)

/-- The predicate probability converted to `ℝ≥0∞` equals its indicator expectation under the
tree law. -/
theorem probability_law (t : Tree α) (P : α → Prop) :
    ENNReal.ofReal (t.probability P)=pmfMean t.law (fun a => if P a then 1 else 0) := by
  have h :=
      mean_law t (fun a => if P a then 1 else 0) (fun a => by (try dsimp); split_ifs <;> norm_num)
  simpa only [probability,apply_ite ENNReal.ofReal,ENNReal.ofReal_one,ENNReal.ofReal_zero] using h
end Tree
end Qatlib.Foundations.ProbabilityCore.FiniteBranch
