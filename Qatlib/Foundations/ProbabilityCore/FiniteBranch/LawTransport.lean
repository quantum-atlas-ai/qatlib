/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Composition

/-!
# Transporting finite-tree quantities along equal laws

This module transports means of nonnegative functions and event probabilities between finite
trees with equal PMF laws. It also bounds probabilities by one and identifies pushforwards of
functions equal on every branch, separating distributional conclusions from tree syntax in
finite algorithm semantics [AticiServedio2007].

## Main statements

* `mean_eq_of_law_eq`: Equal laws give equal means for nonnegative functions.
* `probability_eq_of_law_eq`: Equal laws give equal predicate probabilities.
* `law_map_congr`: Branchwise equal maps induce equal pushforward laws.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
open scoped Classical
variable {α : Type}

/-- Finite trees with equal laws have equal means for any globally nonnegative real-valued
function. -/
theorem mean_eq_of_law_eq (s t : Tree α) (h : s.law=t.law) (f : α → ℝ)
    (hf : ∀ a,0≤f a) : s.mean f=t.mean f := by
  have he : ENNReal.ofReal (s.mean f)=ENNReal.ofReal (t.mean f) := by
    rw [mean_law s f hf,mean_law t f hf,h]
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (mean_nonneg s (all_of_forall _ hf)),
    ENNReal.toReal_ofReal (mean_nonneg t (all_of_forall _ hf))] using ht

/-- Finite trees with equal laws assign equal probabilities to every predicate. -/
theorem probability_eq_of_law_eq (s t : Tree α) (h : s.law=t.law) (P : α → Prop) :
    s.probability P=t.probability P := by
  apply mean_eq_of_law_eq s t h
  intro a
  split_ifs <;> norm_num

/-- The probability of any predicate on a finite sampling tree is at most one. -/
theorem probability_le_one (t : Tree α) (P : α → Prop) : t.probability P≤1 := by
  calc
    t.probability P≤t.mean (fun _ => 1) := by
      apply mean_mono t
      apply all_of_forall
      intro a
      split_ifs <;> norm_num
    _=1 := mean_const t 1

/-- If two maps agree on every branch of a finite tree, their pushforwards of the tree law are
equal. -/
theorem law_map_congr {β : Type} (t : Tree α) (f g : α → β)
    (h : t.All (fun a => f a=g a)) : t.law.map f=t.law.map g := by
  induction t with
  | pure a =>
    change f a=g a at h
    simp only [law,PMF.pure_map,h]
  | sample m p c ih =>
    simp only [law,PMF.map_bind]
    apply congrArg (PMF.bind p)
    funext i
    exact ih i (h i)

end Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
