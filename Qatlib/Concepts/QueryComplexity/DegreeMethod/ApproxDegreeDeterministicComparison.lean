/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveClassicalSimulationBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ApproxPolynomialBlockSensitivityBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree

/-!
# Approximate degree and deterministic query complexity

This module compares the one-third approximate degree of a total Boolean function with its
deterministic decision tree complexity. Decision tree polynomials give one direction, while a
block sensitivity bound yields a sixth-power upper bound in the other direction, following the
polynomial method [BealsEtAl2001].

The affine conversion `tunableGoalConverted` places an approximating polynomial in the interval
from zero to one without increasing degree, at the cost of increasing its error to two-fifths.

## Main statements

* `tunableGoalApproxDegree_le_deterministic`: approximate degree is bounded by deterministic
  query complexity.
* `tunableGoalBlockSensitivity_le`: block sensitivity is at most six times the square of
  approximate degree.
* `stageB_query_comparison_clause74`: deterministic complexity is at most `216 * approxDegree f
  ^ 6`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

/-- The real acceptance polynomial recursively associated with a Boolean decision tree. -/
private noncomputable def tunableGoalTreePoly {n : ℕ} : BoolQueryTree (Fin n) Bool → MvPolynomial (Fin n) ℝ
  | .halt b => MvPolynomial.C (if b then (1 : ℝ) else 0)
  | .ask i onFalse onTrue =>
      (1 - MvPolynomial.X i) * tunableGoalTreePoly onFalse + MvPolynomial.X i * tunableGoalTreePoly onTrue

/-- Evaluating the decision tree polynomial at a Boolean input gives the zero-one encoding of
the tree output. -/
private theorem tunableGoalTreePoly_eval {n : ℕ} (t : BoolQueryTree (Fin n) Bool) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (tunableGoalTreePoly t)
      = if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) t).1 then (1 : ℝ) else 0 := by
  induction t with
  | halt b =>
    simp only [tunableGoalTreePoly, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run,
        MvPolynomial.eval_C]
    rfl
  | ask i onFalse onTrue ihF ihT =>
    have hrun : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun j => x j) (BoolQueryTree.ask i onFalse onTrue)).1
        = if x i then (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun j => x j) onTrue).1
        else (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun j => x j) onFalse).1 := by
      simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
      split_ifs <;> rfl
    rw [hrun]
    cases hx : x i <;>
      simp [tunableGoalTreePoly, hx, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        map_sub, map_one, MvPolynomial.eval_X, ihF, ihT]

/-- The total degree of the decision tree polynomial is at most the maximum number of queries in
the tree. -/
private theorem tunableGoalTreePoly_totalDegree {n : ℕ} (t : BoolQueryTree (Fin n) Bool) :
    (tunableGoalTreePoly t).totalDegree ≤ t.MaxQueries := by
  induction t with
  | halt b =>
    cases b <;>
      simp [tunableGoalTreePoly, MvPolynomial.totalDegree_one,
        MvPolynomial.totalDegree_zero, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | ask i onFalse onTrue ihF ihT =>
    have hsel : ((1 : MvPolynomial (Fin n) ℝ) - MvPolynomial.X i).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub _ _).trans <| by
        rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X]; norm_num
    have hmF : ((1 - MvPolynomial.X i) * tunableGoalTreePoly onFalse).totalDegree
        ≤ 1 + (tunableGoalTreePoly onFalse).totalDegree :=
      (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_right hsel _)
    have hmT : (MvPolynomial.X i * tunableGoalTreePoly onTrue).totalDegree
        ≤ 1 + (tunableGoalTreePoly onTrue).totalDegree :=
      (MvPolynomial.totalDegree_mul _ _).trans
        (by rw [MvPolynomial.totalDegree_X])
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
    exact max_le (hmF.trans (Nat.add_le_add_left (ihF.trans (le_max_left _ _)) _))
      (hmT.trans (Nat.add_le_add_left (ihT.trans (le_max_right _ _)) _))

/-- The decision tree that queries the listed coordinates, updates a base input with the
answers, and applies `leaf` to the resulting input. -/
private def tunableGoalTreeFrom {n : ℕ} (is : List (Fin n)) (base : Fin n → Bool)
    (leaf : (Fin n → Bool) → Bool) : BoolQueryTree (Fin n) Bool :=
  match is with
  | [] => BoolQueryTree.halt (leaf base)
  | i :: rest =>
      BoolQueryTree.ask i
        (tunableGoalTreeFrom rest (Function.update base i false) leaf)
        (tunableGoalTreeFrom rest (Function.update base i true) leaf)

/-- Running `tunableGoalTreeFrom` applies `leaf` to the input using queried values on the listed
coordinates and base values elsewhere. -/
private theorem tunableGoalTreeFrom_run {n : ℕ} (is : List (Fin n)) (base x : Fin n → Bool)
    (leaf : (Fin n → Bool) → Bool) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) (tunableGoalTreeFrom is base leaf)).1
      = leaf (fun j => if j ∈ is then x j else base j) := by
  induction is generalizing base with
  | nil => simp [tunableGoalTreeFrom, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
  | cons i rest ih =>
    have hrun : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun j => x j) (tunableGoalTreeFrom (i :: rest) base leaf)).1
        = if x i then
            (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun j => x j)
              (tunableGoalTreeFrom rest (Function.update base i true) leaf)).1
          else
            (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun j => x j)
              (tunableGoalTreeFrom rest (Function.update base i false) leaf)).1 := by
      simp only [tunableGoalTreeFrom,
          Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
      split_ifs <;> rfl
    rw [hrun]
    by_cases hx : x i = true
    · rw [if_pos hx, ih (Function.update base i true)]
      congr 1
      funext j
      by_cases hj : j = i <;> by_cases hjr : j ∈ rest <;>
        simp [hj, hjr, hx, List.mem_cons, Function.update_apply]
    · rw [if_neg hx, ih (Function.update base i false)]
      congr 1
      funext j
      by_cases hj : j = i <;> by_cases hjr : j ∈ rest <;>
        simp [hj, hjr, hx, List.mem_cons, Function.update_apply]

/-- The list of all coordinates of `Fin n` in their canonical order. -/
private def tunableGoalFullList (n : ℕ) : List (Fin n) := List.ofFn (fun i => i)

/-- Every coordinate belongs to `tunableGoalFullList n`. -/
private theorem tunableGoalFullList_mem (n : ℕ) (j : Fin n) : j ∈ tunableGoalFullList n :=
  List.mem_ofFn.mpr ⟨j, rfl⟩

/-- The decision tree computing `f` by querying every input coordinate. -/
private def tunableGoalExactTree {n : ℕ} (f : (Fin n → Bool) → Bool) : BoolQueryTree (Fin n) Bool :=
  tunableGoalTreeFrom (tunableGoalFullList n) (fun _ => false) f

/-- The full coordinate decision tree returns `f x` on every input `x`. -/
private theorem tunableGoalExactTree_exact {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) (tunableGoalExactTree f)).1 = f x := by
  rw [tunableGoalExactTree, tunableGoalTreeFrom_run]
  congr 1
  funext j
  simp [tunableGoalFullList_mem n j]

/-- The condition that a real polynomial approximates the zero-one encoding of `f` within
one-third at every Boolean input. -/
private def tunableGoalGood {n : ℕ} (f : (Fin n → Bool) → Bool) (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ g : Fin n → Bool,
    |MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0) p
      - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3

/-- The approximate degree is the infimum of total degrees of polynomials satisfying
`tunableGoalGood`. -/
private theorem tunableGoalApproxDegree_eq (n : ℕ) (f : (Fin n → Bool) → Bool) :
    approxDegree f
      = sInf ((fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) '' {p | tunableGoalGood f p}) :=
  rfl

/-- The set of total degrees of one-third approximating polynomials for a total Boolean function
is nonempty. -/
private theorem tunableGoalGood_nonempty (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ((fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) '' {p | tunableGoalGood f p}).Nonempty :=
  ⟨(tunableGoalTreePoly (tunableGoalExactTree f)).totalDegree,
    ⟨tunableGoalTreePoly (tunableGoalExactTree f), fun g => by
      rw [tunableGoalTreePoly_eval, tunableGoalExactTree_exact]
      simp, rfl⟩⟩

/-- The approximate degree of a function is at most the maximum query count of any decision tree
computing it exactly. -/
private theorem tunableGoalApproxDegree_le_budget {n : ℕ} (f : (Fin n → Bool) → Bool)
    (t : BoolQueryTree (Fin n) Bool)
    (ht : ∀ x : Fin n → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) t).1 = f x) :
    approxDegree f ≤ t.MaxQueries := by
  have hpoly : tunableGoalGood f (tunableGoalTreePoly t) := fun g => by
    rw [tunableGoalTreePoly_eval, ht g]
    simp
  have hmem : (tunableGoalTreePoly t).totalDegree
      ∈ (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) '' {p | tunableGoalGood f p} :=
    ⟨tunableGoalTreePoly t, hpoly, rfl⟩
  have hle := Nat.sInf_le (s := (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) ''
    {p | tunableGoalGood f p}) hmem
  rw [← tunableGoalApproxDegree_eq] at hle
  exact hle.trans (tunableGoalTreePoly_totalDegree t)

/-- The one-third approximate degree of a total Boolean function is at most its deterministic
query complexity. -/
private theorem tunableGoalApproxDegree_le_deterministic (n : ℕ) (f : (Fin n → Bool) → Bool) :
    approxDegree f ≤ deterministicQueryComplexity f := by
  have hne : (Set.range fun t : {t : BoolQueryTree (Fin n) Bool //
      ∀ x : Fin n → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) t).1 = f x} =>
      t.1.MaxQueries).Nonempty :=
    ⟨(tunableGoalExactTree f).MaxQueries, ⟨⟨tunableGoalExactTree f, tunableGoalExactTree_exact f⟩, rfl⟩⟩
  have hmem := Nat.sInf_mem hne
  rw [Set.mem_range] at hmem
  obtain ⟨⟨t, ht⟩, htd⟩ := hmem
  have htd' : t.MaxQueries = deterministicQueryComplexity f := htd
  exact (tunableGoalApproxDegree_le_budget f t ht).trans htd'.le

/-- If `y` is within one-third of a zero-one value, then `(1 + 3 * y) / 5` lies in `[0, 1]` and
is within two-fifths of that value. -/
private theorem tunableGoalConvert_range {y fbar : ℝ} (hf : fbar = 0 ∨ fbar = 1)
    (h : |y - fbar| ≤ 1 / 3) :
    0 ≤ (1 + 3 * y) / 5 ∧ (1 + 3 * y) / 5 ≤ 1 ∧
      |(1 + 3 * y) / 5 - fbar| ≤ 2 / 5 := by
  have h' := abs_le.mp h
  rcases hf with rfl | rfl
  · refine ⟨?_, ?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · refine ⟨?_, ?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

/-- The affine polynomial transformation `p ↦ 1 / 5 + (3 / 5) * p`. -/
private noncomputable def tunableGoalConverted {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 / 5) + MvPolynomial.C (3 / 5) * p

/-- At a Boolean input, the converted polynomial evaluates to `(1 + 3 * p.eval x) / 5`. -/
private theorem tunableGoalConverted_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (tunableGoalConverted p)
      = (1 + 3 * MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) / 5 := by
  simp [tunableGoalConverted, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  ring

/-- The affine conversion `tunableGoalConverted` does not increase total degree. -/
private theorem tunableGoalConverted_totalDegree {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    (tunableGoalConverted p).totalDegree ≤ p.totalDegree := by
  have hC : (MvPolynomial.C (3 / 5 : ℝ) : MvPolynomial (Fin n) ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  have hm : ((MvPolynomial.C (3 / 5 : ℝ) : MvPolynomial (Fin n) ℝ) * p).totalDegree
      ≤ p.totalDegree :=
    (MvPolynomial.totalDegree_mul _ _).trans (by rw [hC]; omega)
  have hadd := MvPolynomial.totalDegree_add
    (MvPolynomial.C (1 / 5 : ℝ) : MvPolynomial (Fin n) ℝ)
    (MvPolynomial.C (3 / 5 : ℝ) * p)
  rw [MvPolynomial.totalDegree_C] at hadd
  exact hadd.trans (max_le (Nat.zero_le _) hm)

/-- The block sensitivity of a total Boolean function is at most `6 * approxDegree f ^ 2`. -/
private theorem tunableGoalBlockSensitivity_le (n : ℕ) (f : (Fin n → Bool) → Bool) :
    blockSensitivity f ≤ 6 * approxDegree f ^ 2 := by
  obtain ⟨p, hp, hpd⟩ := (Set.mem_image (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree)
      {p | tunableGoalGood f p} _).mp
    (Nat.sInf_mem (s := (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) ''
      {p | tunableGoalGood f p}) (tunableGoalGood_nonempty n f))
  have hpd' : p.totalDegree = approxDegree f := hpd
  have hfb (x : Fin n → Bool) :
      (if f x then (1 : ℝ) else 0) = 0 ∨ (if f x then (1 : ℝ) else 0) = 1 := by
    cases f x <;> simp
  have hqeval : ∀ x : Fin n → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (tunableGoalConverted p) ∧
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (tunableGoalConverted p) ≤ 1 ∧
      |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (tunableGoalConverted p)
        - (if f x then (1 : ℝ) else 0)| ≤ 2 / 5 := by
    intro x
    rw [tunableGoalConverted_eval]
    exact tunableGoalConvert_range (hfb x) (hp x)
  have hqdeg : (tunableGoalConverted p).totalDegree ≤ approxDegree f := by
    rw [← hpd']
    exact tunableGoalConverted_totalDegree p
  have hmain := approximatePolynomialBlockSensitivity n f (tunableGoalConverted p) (2 / 5)
    (by norm_num) (by norm_num) hqeval
  have hconst1 : (1 - 2 * (2 / 5) : ℝ) = 1 / 5 := by norm_num
  have hconst2 : (2 - 2 * (2 / 5) : ℝ) = 6 / 5 := by norm_num
  rw [hconst1, hconst2] at hmain
  have hqd : ((tunableGoalConverted p).totalDegree : ℝ) ≤ (approxDegree f : ℝ) := by
    exact_mod_cast hqdeg
  have hqd2 : ((tunableGoalConverted p).totalDegree : ℝ) ^ 2 ≤ (approxDegree f : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hqd 2
  have hmain' : (1 / 5 : ℝ) * (blockSensitivity f : ℝ)
      ≤ (6 / 5) * (approxDegree f : ℝ) ^ 2 :=
    hmain.trans (mul_le_mul_of_nonneg_left hqd2 (by norm_num : (0 : ℝ) ≤ 6 / 5))
  have hbs : (blockSensitivity f : ℝ) ≤ 6 * (approxDegree f : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hmain' (by norm_num : (0 : ℝ) ≤ 5)
    ring_nf at this ⊢
    linarith
  exact_mod_cast hbs

/-- For every total Boolean function, approximate degree is at most deterministic query
complexity, which is at most `216 * approxDegree f ^ 6` [BealsEtAl2001]. -/
theorem stageB_query_comparison_clause74 :
  ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
    approxDegree f ≤ deterministicQueryComplexity f ∧
      deterministicQueryComplexity f ≤ 216 * approxDegree f ^ 6 := by
  intro n f
  constructor
  · exact tunableGoalApproxDegree_le_deterministic n f
  · have hbs := tunableGoalBlockSensitivity_le n f
    have hD := sensitivityDominanceCorollary n f
    have hmono : blockSensitivity f ^ 3 ≤ (6 * approxDegree f ^ 2) ^ 3 := by gcongr
    have hcon : (6 * approxDegree f ^ 2) ^ 3 = 216 * approxDegree f ^ 6 := by ring
    exact hD.trans (hmono.trans_eq hcon)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
