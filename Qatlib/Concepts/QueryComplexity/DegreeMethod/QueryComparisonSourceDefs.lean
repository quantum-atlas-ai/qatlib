/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.PermutationLayerAverage
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeAndOr
import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrExactDegreeSubgoalBeal
import Qatlib.Concepts.QueryComplexity.AdversarySearch.OrZeroErrorQueryLowerBoundBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SymmetrizationAverageSubgoalBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Theorem46PrimeCaseRestrictedBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityExactLowerBoundRestrictedBeal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# OR polynomials and comparison-model programs

This module defines the Boolean function `orFunction`, its representing polynomial
`orPolynomial`, and the classical scan tree `orScanTree`. It proves polynomial evaluation and
degree bounds, scan correctness and query counts, and exact zero-query programs for constant
functions.

The definitions `sourceQE`, `sourceQ2`, and `sourceQ0` expose the selected finite-machine query
minima. These objects support comparisons with the polynomial method of [BealsEtAl2001].

## Main statements

* `orPolynomial_represents`: The product-form polynomial represents OR on Boolean inputs.
* `orPolynomial_totalDegree_le`: The OR polynomial has degree at most the input size.
* `orScanTree_run`: The scan tree detects a true bit in its index list.
* `orScanTree_maxQueries`: The maximum number of queries equals the list length.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The Boolean OR function on the finite input index type. -/
def orFunction : (I → Bool) → Bool := fun g => ∃ i, g i = true

/-- The real multivariate OR polynomial `1 - ∏ i, (1 - X i)`. -/
def orPolynomial : MvPolynomial I ℝ :=
  MvPolynomial.C 1 - (Finset.univ.prod fun i => (1 - MvPolynomial.X i : MvPolynomial I ℝ))

omit [DecidableEq I] in

/-- Evaluating the OR polynomial at a Boolean oracle point gives one for a true OR value and
zero otherwise. -/
theorem orPolynomial_eval (g : I → Bool) :
    MvPolynomial.eval (oraclePoint g) (orPolynomial) = if orFunction g then (1 : ℝ) else 0 := by
  unfold orPolynomial orFunction
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_C, MvPolynomial.eval_prod]
  by_cases h : ∃ i, g i = true
  · obtain ⟨i, hi⟩ := h
    have hx : ∃ i, g i = true := ⟨i, hi⟩
    have hmem : i ∈ (Finset.univ : Finset I) := Finset.mem_univ i
    have hfac : (1 - oraclePoint g i : ℝ) = 0 := by
      rw [oraclePoint]
      simp [hi]
    have hprod : ∏ j ∈ (Finset.univ : Finset I), (1 - oraclePoint g j : ℝ) = 0 :=
      Finset.prod_eq_zero hmem hfac
    simp [hx, hprod]
  · have hall : ∀ i ∈ (Finset.univ : Finset I), (1 - oraclePoint g i : ℝ) = 1 := by
      intro i _
      rw [oraclePoint]
      have : ¬ g i = true := by
        intro hcon
        exact h ⟨i, hcon⟩
      simp [this]
    have hprod : ∏ j ∈ (Finset.univ : Finset I), (1 - oraclePoint g j : ℝ) = 1 :=
      Finset.prod_eq_one hall
    simp [h, hprod]

/-- The total degree of the OR polynomial is at most the number of input indices. -/
theorem orPolynomial_totalDegree_le :
    (orPolynomial : MvPolynomial I ℝ).totalDegree ≤ Fintype.card I := by
  let P : MvPolynomial I ℝ :=
    (Finset.univ : Finset I).prod fun i => (1 - MvPolynomial.X i : MvPolynomial I ℝ)
  have hmul : ∀ i, ((1 - MvPolynomial.X i : MvPolynomial I ℝ)).totalDegree ≤ 1 :=
    fun i => one_sub_X_totalDegree_le i
  have hsum : P.totalDegree
      ≤ ∑ i ∈ (Finset.univ : Finset I), (1 - MvPolynomial.X i : MvPolynomial I ℝ).totalDegree := by
    exact MvPolynomial.totalDegree_finsetProd _ _
  have hcard : ∑ i ∈ (Finset.univ : Finset I), (1 - MvPolynomial.X i : MvPolynomial I ℝ).totalDegree
      ≤ Fintype.card I := by
    have hle : ∑ i ∈ (Finset.univ : Finset I),
          (1 - MvPolynomial.X i : MvPolynomial I ℝ).totalDegree
        ≤ ∑ _i ∈ (Finset.univ : Finset I), 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmul i
    have : ∑ _i ∈ (Finset.univ : Finset I), 1 = Fintype.card I := by simp
    rw [this] at hle
    exact hle
  have hdegP : P.totalDegree ≤ Fintype.card I := hsum.trans hcard
  have hnegP : (-P : MvPolynomial I ℝ).totalDegree ≤ P.totalDegree := by
    have h : (-P : MvPolynomial I ℝ) = (-1 : ℝ) • P := by simp
    rw [h]
    exact MvPolynomial.totalDegree_smul_le (-1) P
  have hsub : (MvPolynomial.C 1 - P : MvPolynomial I ℝ).totalDegree
      ≤ max (MvPolynomial.C 1 : MvPolynomial I ℝ).totalDegree P.totalDegree := by
    rw [sub_eq_add_neg]
    refine le_trans (MvPolynomial.totalDegree_add (MvPolynomial.C 1 : MvPolynomial I ℝ) (-P)) ?_
    exact max_le_max le_rfl hnegP
  have hone : (MvPolynomial.C 1 : MvPolynomial I ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C 1
  unfold orPolynomial
  rw [show (MvPolynomial.C 1 - (Finset.univ : Finset I).prod
      fun i => (1 - MvPolynomial.X i : MvPolynomial I ℝ) : MvPolynomial I ℝ)
      = MvPolynomial.C 1 - P by rfl]
  refine le_trans hsub ?_
  rw [hone, max_eq_right (Nat.zero_le _)]
  exact hdegP

/-- A list enumerating all elements of the finite type `I`. -/
def allElements (I : Type) [Fintype I] : List I := (Finset.univ : Finset I).toList

/-- The enumeration of all elements has length equal to the cardinality of `I`. -/
theorem allElements_length (I : Type) [Fintype I] :
    (allElements I).length = Fintype.card I := by
  rw [allElements, Finset.length_toList]
  exact Finset.card_univ

/-- Every element of `I` appears in `allElements I`. -/
theorem allElements_mem (I : Type) [Fintype I] (i : I) : i ∈ allElements I := by
  rw [allElements, Finset.mem_toList]
  exact Finset.mem_univ i

/-- The decision tree that scans the listed indices until a true bit is found, returning false
if the list is exhausted. -/
def orScanTree : List I → BoolQueryTree I Bool
  | [] => .halt false
  | i :: is => .ask i (orScanTree is) (.halt true)

omit [Fintype I] [DecidableEq I] in

/-- The scan tree returns true exactly when at least one index in its list has a true input bit. -/
theorem orScanTree_run (l : List I) (g : I → Bool) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (orScanTree l)).1 = true ↔ ∃ i ∈ l, g i = true := by
  induction l with
  | nil => simp [orScanTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
  | cons i is ih =>
    rw [orScanTree]
    by_cases hgi : g i = true
    · have hsel : (if g i = true then Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (BoolQueryTree.halt true)
            else Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (orScanTree is)).1
          = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (BoolQueryTree.halt true)).1 := by
        simp [hgi]
      rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hsel]
      rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
      constructor
      · intro _
        exact ⟨i, by simp, hgi⟩
      · intro _
        trivial
    · have hgi' : g i = false := Bool.eq_false_of_not_eq_true hgi
      have hsel : (if g i = true then Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (BoolQueryTree.halt true)
            else Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (orScanTree is)).1
          = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (orScanTree is)).1 := by
        simp [hgi]
      rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hsel, ih]
      simp only [List.mem_cons]
      constructor
      · intro h
        rcases h with ⟨j, hj, hgj⟩
        exact ⟨j, Or.inr hj, hgj⟩
      · intro h
        rcases h with ⟨j, hj, hgj⟩
        rcases hj with rfl | hj
        · exact absurd hgj hgi
        · exact ⟨j, hj, hgj⟩

omit [Fintype I] [DecidableEq I] in

/-- The maximum query count of the scan tree is the length of its index list. -/
theorem orScanTree_maxQueries (l : List I) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries (orScanTree l) = l.length := by
  induction l with
  | nil => simp [orScanTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | cons i is ih =>
    rw [orScanTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries, ih]
    simp only [List.length_cons,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
    omega

/-- A zero-query decision program initialized at the basis state `p` with an empty accepting
event. -/
def rejectProgram (p : (I × Bool) × W) : DecisionProgram I W where
  circuit := []
  initial := Ket p
  accept := ∅

/-- A zero-query decision program initialized at the basis state `p` and accepting that basis
outcome. -/
def acceptProgram (p : (I × Bool) × W) : DecisionProgram I W where
  circuit := []
  initial := Ket p
  accept := {p}

omit [Fintype I] [Fintype W] in

/-- The constant-reject program uses zero queries. -/
theorem rejectProgram_queryCount (p : (I × Bool) × W) :
    QueryCount (rejectProgram p).circuit = 0 := rfl

omit [Fintype I] [Fintype W] in

/-- The constant-accept program uses zero queries. -/
theorem acceptProgram_queryCount (p : (I × Bool) × W) :
    QueryCount (acceptProgram p).circuit = 0 := rfl

/-- The acceptance probability of the constant-reject program is zero on every oracle. -/
theorem rejectProgram_successProb (p : (I × Bool) × W) (g : I → Bool) :
    (rejectProgram p).successProb g = 0 := by
  unfold DecisionProgram.successProb
  simp [rejectProgram, MeasureProb, Finset.sum_empty]

/-- The acceptance probability of the constant-accept program is one on every oracle. -/
theorem acceptProgram_successProb (p : (I × Bool) × W) (g : I → Bool) :
    (acceptProgram p).successProb g = 1 := by
  unfold DecisionProgram.successProb
  simp [acceptProgram, MeasureProb, Ket, BornProb]

/-- The constant-reject program exactly computes the constant-false function. -/
theorem rejectProgram_exact_false (p : (I × Bool) × W) :
    (rejectProgram p).ExactFor (fun _ => false) := by
  intro g
  rw [rejectProgram_successProb]
  simp

/-- The constant-accept program exactly computes the constant-true function. -/
theorem acceptProgram_exact_true (p : (I × Bool) × W) :
    (acceptProgram p).ExactFor (fun _ => true) := by
  intro g
  rw [acceptProgram_successProb]
  simp

/-- The selected machine class's minimum query count under `BoundedFor`, given a nonempty
bounded count set. -/
noncomputable def sourceQE (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.boundedCountSet f) : ℕ :=
  M.minBoundedQueries f h

/-- The selected machine class's minimum query count under `SuccessFor`, given a nonempty
success count set. -/
noncomputable def sourceQ2 (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.successCountSet f) : ℕ :=
  M.minSuccessQueries f h

/-- The selected machine class's minimum query count under `ZeroErrorFor`, given a nonempty
zero-error count set. -/
noncomputable def sourceQ0 (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.zeroErrorCountSet f) : ℕ :=
  M.minZeroErrorQueries f h

omit [DecidableEq I] in

/-- The OR polynomial represents `orFunction` under Boolean evaluation [BealsEtAl2001]. -/
theorem orPolynomial_represents : ∀ g : I → Bool,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval orPolynomial g = if orFunction g then (1 : ℝ) else 0 := by
  intro g
  have h1 := orPolynomial_eval g
  unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval
  show MvPolynomial.eval (oraclePoint g) orPolynomial = if orFunction g then (1 : ℝ) else 0
  rw [h1]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
