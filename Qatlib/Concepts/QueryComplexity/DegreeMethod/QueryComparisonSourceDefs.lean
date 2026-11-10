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
set_option warningAsError false
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

def orFunction : (I → Bool) → Bool := fun g => ∃ i, g i = true

def orPolynomial : MvPolynomial I ℝ :=
  MvPolynomial.C 1 - (Finset.univ.prod fun i => (1 - MvPolynomial.X i : MvPolynomial I ℝ))

omit [DecidableEq I] in

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

def allElements (I : Type) [Fintype I] : List I := (Finset.univ : Finset I).toList

theorem allElements_length (I : Type) [Fintype I] :
    (allElements I).length = Fintype.card I := by
  rw [allElements, Finset.length_toList]
  exact Finset.card_univ

theorem allElements_mem (I : Type) [Fintype I] (i : I) : i ∈ allElements I := by
  rw [allElements, Finset.mem_toList]
  exact Finset.mem_univ i

def orScanTree : List I → BoolQueryTree I Bool
  | [] => .halt false
  | i :: is => .ask i (orScanTree is) (.halt true)

omit [Fintype I] [DecidableEq I] in

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

theorem orScanTree_maxQueries (l : List I) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries (orScanTree l) = l.length := by
  induction l with
  | nil => simp [orScanTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | cons i is ih =>
    rw [orScanTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries, ih]
    simp only [List.length_cons,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
    omega

def rejectProgram (p : (I × Bool) × W) : DecisionProgram I W where
  circuit := []
  initial := Ket p
  accept := ∅

def acceptProgram (p : (I × Bool) × W) : DecisionProgram I W where
  circuit := []
  initial := Ket p
  accept := {p}

omit [Fintype I] [Fintype W] in

theorem rejectProgram_queryCount (p : (I × Bool) × W) :
    QueryCount (rejectProgram p).circuit = 0 := rfl

omit [Fintype I] [Fintype W] in

theorem acceptProgram_queryCount (p : (I × Bool) × W) :
    QueryCount (acceptProgram p).circuit = 0 := rfl

theorem rejectProgram_successProb (p : (I × Bool) × W) (g : I → Bool) :
    (rejectProgram p).successProb g = 0 := by
  unfold DecisionProgram.successProb
  simp [rejectProgram, MeasureProb, Finset.sum_empty]

theorem acceptProgram_successProb (p : (I × Bool) × W) (g : I → Bool) :
    (acceptProgram p).successProb g = 1 := by
  unfold DecisionProgram.successProb
  simp [acceptProgram, MeasureProb, Ket, BornProb]

theorem rejectProgram_exact_false (p : (I × Bool) × W) :
    (rejectProgram p).ExactFor (fun _ => false) := by
  intro g
  rw [rejectProgram_successProb]
  simp

theorem acceptProgram_exact_true (p : (I × Bool) × W) :
    (acceptProgram p).ExactFor (fun _ => true) := by
  intro g
  rw [acceptProgram_successProb]
  simp

noncomputable def sourceQE (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.boundedCountSet f) : ℕ :=
  M.minBoundedQueries f h

noncomputable def sourceQ2 (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.successCountSet f) : ℕ :=
  M.minSuccessQueries f h

noncomputable def sourceQ0 (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.zeroErrorCountSet f) : ℕ :=
  M.minZeroErrorQueries f h

omit [DecidableEq I] in

theorem orPolynomial_represents : ∀ g : I → Bool,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval orPolynomial g = if orFunction g then (1 : ℝ) else 0 := by
  intro g
  have h1 := orPolynomial_eval g
  unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval
  show MvPolynomial.eval (oraclePoint g) orPolynomial = if orFunction g then (1 : ℝ) else 0
  rw [h1]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
