/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open scoped BigOperators Matrix
open Qatlib

noncomputable def CheckedSearchState {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (j : ℕ) : QState (I × Bool) :=
  Run (BitOracleOn (fun i => decide (i ∈ A))) (LiftCircuit (SearchCircuit I j))
    (WithMinus (Uniform I))

noncomputable def VerifyState {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Bool) (i : I) : QState (I × Bool) :=
  Run (BitOracleOn f) [Step.query] (Ket (i,false))

noncomputable def CheckedOutputMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (j : ℕ) (i : I) : ℝ :=
  (∑ b : Bool, BornProb (CheckedSearchState A j) (i,b)) *
    BornProb (VerifyState (fun x => decide (x ∈ A)) i) (i,true)

noncomputable def CheckedRejectMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (j : ℕ) : ℝ :=
  ∑ i, (∑ b : Bool, BornProb (CheckedSearchState A j) (i,b)) *
    BornProb (VerifyState (fun x => decide (x ∈ A)) i) (i,false)

theorem search_checked_attempt {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (j : ℕ) :
    QueryCount (LiftCircuit (SearchCircuit I j)) +
        QueryCount ([Step.query] : Circuit (I × Bool)) = j + 1 ∧
    (∀ i, CheckedOutputMass A j i = if i ∈ A then BornProb (SearchState A j) i else 0) ∧
    CheckedRejectMass A j = 1 - MeasureProb (SearchState A j) A ∧
    (∑ i, CheckedOutputMass A j i) + CheckedRejectMass A j = 1 ∧
    (∀ i, 0 ≤ CheckedOutputMass A j i) ∧ 0 ≤ CheckedRejectMass A j := by
  classical
  let f : I → Bool := fun i => decide (i ∈ A)
  have hverify (i : I) (b : Bool) : BornProb (VerifyState f i) (i,b) =
      if b = f i then 1 else 0 := by
    unfold VerifyState
    rw [run_query_bitOracleOn_ket]
    simp [bornProb_ket]
  have hmarginal (i : I) : (∑ b : Bool, BornProb (CheckedSearchState A j) (i,b)) =
      BornProb (SearchState A j) i := by
    have h := (search_bit_oracle_compile_phase f (SearchCircuit I j) (Uniform I)).2.2 {i}
    simpa only [CheckedSearchState, SearchState, Qatlib.Concepts.SearchStopping.KnownCount.GroverState,
      SetOracle, MeasureProb, Finset.sum_product, Finset.sum_singleton] using h
  have hout (i : I) : CheckedOutputMass A j i =
      if i ∈ A then BornProb (SearchState A j) i else 0 := by
    unfold CheckedOutputMass
    rw [hmarginal]
    change BornProb (SearchState A j) i * BornProb (VerifyState f i) (i,true) = _
    rw [hverify]
    by_cases hi : i ∈ A <;> simp [f, hi]
  have hreject : CheckedRejectMass A j =
      ∑ i, if i ∈ A then 0 else BornProb (SearchState A j) i := by
    unfold CheckedRejectMass
    apply Finset.sum_congr rfl
    intro i _
    rw [hmarginal]
    change BornProb (SearchState A j) i * BornProb (VerifyState f i) (i,false) = _
    rw [hverify]
    by_cases hi : i ∈ A <;> simp [f, hi]
  have hsum : (∑ i, CheckedOutputMass A j i) = MeasureProb (SearchState A j) A := by
    simp_rw [hout]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, MeasureProb]
  have htotal : (∑ i, CheckedOutputMass A j i) + CheckedRejectMass A j = 1 := by
    rw [hreject]
    simp_rw [hout]
    rw [← Finset.sum_add_distrib]
    have hs : (∑ i, ((if i ∈ A then BornProb (SearchState A j) i else 0) +
        (if i ∈ A then 0 else BornProb (SearchState A j) i))) =
        ∑ i, BornProb (SearchState A j) i := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [hs]
    exact (search_circuit_laws hN A j).2.2.2
  refine ⟨?_, hout, ?_, htotal, ?_, ?_⟩
  · rw [(search_bit_oracle_compile_phase f (SearchCircuit I j) (Uniform I)).1,
      (search_circuit_laws hN A j).1]
    simp
  · rw [hsum] at htotal
    linarith
  · intro i
    rw [hout]
    split_ifs
    · exact bornProb_nonneg _ _
    · exact le_rfl
  · rw [hreject]
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact bornProb_nonneg _ _

noncomputable def CheckedSuccess {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m : ℕ) : ℝ :=
  (∑ j ∈ Finset.range m, ∑ i, CheckedOutputMass A j i) / (m : ℝ)

noncomputable def CheckedFailure {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m : ℕ) : ℝ :=
  (∑ j ∈ Finset.range m, CheckedRejectMass A j) / (m : ℝ)

noncomputable def CheckedMeanQueries (I : Type*) [Fintype I] [DecidableEq I]
    (m : ℕ) : ℝ :=
  (∑ j ∈ Finset.range m,
    ((QueryCount (LiftCircuit (SearchCircuit I j)) +
      QueryCount ([Step.query] : Circuit (I × Bool)) : ℕ) : ℝ)) / (m : ℝ)

theorem search_checked_random_attempt {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (m : ℕ) (hm : 0 < m) :
    CheckedSuccess A m = RandomizedSuccess A m ∧
    CheckedFailure A m = 1 - CheckedSuccess A m ∧
    (0 ≤ CheckedSuccess A m ∧ 0 ≤ CheckedFailure A m) ∧
    CheckedMeanQueries I m = ((m : ℝ) + 1) / 2 := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmr
  have hout (j : ℕ) : (∑ i, CheckedOutputMass A j i) = MeasureProb (SearchState A j) A := by
    have h := search_checked_attempt hN A j
    linarith [h.2.2.1, h.2.2.2.1]
  have hs : CheckedSuccess A m = RandomizedSuccess A m := by
    unfold CheckedSuccess RandomizedSuccess
    simp_rw [hout]
  have ht : CheckedSuccess A m + CheckedFailure A m = 1 := by
    unfold CheckedSuccess CheckedFailure
    rw [← add_div, ← Finset.sum_add_distrib]
    simp_rw [(search_checked_attempt hN A _).2.2.2.1]
    simp [hmne]
  refine ⟨hs, by linarith, ⟨?_, ?_⟩, ?_⟩
  · unfold CheckedSuccess
    apply div_nonneg _ hmr.le
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact (search_checked_attempt hN A j).2.2.2.2.1 i
  · unfold CheckedFailure
    apply div_nonneg _ hmr.le
    apply Finset.sum_nonneg
    intro j _
    exact (search_checked_attempt hN A j).2.2.2.2.2
  · have hsum (n : ℕ) : (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ)) =
        (n : ℝ) * ((n : ℝ) + 1) / 2 := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    unfold CheckedMeanQueries
    have hcount (j : ℕ) : QueryCount (LiftCircuit (SearchCircuit I j)) +
        QueryCount ([Step.query] : Circuit (I × Bool)) = j + 1 :=
      (search_checked_attempt hN A j).1
    simp_rw [hcount]
    rw [hsum]
    field_simp

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
