/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib
open Qatlib
open Matrix
open scoped Classical ComplexOrder

set_option autoImplicit false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
  set_option linter.unusedSimpArgs false in
set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib
open scoped Classical
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

def clause6Aux_counterGraph : MbqcGraph 4 where
  edges := {(0, 2), (0, 3), (1, 2), (1, 3)}

def clause6Aux_counterI : Finset (Fin 4) := (∅ : Finset (Fin 4))

def clause6Aux_counterO : Finset (Fin 4) := ({0} : Finset (Fin 4))

def clause6Aux_counterLam : Fin 4 → MbqcPlane := fun v => if v = 3 then .YZ else .XY

theorem clause6Aux_adj_zero (u : Fin 4) :
    mbqcAdj clause6Aux_counterGraph 0 u = true ↔ u = 2 ∨ u = 3 := by
  fin_cases u <;> decide

theorem clause6Aux_adj_one (u : Fin 4) :
    mbqcAdj clause6Aux_counterGraph 1 u = true ↔ u = 2 ∨ u = 3 := by
  fin_cases u <;> decide

theorem clause6Aux_adj_two (u : Fin 4) :
    mbqcAdj clause6Aux_counterGraph 2 u = true ↔ u = 0 ∨ u = 1 := by
  fin_cases u <;> decide

theorem clause6Aux_adj_three (u : Fin 4) :
    mbqcAdj clause6Aux_counterGraph 3 u = true ↔ u = 0 ∨ u = 1 := by
  fin_cases u <;> decide

theorem clause6Aux_odd_empty :
    mbqcOdd clause6Aux_counterGraph (∅ : Finset (Fin 4)) = (∅ : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_zero :
    mbqcOdd clause6Aux_counterGraph ({0} : Finset (Fin 4)) = ({2, 3} : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_one :
    mbqcOdd clause6Aux_counterGraph ({1} : Finset (Fin 4)) = ({2, 3} : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_two :
    mbqcOdd clause6Aux_counterGraph ({2} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_three :
    mbqcOdd clause6Aux_counterGraph ({3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_zero_one :
    mbqcOdd clause6Aux_counterGraph ({0, 1} : Finset (Fin 4)) = (∅ : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_zero_two :
    mbqcOdd clause6Aux_counterGraph ({0, 2} : Finset (Fin 4)) = (Finset.univ : Finset (Fin 4)) := by
  decide

theorem clause6Aux_odd_zero_three :
    mbqcOdd clause6Aux_counterGraph ({0, 3} : Finset (Fin 4)) = (Finset.univ : Finset (Fin 4)) := by
  decide

theorem clause6Aux_odd_one_three :
    mbqcOdd clause6Aux_counterGraph ({1, 3} : Finset (Fin 4)) = (Finset.univ : Finset (Fin 4)) := by
  decide

theorem clause6Aux_odd_two_three :
    mbqcOdd clause6Aux_counterGraph ({2, 3} : Finset (Fin 4)) = (∅ : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_zero_one_three :
    mbqcOdd clause6Aux_counterGraph ({0, 1, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_zero_two_three :
    mbqcOdd clause6Aux_counterGraph ({0, 2, 3} : Finset (Fin 4)) = ({2, 3} : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_one_two_three :
    mbqcOdd clause6Aux_counterGraph ({1, 2, 3} : Finset (Fin 4)) = ({2, 3} : Finset (Fin 4)) := by decide

theorem clause6Aux_odd_univ :
    mbqcOdd clause6Aux_counterGraph (Finset.univ : Finset (Fin 4)) = (∅ : Finset (Fin 4)) := by decide

theorem clause6Aux_plane_XY_of {mem odd : Bool} (h : mbqcGFlowPlaneCondB .XY mem odd = true) :
    mem = false ∧ odd = true := by
  cases mem <;> cases odd <;> simp [mbqcGFlowPlaneCondB] at h ⊢

theorem clause6Aux_plane_YZ_of {mem odd : Bool} (h : mbqcGFlowPlaneCondB .YZ mem odd = true) :
    mem = true ∧ odd = false := by
  cases mem <;> cases odd <;> simp [mbqcGFlowPlaneCondB] at h ⊢

theorem clause6Aux_notMem_of_decide {v : Fin 4} {S : Finset (Fin 4)}
    (h : decide (v ∈ S) = false) : v ∉ S := by
  rw [decide_eq_false_iff_not] at h
  exact h

theorem clause6Aux_mem_of_decide {v : Fin 4} {S : Finset (Fin 4)}
    (h : decide (v ∈ S) = true) : v ∈ S := by
  exact of_decide_eq_true h

theorem clause6Aux_shape_one
    (g : Fin 4 → Finset (Fin 4)) (r : Fin 4 → Fin 4)
    (h : mbqcGFlowCheck clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam g r) :
    ((r 1 : ℕ) < (r 2 : ℕ) ∧ (r 1 : ℕ) ≤ (r 0 : ℕ)) ∨
    ((r 1 : ℕ) < (r 3 : ℕ) ∧ (r 1 : ℕ) ≤ (r 0 : ℕ)) ∨
    ((r 1 : ℕ) < (r 0 : ℕ) ∧ (r 1 : ℕ) < (r 2 : ℕ) ∧ (r 1 : ℕ) ≤ (r 3 : ℕ)) ∨
    ((r 1 : ℕ) < (r 0 : ℕ) ∧ (r 1 : ℕ) < (r 3 : ℕ) ∧ (r 1 : ℕ) ≤ (r 2 : ℕ)) := by
  have h1 := h 1 (by decide : (1 : Fin 4) ∉ clause6Aux_counterO)
  obtain ⟨_, hA, hB, hC⟩ := h1
  have hC' : mbqcGFlowPlaneCondB (clause6Aux_counterLam 1) (decide ((1 : Fin 4) ∈ g 1))
      (decide ((1 : Fin 4) ∈ mbqcOdd clause6Aux_counterGraph (g 1))) = true := hC
  have hlam : clause6Aux_counterLam 1 = .XY := by decide
  rw [hlam] at hC'
  obtain ⟨hmem, hodd⟩ := clause6Aux_plane_XY_of hC'
  have h1not : (1 : Fin 4) ∉ g 1 := clause6Aux_notMem_of_decide hmem
  have h1in : (1 : Fin 4) ∈ mbqcOdd clause6Aux_counterGraph (g 1) := clause6Aux_mem_of_decide hodd
  by_cases h0 : (0 : Fin 4) ∈ g 1 <;> by_cases h2 : (2 : Fin 4) ∈ g 1 <;> by_cases h3 : (3 : Fin 4) ∈ g 1
  · have hEq : g 1 = ({0, 2, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    rw [hEq, clause6Aux_odd_zero_two_three] at h1in
    simp at h1in
  · have hEq : g 1 = ({0, 2} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    right; right; left
    have hA0 : mbqcRankPrec r 1 0 := hA 0 (by simp [h0]) (by decide)
    have hA2 : mbqcRankPrec r 1 2 := hA 2 (by simp [h2]) (by decide)
    have hB3 : ¬ mbqcRankPrec r 3 1 :=
      fun hc => hB 3 hc (by rw [hEq, clause6Aux_odd_zero_two]; simp)
    simp only [mbqcRankPrec] at hA0 hA2 hB3
    exact ⟨hA0, hA2, not_lt.mp hB3⟩
  · have hEq : g 1 = ({0, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    right; right; right
    have hA0 : mbqcRankPrec r 1 0 := hA 0 (by simp [h0]) (by decide)
    have hA3 : mbqcRankPrec r 1 3 := hA 3 (by simp [h3]) (by decide)
    have hB2 : ¬ mbqcRankPrec r 2 1 :=
      fun hc => hB 2 hc (by rw [hEq, clause6Aux_odd_zero_three]; simp)
    simp only [mbqcRankPrec] at hA0 hA3 hB2
    exact ⟨hA0, hA3, not_lt.mp hB2⟩
  · have hEq : g 1 = ({0} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    rw [hEq, clause6Aux_odd_zero] at h1in
    simp at h1in
  · have hEq : g 1 = ({2, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    rw [hEq, clause6Aux_odd_two_three] at h1in
    simp at h1in
  · have hEq : g 1 = ({2} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    left
    have hA2 : mbqcRankPrec r 1 2 := hA 2 (by simp [h2]) (by decide)
    have hB0 : ¬ mbqcRankPrec r 0 1 :=
      fun hc => hB 0 hc (by rw [hEq, clause6Aux_odd_two]; simp)
    simp only [mbqcRankPrec] at hA2 hB0
    exact ⟨hA2, not_lt.mp hB0⟩
  · have hEq : g 1 = ({3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    right; left
    have hA3 : mbqcRankPrec r 1 3 := hA 3 (by simp [h3]) (by decide)
    have hB0 : ¬ mbqcRankPrec r 0 1 :=
      fun hc => hB 0 hc (by rw [hEq, clause6Aux_odd_three]; simp)
    simp only [mbqcRankPrec] at hA3 hB0
    exact ⟨hA3, not_lt.mp hB0⟩
  · have hEq : g 1 = (∅ : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h1not, h0, h2, h3] at ⊢
    rw [hEq, clause6Aux_odd_empty] at h1in
    simp at h1in

theorem clause6Aux_shape_two
    (g : Fin 4 → Finset (Fin 4)) (r : Fin 4 → Fin 4)
    (h : mbqcGFlowCheck clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam g r) :
    ((r 2 : ℕ) < (r 0 : ℕ) ∧ (r 2 : ℕ) ≤ (r 3 : ℕ)) ∨
    ((r 2 : ℕ) < (r 1 : ℕ) ∧ (r 2 : ℕ) ≤ (r 3 : ℕ)) ∨
    ((r 2 : ℕ) < (r 0 : ℕ) ∧ (r 2 : ℕ) < (r 3 : ℕ) ∧ (r 2 : ℕ) ≤ (r 1 : ℕ)) ∨
    ((r 2 : ℕ) < (r 1 : ℕ) ∧ (r 2 : ℕ) < (r 3 : ℕ) ∧ (r 2 : ℕ) ≤ (r 0 : ℕ)) := by
  have h2 := h 2 (by decide : (2 : Fin 4) ∉ clause6Aux_counterO)
  obtain ⟨_, hA, hB, hC⟩ := h2
  have hC' : mbqcGFlowPlaneCondB (clause6Aux_counterLam 2) (decide ((2 : Fin 4) ∈ g 2))
      (decide ((2 : Fin 4) ∈ mbqcOdd clause6Aux_counterGraph (g 2))) = true := hC
  have hlam : clause6Aux_counterLam 2 = .XY := by decide
  rw [hlam] at hC'
  obtain ⟨hmem, hodd⟩ := clause6Aux_plane_XY_of hC'
  have h2not : (2 : Fin 4) ∉ g 2 := clause6Aux_notMem_of_decide hmem
  have h2in : (2 : Fin 4) ∈ mbqcOdd clause6Aux_counterGraph (g 2) := clause6Aux_mem_of_decide hodd
  by_cases h0 : (0 : Fin 4) ∈ g 2 <;> by_cases h1 : (1 : Fin 4) ∈ g 2 <;> by_cases h3 : (3 : Fin 4) ∈ g 2
  · have hEq : g 2 = ({0, 1, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    rw [hEq, clause6Aux_odd_zero_one_three] at h2in
    simp at h2in
  · have hEq : g 2 = ({0, 1} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    rw [hEq, clause6Aux_odd_zero_one] at h2in
    simp at h2in
  · have hEq : g 2 = ({0, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    right; right; left
    have hA0 : mbqcRankPrec r 2 0 := hA 0 (by simp [h0]) (by decide)
    have hA3 : mbqcRankPrec r 2 3 := hA 3 (by simp [h3]) (by decide)
    rw [hEq, clause6Aux_odd_zero_three] at h2in
    have hB1 : ¬ mbqcRankPrec r 1 2 :=
      fun hc => hB 1 hc (by rw [hEq, clause6Aux_odd_zero_three]; simp)
    simp only [mbqcRankPrec] at hA0 hA3 hB1
    exact ⟨hA0, hA3, not_lt.mp hB1⟩
  · have hEq : g 2 = ({0} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    left
    have hA0 : mbqcRankPrec r 2 0 := hA 0 (by simp [h0]) (by decide)
    rw [hEq, clause6Aux_odd_zero] at h2in
    have hB3 : ¬ mbqcRankPrec r 3 2 :=
      fun hc => hB 3 hc (by rw [hEq, clause6Aux_odd_zero]; simp)
    simp only [mbqcRankPrec] at hA0 hB3
    exact ⟨hA0, not_lt.mp hB3⟩
  · have hEq : g 2 = ({1, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    right; right; right
    have hA1 : mbqcRankPrec r 2 1 := hA 1 (by simp [h1]) (by decide)
    have hA3 : mbqcRankPrec r 2 3 := hA 3 (by simp [h3]) (by decide)
    rw [hEq, clause6Aux_odd_one_three] at h2in
    have hB0 : ¬ mbqcRankPrec r 0 2 :=
      fun hc => hB 0 hc (by rw [hEq, clause6Aux_odd_one_three]; simp)
    simp only [mbqcRankPrec] at hA1 hA3 hB0
    exact ⟨hA1, hA3, not_lt.mp hB0⟩
  · have hEq : g 2 = ({1} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    right; left
    have hA1 : mbqcRankPrec r 2 1 := hA 1 (by simp [h1]) (by decide)
    rw [hEq, clause6Aux_odd_one] at h2in
    have hB3 : ¬ mbqcRankPrec r 3 2 :=
      fun hc => hB 3 hc (by rw [hEq, clause6Aux_odd_one]; simp)
    simp only [mbqcRankPrec] at hA1 hB3
    exact ⟨hA1, not_lt.mp hB3⟩
  · have hEq : g 2 = ({3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    rw [hEq, clause6Aux_odd_three] at h2in
    simp at h2in
  · have hEq : g 2 = (∅ : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h2not, h0, h1, h3] at ⊢
    rw [hEq, clause6Aux_odd_empty] at h2in
    simp at h2in

theorem clause6Aux_shape_three
    (g : Fin 4 → Finset (Fin 4)) (r : Fin 4 → Fin 4)
    (h : mbqcGFlowCheck clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam g r) :
    ((r 3 : ℕ) ≤ (r 0 : ℕ) ∧ (r 3 : ℕ) ≤ (r 1 : ℕ)) ∨
    ((r 3 : ℕ) < (r 2 : ℕ)) ∨
    ((r 3 : ℕ) < (r 0 : ℕ) ∧ (r 3 : ℕ) < (r 1 : ℕ)) ∨
    ((r 3 : ℕ) < (r 0 : ℕ) ∧ (r 3 : ℕ) < (r 1 : ℕ) ∧ (r 3 : ℕ) < (r 2 : ℕ)) := by
  have h3 := h 3 (by decide : (3 : Fin 4) ∉ clause6Aux_counterO)
  obtain ⟨_, hA, hB, hC⟩ := h3
  have hC' : mbqcGFlowPlaneCondB (clause6Aux_counterLam 3) (decide ((3 : Fin 4) ∈ g 3))
      (decide ((3 : Fin 4) ∈ mbqcOdd clause6Aux_counterGraph (g 3))) = true := hC
  have hlam : clause6Aux_counterLam 3 = .YZ := by decide
  rw [hlam] at hC'
  obtain ⟨hmem, hodd⟩ := clause6Aux_plane_YZ_of hC'
  have h3in : (3 : Fin 4) ∈ g 3 := clause6Aux_mem_of_decide hmem
  have h3not : (3 : Fin 4) ∉ mbqcOdd clause6Aux_counterGraph (g 3) :=
      clause6Aux_notMem_of_decide hodd
  by_cases h0 : (0 : Fin 4) ∈ g 3 <;> by_cases h1 : (1 : Fin 4) ∈ g 3 <;> by_cases h2 : (2 : Fin 4) ∈ g 3
  · have hEq : g 3 = (Finset.univ : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    right; right; right
    have hA0 : mbqcRankPrec r 3 0 := hA 0 (by simp [h0]) (by decide)
    have hA1 : mbqcRankPrec r 3 1 := hA 1 (by simp [h1]) (by decide)
    have hA2 : mbqcRankPrec r 3 2 := hA 2 (by simp [h2]) (by decide)
    simp only [mbqcRankPrec] at hA0 hA1 hA2
    exact ⟨hA0, hA1, hA2⟩
  · have hEq : g 3 = ({0, 1, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    right; right; left
    have hA0 : mbqcRankPrec r 3 0 := hA 0 (by simp [h0]) (by decide)
    have hA1 : mbqcRankPrec r 3 1 := hA 1 (by simp [h1]) (by decide)
    simp only [mbqcRankPrec] at hA0 hA1
    exact ⟨hA0, hA1⟩
  · have hEq : g 3 = ({0, 2, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    rw [hEq, clause6Aux_odd_zero_two_three] at h3not
    simp at h3not
  · have hEq : g 3 = ({0, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    rw [hEq, clause6Aux_odd_zero_three] at h3not
    simp at h3not
  · have hEq : g 3 = ({1, 2, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    rw [hEq, clause6Aux_odd_one_two_three] at h3not
    simp at h3not
  · have hEq : g 3 = ({1, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    rw [hEq, clause6Aux_odd_one_three] at h3not
    simp at h3not
  · have hEq : g 3 = ({2, 3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    right; left
    have hA2 : mbqcRankPrec r 3 2 := hA 2 (by simp [h2]) (by decide)
    simp only [mbqcRankPrec] at hA2
    exact hA2
  · have hEq : g 3 = ({3} : Finset (Fin 4)) := by
      apply Finset.ext
      intro u
      fin_cases u <;> simp [Finset.mem_insert, Finset.mem_singleton, h3in, h0, h1, h2] at ⊢
    left
    rw [hEq, clause6Aux_odd_three] at h3not
    have hB0 : ¬ mbqcRankPrec r 0 3 :=
      fun hc => hB 0 hc (by rw [hEq, clause6Aux_odd_three]; simp)
    have hB1 : ¬ mbqcRankPrec r 1 3 :=
      fun hc => hB 1 hc (by rw [hEq, clause6Aux_odd_three]; simp)
    simp only [mbqcRankPrec] at hB0 hB1
    exact ⟨not_lt.mp hB0, not_lt.mp hB1⟩

theorem clause6Aux_counter_noCheck :
    ∀ (g : Fin 4 → Finset (Fin 4)) (r : Fin 4 → Fin 4),
      ¬ mbqcGFlowCheck clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam g r := by
  intro g r h
  rcases clause6Aux_shape_one g r h with s1 | s1 | s1 | s1 <;>
    rcases clause6Aux_shape_two g r h with s2 | s2 | s2 | s2 <;>
    rcases clause6Aux_shape_three g r h with s3 | s3 | s3 | s3 <;>
    omega

def clause6Aux_counterPrec : Fin 4 → Fin 4 → Prop :=
  fun u v => (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 1 ∧ v = 0)

instance clause6Aux_counterPrecDec : DecidableRel clause6Aux_counterPrec := by
  intro u v
  unfold clause6Aux_counterPrec
  infer_instance

theorem clause6Aux_counterPrec_strict : IsStrictOrder (Fin 4) clause6Aux_counterPrec where
  irrefl x h := by
    simp only [clause6Aux_counterPrec] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  trans {a b c} h1 h2 := by
    simp only [clause6Aux_counterPrec] at h1 h2
    rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp only [clause6Aux_counterPrec] <;> omega

def clause6Aux_counterG : Fin 4 → Finset (Fin 4)
  | 0 => (∅ : Finset (Fin 4))
  | 1 => ({2} : Finset (Fin 4))
  | 2 => ({0} : Finset (Fin 4))
  | 3 => ({3} : Finset (Fin 4))

theorem clause6_clause3b_counter_witness :
    MbqcHasGFlow clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam := by
  refine ⟨clause6Aux_counterG, clause6Aux_counterPrec, clause6Aux_counterPrecDec, ?_, clause6Aux_counterPrec_strict,
    ?_, ?_, ?_⟩
  · intro v hv u hu
    simp [clause6Aux_counterI]
  · intro v hv u hu hne
    have hvlit : v = (0 : Fin 4) ∨ v = (1 : Fin 4) ∨ v = (2 : Fin 4) ∨ v = (3 : Fin 4) := by
      fin_cases v <;> simp
    rcases hvlit with rfl | rfl | rfl | rfl
    · exact absurd (by decide : (0 : Fin 4) ∈ clause6Aux_counterO) hv
    · have : u = 2 := by
        simp only [clause6Aux_counterG] at hu
        simpa using! hu
      subst this
      simp only [clause6Aux_counterPrec]
      exact Or.inl ⟨by decide, by decide⟩
    · have : u = 0 := by
        simp only [clause6Aux_counterG] at hu
        simpa using! hu
      subst this
      simp only [clause6Aux_counterPrec]
      exact Or.inr (Or.inl ⟨by decide, by decide⟩)
    · have : u = 3 := by
        simp only [clause6Aux_counterG] at hu
        simpa using! hu
      subst this
      exact absurd rfl hne
  · intro v hv u hprec hu
    have hvlit : v = (0 : Fin 4) ∨ v = (1 : Fin 4) ∨ v = (2 : Fin 4) ∨ v = (3 : Fin 4) := by
      fin_cases v <;> simp
    rcases hvlit with rfl | rfl | rfl | rfl
    · exact absurd (by decide : (0 : Fin 4) ∈ clause6Aux_counterO) hv
    · simp only [clause6Aux_counterG, clause6Aux_odd_two] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · simp only [clause6Aux_counterPrec] at hprec
        rcases hprec with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · simp only [clause6Aux_counterPrec] at hprec
        rcases hprec with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · simp only [clause6Aux_counterG, clause6Aux_odd_zero] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · simp only [clause6Aux_counterPrec] at hprec
        rcases hprec with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · simp only [clause6Aux_counterPrec] at hprec
        rcases hprec with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · simp only [clause6Aux_counterG, clause6Aux_odd_three] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · simp only [clause6Aux_counterPrec] at hprec
        rcases hprec with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · simp only [clause6Aux_counterPrec] at hprec
        rcases hprec with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · intro v hv
    have hvlit : v = (0 : Fin 4) ∨ v = (1 : Fin 4) ∨ v = (2 : Fin 4) ∨ v = (3 : Fin 4) := by
      fin_cases v <;> simp
    rcases hvlit with rfl | rfl | rfl | rfl
    · exact absurd (by decide : (0 : Fin 4) ∈ clause6Aux_counterO) hv
    · have hlam : clause6Aux_counterLam 1 = .XY := by decide
      rw [hlam]
      simp only [mbqcGFlowPlaneCond, clause6Aux_counterG, clause6Aux_odd_two]
      simp [Finset.mem_insert, Finset.mem_singleton]
    · have hlam : clause6Aux_counterLam 2 = .XY := by decide
      rw [hlam]
      simp only [mbqcGFlowPlaneCond, clause6Aux_counterG, clause6Aux_odd_zero]
      simp [Finset.mem_insert, Finset.mem_singleton]
    · have hlam : clause6Aux_counterLam 3 = .YZ := by decide
      rw [hlam]
      simp only [mbqcGFlowPlaneCond, clause6Aux_counterG, clause6Aux_odd_three]
      simp [Finset.mem_insert, Finset.mem_singleton]

theorem clause6Aux_find_isSome_iff_exists {α : Type} (p : α → Bool) (l : List α) :
    (List.find? p l).isSome = true ↔ ∃ x ∈ l, p x = true := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
    exact ⟨a, List.mem_of_find?_eq_some ha, List.find?_some ha⟩
  · rintro ⟨x, hx, hp⟩
    cases hfind : List.find? p l with
    | none => exact absurd hp (List.find?_eq_none.mp hfind x hx)
    | some a => simp

theorem clause6_clause3b_complete_refuted :
    ¬ (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane),
        MbqcHasGFlow G I O lam → (mbqcGFlowDecide G I O lam).isSome = true) := by
  intro h
  have hform :
      mbqcGFlowDecide clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam =
        (Fintype.elems (α := (Fin 4 → Finset (Fin 4)) × (Fin 4 → Fin 4))).toList.find?
          (fun p => decide (mbqcGFlowCheck clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO
            clause6Aux_counterLam p.1 p.2)) := rfl
  have hsome := h 4 clause6Aux_counterGraph clause6Aux_counterI clause6Aux_counterO clause6Aux_counterLam
    clause6_clause3b_counter_witness
  rw [hform, clause6Aux_find_isSome_iff_exists] at hsome
  obtain ⟨p, _, hp⟩ := hsome
  exact clause6Aux_counter_noCheck p.1 p.2 (of_decide_eq_true hp)

theorem clause1_counter : ¬
    (  (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (a : Fin n → ℝ),
      MbqcHasFlow G I O → MbqcStronglyDeterministic G I O (fun _ => MbqcPlane.XY) a)

  ∧ (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n))
        (lam : Fin n → MbqcPlane) (a : Fin n → ℝ),
      MbqcHasGFlow G I O lam → MbqcStronglyDeterministic G I O lam a)

  ∧ (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)),
      (mbqcFlowDecide G I O).isSome = true ↔ MbqcHasFlow G I O)
  ∧ (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane),
      (mbqcGFlowDecide G I O lam).isSome = true ↔ MbqcHasGFlow G I O lam)

  ∧ (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (a : Fin n → ℝ),
      match mbqcFlowDecide G I O with
      | some (_, r) =>
          ∃ corr : (Fin n → Bool) → Fin n → Operator 2,
            (∀ s : Fin n → Bool, ∀ v : Fin n, MbqcPauliWire (corr s v)) ∧
            MbqcCausalCorrection (mbqcRankPrec r) corr ∧
            ∀ ρ : Operator (2 ^ I.card), IsDensityOperator ρ →
              ∀ s s' : Fin n → Bool,
                mbqcPatternBranch G I O r (fun _ => MbqcPlane.XY) a corr s ρ
                  = mbqcPatternBranch G I O r (fun _ => MbqcPlane.XY) a corr s' ρ
      | none => True)

  ∧ (¬ MbqcStronglyDeterministic mbqcCounterexampleGraph
        (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) (fun _ => MbqcPlane.XY)
        (fun _ => Real.pi / 2))) := by
  intro h
  exact clause6_clause3b_complete_refuted
    (fun n G I O lam hg => (h.2.2.2.1 n G I O lam).2 hg)

def clause6Aux_branchGraph : MbqcGraph 6 where
  edges := {(0, 3), (1, 4), (2, 3), (2, 4), (2, 5)}

def clause6Aux_branchI : Finset (Fin 6) := (∅ : Finset (Fin 6))

def clause6Aux_branchO : Finset (Fin 6) := ({3, 4, 5} : Finset (Fin 6))

def clause6Aux_branchA : Fin 6 → ℝ := fun _ => 0

def clause6Aux_branchFM : Fin 6 → Option (Fin 6) :=
  fun v =>
    if v = 0 then some 3
    else if v = 1 then some 4
    else if v = 2 then some 5
    else none

def clause6Aux_branchS0 : Fin 6 → Bool := fun _ => false

def clause6Aux_branchS1 : Fin 6 → Bool := fun v => decide (v = 0 ∨ v = 1)

def clause6Aux_branchR : Fin 6 → Fin 6 :=
  fun v => if v = 0 then 0 else if v = 1 then 0 else if v = 2 then 1 else 2

theorem clause6Aux_branch_card_I : clause6Aux_branchI.card = 0 := by
  simp [clause6Aux_branchI]

theorem clause6Aux_branch_card_O : clause6Aux_branchO.card = 3 := by
  simp [clause6Aux_branchO]

theorem clause6Aux_branchO_mem (v : Fin 6) : v ∈ clause6Aux_branchO ↔ v = 3 ∨ v = 4 ∨ v = 5 := by
  simp [clause6Aux_branchO]

theorem clause6Aux_branch_adj (u v : Fin 6) :
    mbqcAdj clause6Aux_branchGraph u v = true ↔
      (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨ (u = 1 ∧ v = 4) ∨ (u = 4 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨ (u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2) ∨
      (u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2) := by
  fin_cases u <;> fin_cases v <;> simp [mbqcAdj, clause6Aux_branchGraph]

theorem clause6Aux_branch_adj_zero {w : Fin 6} (h : mbqcAdj clause6Aux_branchGraph 0 w = true) :
    w = 3 := by
  rw [clause6Aux_branch_adj] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact h.2
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

theorem clause6Aux_branch_adj_one {w : Fin 6} (h : mbqcAdj clause6Aux_branchGraph 1 w = true) :
    w = 4 := by
  rw [clause6Aux_branch_adj] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact h.2
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

theorem clause6Aux_branch_adj_two {w : Fin 6} (h : mbqcAdj clause6Aux_branchGraph 2 w = true) :
    w = 3 ∨ w = 4 ∨ w = 5 := by
  rw [clause6Aux_branch_adj] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact Or.inl h.2
  · exact absurd h.1 (by simp)
  · exact Or.inr (Or.inl h.2)
  · exact absurd h.1 (by simp)
  · exact Or.inr (Or.inr h.2)
  · exact absurd h.1 (by simp)

theorem clause6Aux_branch_adj_three {k : Fin 6} (h : mbqcAdj clause6Aux_branchGraph 3 k = true) :
    k = 0 ∨ k = 2 := by
  rw [clause6Aux_branch_adj] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact absurd h.1 (by simp)
  · exact Or.inl h.2
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact Or.inr h.2
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

theorem clause6Aux_branch_adj_four {k : Fin 6} (h : mbqcAdj clause6Aux_branchGraph 4 k = true) :
    k = 1 ∨ k = 2 := by
  rw [clause6Aux_branch_adj] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact Or.inl h.2
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact Or.inr h.2
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

theorem clause6Aux_branch_adj_five {k : Fin 6} (h : mbqcAdj clause6Aux_branchGraph 5 k = true) :
    k = 2 := by
  rw [clause6Aux_branch_adj] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact h.2

theorem clause6Aux_branch_adj_03 : mbqcAdj clause6Aux_branchGraph 0 3 = true := by
  rw [clause6Aux_branch_adj]; exact Or.inl ⟨rfl, rfl⟩

theorem clause6Aux_branch_adj_14 : mbqcAdj clause6Aux_branchGraph 1 4 = true := by
  rw [clause6Aux_branch_adj]; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem clause6Aux_branch_adj_25 : mbqcAdj clause6Aux_branchGraph 2 5 = true := by
  rw [clause6Aux_branch_adj]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))

theorem clause6Aux_branch_adj_32 : mbqcAdj clause6Aux_branchGraph 3 2 = true := by
  rw [clause6Aux_branch_adj]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))

theorem clause6Aux_branch_adj_30 : mbqcAdj clause6Aux_branchGraph 3 0 = true := by
  rw [clause6Aux_branch_adj]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem clause6Aux_branch_adj_42 : mbqcAdj clause6Aux_branchGraph 4 2 = true := by
  rw [clause6Aux_branch_adj]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))

theorem clause6Aux_branch_adj_41 : mbqcAdj clause6Aux_branchGraph 4 1 = true := by
  rw [clause6Aux_branch_adj]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

theorem clause6Aux_branch_lt_antisymm {r : Fin 6 → Fin 6} {u v : Fin 6}
    (h1 : mbqcRankPrec r u v) (h2 : mbqcRankPrec r v u) : False := by
  simp only [mbqcRankPrec] at h1 h2
  omega

theorem clause6Aux_branch_forced {f : Fin 6 → Option (Fin 6)} {r : Fin 6 → Fin 6}
    (h : mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO f r) :
    clause6Aux_outMaskedFlow f clause6Aux_branchO = clause6Aux_branchFM := by
  have h0 : f 0 = some 3 := by
    obtain ⟨w, hfw, hadj, _, _, _⟩ := h 0 (by simp [clause6Aux_branchO])
    have hw : w = 3 := clause6Aux_branch_adj_zero hadj
    subst hw
    exact hfw
  have h1 : f 1 = some 4 := by
    obtain ⟨w, hfw, hadj, _, _, _⟩ := h 1 (by simp [clause6Aux_branchO])
    have hw : w = 4 := clause6Aux_branch_adj_one hadj
    subst hw
    exact hfw
  have h2 : f 2 = some 5 := by
    obtain ⟨w, hfw, hadj, _, _, hF3⟩ := h 2 (by simp [clause6Aux_branchO])
    rcases clause6Aux_branch_adj_two hadj with hw | hw | hw
    · subst hw
      obtain ⟨w0, hfw0, _, _, _, hF30⟩ := h 0 (by simp [clause6Aux_branchO])
      rw [h0] at hfw0
      cases hfw0
      have hA : mbqcRankPrec r 0 2 := hF30 2 clause6Aux_branch_adj_32 (by omega)
      have hB : mbqcRankPrec r 2 0 := hF3 0 clause6Aux_branch_adj_30 (by omega)
      exact (clause6Aux_branch_lt_antisymm hA hB).elim
    · subst hw
      obtain ⟨w1, hfw1, _, _, _, hF31⟩ := h 1 (by simp [clause6Aux_branchO])
      rw [h1] at hfw1
      cases hfw1
      have hA : mbqcRankPrec r 1 2 := hF31 2 clause6Aux_branch_adj_42 (by omega)
      have hB : mbqcRankPrec r 2 1 := hF3 1 clause6Aux_branch_adj_41 (by omega)
      exact (clause6Aux_branch_lt_antisymm hA hB).elim
    · subst hw
      exact hfw
  funext v
  fin_cases v <;> simp [clause6Aux_outMaskedFlow, clause6Aux_branchO, clause6Aux_branchFM, h0, h1, h2]

theorem clause6Aux_branch_check :
    mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO clause6Aux_branchFM clause6Aux_branchR := by
  intro v hv
  fin_cases v
  · refine ⟨3, rfl, clause6Aux_branch_adj_03, by simp [clause6Aux_branchI], ?_, ?_⟩
    · simp [mbqcRankPrec, clause6Aux_branchR]
    · intro k hk hkv
      rcases clause6Aux_branch_adj_three hk with hk' | hk'
      · exact absurd hk' hkv
      · subst hk'
        simp [mbqcRankPrec, clause6Aux_branchR]
  · refine ⟨4, rfl, clause6Aux_branch_adj_14, by simp [clause6Aux_branchI], ?_, ?_⟩
    · simp [mbqcRankPrec, clause6Aux_branchR]
    · intro k hk hkv
      rcases clause6Aux_branch_adj_four hk with hk' | hk'
      · exact absurd hk' hkv
      · subst hk'
        simp [mbqcRankPrec, clause6Aux_branchR]
  · refine ⟨5, rfl, clause6Aux_branch_adj_25, by simp [clause6Aux_branchI], ?_, ?_⟩
    · simp [mbqcRankPrec, clause6Aux_branchR]
    · intro k hk hkv
      exact absurd (clause6Aux_branch_adj_five hk) hkv
  · simp [clause6Aux_branchO] at hv
  · simp [clause6Aux_branchO] at hv
  · simp [clause6Aux_branchO] at hv

theorem clause6Aux_find_some_of_mem {α : Type} (p : α → Bool) (l : List α) (x : α)
    (hx : x ∈ l) (hp : p x = true) : ∃ y, l.find? p = some y ∧ p y = true := by
  cases hfind : l.find? p with
  | none =>
    exact absurd hp (List.find?_eq_none.mp hfind x hx)
  | some y =>
    exact ⟨y, rfl, List.find?_some hfind⟩

theorem clause6Aux_find_mem_complete {α : Type} [Fintype α] (x : α) :
    x ∈ (Fintype.elems (α := α)).toList :=
  Finset.mem_toList.mpr (Fintype.complete x)

theorem clause6Aux_branch_decider_some :
    ∃ p : (Fin 6 → Option (Fin 6)) × (Fin 6 → Fin 6),
      mbqcFlowDecide clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO = some p := by
  have hform :
      mbqcFlowDecide clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO =
        (Fintype.elems (α := (Fin 6 → Option (Fin 6)) × (Fin 6 → Fin 6))).toList.find?
          (fun q => decide (mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO q.1 q.2)) := rfl
  rw [hform]
  have hx : ((fun q => decide (mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO q.1 q.2))
      ((clause6Aux_branchFM, clause6Aux_branchR) : (Fin 6 → Option (Fin 6)) × (Fin 6 → Fin 6))) = true :=
    decide_eq_true clause6Aux_branch_check
  have hm : ((clause6Aux_branchFM, clause6Aux_branchR) : (Fin 6 → Option (Fin 6)) × (Fin 6 → Fin 6))
      ∈ (Fintype.elems (α := (Fin 6 → Option (Fin 6)) × (Fin 6 → Fin 6))).toList :=
    clause6Aux_find_mem_complete _
  obtain ⟨y, hy, _⟩ := clause6Aux_find_some_of_mem
    (fun q => decide (mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO q.1 q.2)) _ _ hm hx
  exact ⟨y, hy⟩

def clause6Aux_regSplit {n : ℕ} : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun z := (z 0, fun i => z i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv := by
    intro z
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv := by
    intro p
    obtain ⟨b, z⟩ := p
    refine Prod.ext rfl ?_
    funext i
    rfl

theorem clause6Aux_sum_prod_pi {n : ℕ} (h : Fin n → Bool → ℂ) :
    ∑ z : Fin n → Bool, ∏ i : Fin n, h i (z i) = ∏ i : Fin n, ∑ b : Bool, h i b := by
  induction n with
  | zero =>
    have hp : ∀ z : Fin 0 → Bool, (∏ i : Fin 0, h i (z i)) = 1 := fun _ => Fin.prod_univ_zero _
    rw [Finset.sum_congr rfl (fun z _ => hp z), Fin.prod_univ_zero]
    simp
  | succ n ih =>
    have hsplit : ∀ (b : Bool) (z' : Fin n → Bool),
        (∏ i : Fin (n + 1), h i (Fin.cases b z' i)) = h 0 b * ∏ i : Fin n, h i.succ (z' i) := by
      intro b z'
      rw [Fin.prod_univ_succ]
      rfl
    rw [← Equiv.sum_comp (clause6Aux_regSplit (n := n)).symm
      (fun z : Fin (n + 1) → Bool => ∏ i : Fin (n + 1), h i (z i))]
    rw [Fintype.sum_prod_type]
    simp only [clause6Aux_regSplit, Equiv.coe_fn_symm_mk, hsplit]
    have hinner : ∀ b : Bool,
        ∑ z' : Fin n → Bool, h 0 b * ∏ i : Fin n, h i.succ (z' i)
          = h 0 b * ∏ i : Fin n, ∑ b' : Bool, h i.succ b' := by
      intro b
      have key : ∑ z' : Fin n → Bool, ∏ i : Fin n, h i.succ (z' i)
          = ∏ i : Fin n, ∑ b' : Bool, h i.succ b' := ih _
      rw [← Finset.mul_sum, key]
    conv_lhs => simp only [hinner]
    rw [← Finset.sum_mul]
    have hprod : (∏ i : Fin (n + 1), ∑ b : Bool, h i b)
        = (∑ b : Bool, h 0 b) * ∏ i : Fin n, ∑ b' : Bool, h i.succ b' :=
      Fin.prod_univ_succ _
    rw [hprod]

theorem clause6Aux_boolEquivFin2_false : boolEquivFin2 false = 0 := rfl

theorem clause6Aux_boolEquivFin2_true : boolEquivFin2 true = 1 := rfl

theorem clause6Aux_pauliProductDensity_mul {n : ℕ} (f g : Fin n → Operator 2) :
    pauliProductDensity f * pauliProductDensity g
      = pauliProductDensity (fun i => f i * g i) := by
  ext x y
  simp only [pauliProductDensity, Matrix.of_apply, Matrix.mul_apply]
  simp only [← Finset.prod_mul_distrib]
  have hsumeq : (∑ z : Fin n → Bool,
        ∏ i : Fin n, f i (boolEquivFin2 (x i)) (boolEquivFin2 (z i))
          * g i (boolEquivFin2 (z i)) (boolEquivFin2 (y i)))
      = ∏ i : Fin n, ∑ b : Bool, f i (boolEquivFin2 (x i)) (boolEquivFin2 b)
          * g i (boolEquivFin2 b) (boolEquivFin2 (y i)) :=
    clause6Aux_sum_prod_pi (fun i t => f i (boolEquivFin2 (x i)) (boolEquivFin2 t)
      * g i (boolEquivFin2 t) (boolEquivFin2 (y i)))
  rw [hsumeq]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.sum_bool, Fin.sum_univ_two, clause6Aux_boolEquivFin2_false,
      clause6Aux_boolEquivFin2_true]
  exact add_comm _ _

def clause6Aux_branchRho : Operator (2 ^ clause6Aux_branchI.card) := 1

theorem clause6Aux_branchRho_density : IsDensityOperator clause6Aux_branchRho := by
  constructor
  · have h : clause6Aux_branchRho = (1 : Operator 1) := rfl
    rw [h]
    exact Matrix.PosSemidef.one
  · simp [clause6Aux_branchRho, Matrix.trace, clause6Aux_branchI]

theorem clause6Aux_check_of_find {α : Type} (p : α → Bool) (l : List α) (x : α)
    (h : l.find? p = some x) : p x = true := List.find?_some h

theorem clause6Aux_branch_refuted_skeleton
    (e0 : ∀ r : Fin 6 → Fin 6,
      (mbqcPatternBranch clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
        clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS0
        (1 : Operator (2 ^ clause6Aux_branchI.card))) 0 0 = 1)
    (e1 : ∀ r : Fin 6 → Fin 6,
      (mbqcPatternBranch clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
        clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS1
        (1 : Operator (2 ^ clause6Aux_branchI.card))) 0 0 = 0) :
    ¬ clause6Aux_clause4_branchObligation := by
  intro h
  specialize h 6 clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO clause6Aux_branchA
  obtain ⟨p, hp⟩ := clause6Aux_branch_decider_some
  obtain ⟨f, r⟩ := p
  rw [hp] at h
  have hcheck : mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO f r := by
    have hform :
        mbqcFlowDecide clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO =
          (Fintype.elems (α := (Fin 6 → Option (Fin 6)) × (Fin 6 → Fin 6))).toList.find?
            (fun q => decide (mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO q.1 q.2)) := rfl
    rw [hform] at hp
    exact of_decide_eq_true (clause6Aux_check_of_find
      (fun q : (Fin 6 → Option (Fin 6)) × (Fin 6 → Fin 6) =>
        decide (mbqcFlowCheck clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO q.1 q.2)) _ _ hp)
  have hfm : clause6Aux_outMaskedFlow f clause6Aux_branchO = clause6Aux_branchFM :=
      clause6Aux_branch_forced hcheck
  have heq := h 1 clause6Aux_branchRho_density clause6Aux_branchS0 clause6Aux_branchS1
  rw [hfm] at heq
  have heq00 :
      (mbqcPatternBranch clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
        clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS0
        (1 : Operator (2 ^ clause6Aux_branchI.card))) 0 0
      = (mbqcPatternBranch clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
        clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS1
        (1 : Operator (2 ^ clause6Aux_branchI.card))) 0 0 :=
    congrArg
      (fun M : Operator (2 ^ clause6Aux_branchO.card) => M (0 : Fin (2 ^ clause6Aux_branchO.card))
        (0 : Fin (2 ^ clause6Aux_branchO.card))) heq
  have v0 := e0 r
  have v1 := e1 r
  rw [v0, v1] at heq00
  exact absurd heq00 (by norm_num)

def clause6Aux_branch_entry_zero_obl : Prop :=
  ∀ r : Fin 6 → Fin 6,
    (mbqcPatternBranch clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
      clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS0
      (1 : Operator (2 ^ clause6Aux_branchI.card))) 0 0 = 1

def clause6Aux_branch_entry_one_obl : Prop :=
  ∀ r : Fin 6 → Fin 6,
    (mbqcPatternBranch clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
      clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS1
      (1 : Operator (2 ^ clause6Aux_branchI.card))) 0 0 = 0

theorem clause6Aux_clause4_branch_refuted_of_entries
    (h0 : clause6Aux_branch_entry_zero_obl) (h1 : clause6Aux_branch_entry_one_obl) :
    ¬ clause6Aux_clause4_branchObligation :=
  clause6Aux_branch_refuted_skeleton h0 h1

theorem clause6Aux_relabelGate_mul {n : ℕ} (A B : Matrix (Reg n) (Reg n) ℂ) :
    relabelGate (bitVecEquiv n) A * relabelGate (bitVecEquiv n) B
      = relabelGate (bitVecEquiv n) (A * B) := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact Equiv.sum_comp (bitVecEquiv n).symm
    (fun k => A ((bitVecEquiv n).symm i) k * B k ((bitVecEquiv n).symm j))

theorem clause6Aux_regWireGate_mul {n : ℕ} (v : Fin n) (A B : Operator 2) :
    mbqcRegWireGate v A * mbqcRegWireGate v B = mbqcRegWireGate v (A * B) := by
  rw [mbqcRegWireGate_eq, mbqcRegWireGate_eq, pauliProductDensity_mul]
  have h : (fun i : Fin n => (if i = v then A else 1) * (if i = v then B else 1))
      = (fun i : Fin n => if i = v then A * B else 1) := by
    funext i
    by_cases hi : i = v
    · subst hi
      simp
    · simp [hi]
  rw [h, mbqcRegWireGate_eq]

theorem clause6Aux_regWireGate_comm {n : ℕ} {v w : Fin n} (hvw : v ≠ w)
    (A B : Operator 2) :
    mbqcRegWireGate v A * mbqcRegWireGate w B
      = mbqcRegWireGate w B * mbqcRegWireGate v A := by
  rw [mbqcRegWireGate_eq, mbqcRegWireGate_eq, pauliProductDensity_mul,
    pauliProductDensity_mul]
  congr 1
  funext i
  by_cases hv : i = v
  · by_cases hw : i = w
    · exact absurd (hv.symm.trans hw) hvw
    · simp only [if_pos hv, if_neg hw, one_mul, mul_one]
  · by_cases hw : i = w
    · simp only [if_neg hv, if_pos hw, one_mul, mul_one]
    · simp only [if_neg hv, if_neg hw, one_mul]

theorem clause6Aux_wireGate_mul {n : ℕ} (v : Fin n) (A B : Operator 2) :
    mbqcWireGate v A * mbqcWireGate v B = mbqcWireGate v (A * B) := by
  unfold mbqcWireGate
  rw [clause6Aux_relabelGate_mul, clause6Aux_regWireGate_mul]

theorem clause6Aux_wireGate_comm {n : ℕ} {v w : Fin n} (hvw : v ≠ w) (A B : Operator 2) :
    mbqcWireGate v A * mbqcWireGate w B
      = mbqcWireGate w B * mbqcWireGate v A := by
  unfold mbqcWireGate
  rw [clause6Aux_relabelGate_mul, clause6Aux_relabelGate_mul, clause6Aux_regWireGate_comm hvw]

theorem clause6Aux_foldl_perm {n : ℕ} (g : Fin n → Matrix (Reg n) (Reg n) ℂ) :
    ∀ (L L' : List (Fin n)), L.Perm L' → ∀ (init : Matrix (Reg n) (Reg n) ℂ),
      (∀ a b : Fin n, a ∈ L → b ∈ L → g a * g b = g b * g a) →
      (∀ a : Fin n, a ∈ L → g a * init = init * g a) →
      L.foldl (fun acc v => g v * acc) init = L'.foldl (fun acc v => g v * acc) init := by
  intro L L' hp
  induction hp with
  | nil =>
    intro init _ _
    rfl
  | cons a _hp ih =>
    intro init hcomm hinit
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · intro b c hb hc
      exact hcomm b c (List.mem_cons_of_mem a hb) (List.mem_cons_of_mem a hc)
    · intro b hb
      have hba : g b * g a = g a * g b :=
        hcomm b a (List.mem_cons_of_mem a hb) List.mem_cons_self
      have hbi : g b * init = init * g b := hinit b (List.mem_cons_of_mem a hb)
      calc g b * (g a * init) = (g b * g a) * init := by rw [mul_assoc]
        _ = (g a * g b) * init := by rw [hba]
        _ = g a * (g b * init) := by rw [← mul_assoc]
        _ = g a * (init * g b) := by rw [hbi]
        _ = (g a * init) * g b := by rw [mul_assoc]
  | swap a b l =>
    intro init hcomm hinit
    simp only [List.foldl_cons]
    congr 1
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact hcomm a b (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
  | trans h1 h2 ih1 ih2 =>
    intro init hcomm hinit
    rw [ih1 init hcomm hinit]
    apply ih2
    · intro a b ha hb
      exact hcomm a b (h1.mem_iff.mpr ha) (h1.mem_iff.mpr hb)
    · intro a ha
      exact hinit a (h1.mem_iff.mpr ha)

theorem clause6Aux_xcond_s0 (u : Fin 6) :
    ¬(∃ v : Fin 6, clause6Aux_branchS0 v = true ∧ clause6Aux_branchFM v = some u) := by
  rintro ⟨v, hv, _⟩
  simp only [clause6Aux_branchS0] at hv
  nomatch hv

theorem clause6Aux_zcond_s0 (u : Fin 6) :
    ¬(∃ v w : Fin 6, clause6Aux_branchS0 v = true ∧ clause6Aux_branchFM v = some w
      ∧ u ≠ v ∧ mbqcAdj clause6Aux_branchGraph w u) := by
  rintro ⟨v, w, hv, _⟩
  simp only [clause6Aux_branchS0] at hv
  nomatch hv

theorem clause6Aux_corr_s0 (u : Fin 6) :
    flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS0 u = 1 := by
  unfold flowCorrection
  rw [if_neg (clause6Aux_xcond_s0 u), if_neg (clause6Aux_zcond_s0 u)]
  exact one_mul _

theorem clause6Aux_S1_of (v : Fin 6) (h : clause6Aux_branchS1 v = true) : v = 0 ∨ v = 1 := by
  unfold clause6Aux_branchS1 at h
  exact of_decide_eq_true h

theorem clause6Aux_xcond_s1 (u : Fin 6) :
    (∃ v : Fin 6, clause6Aux_branchS1 v = true ∧ clause6Aux_branchFM v = some u) ↔ u = 3 ∨ u = 4 := by
  constructor
  · intro ⟨v, hv, hf⟩
    rcases clause6Aux_S1_of v hv with rfl | rfl
    · have h3 : (3 : Fin 6) = u := by simpa [clause6Aux_branchFM] using! hf
      exact Or.inl h3.symm
    · have h4 : (4 : Fin 6) = u := by simpa [clause6Aux_branchFM] using! hf
      exact Or.inr h4.symm
  · intro h
    rcases h with h | h
    · exact ⟨0, by decide, by simp [clause6Aux_branchFM, h]⟩
    · exact ⟨1, by decide, by simp [clause6Aux_branchFM, h]⟩

theorem clause6Aux_adj_from_three (u : Fin 6) :
    mbqcAdj clause6Aux_branchGraph 3 u = true ↔ u = 0 ∨ u = 2 := by
  fin_cases u <;> simp [mbqcAdj, clause6Aux_branchGraph]

theorem clause6Aux_adj_from_four (u : Fin 6) :
    mbqcAdj clause6Aux_branchGraph 4 u = true ↔ u = 1 ∨ u = 2 := by
  fin_cases u <;> simp [mbqcAdj, clause6Aux_branchGraph]

theorem clause6Aux_zcond_s1 (u : Fin 6) :
    (∃ v w : Fin 6, clause6Aux_branchS1 v = true ∧ clause6Aux_branchFM v = some w
      ∧ u ≠ v ∧ mbqcAdj clause6Aux_branchGraph w u) ↔ u = 2 := by
  constructor
  · intro ⟨v, w, hv, hf, hne, hadj⟩
    rcases clause6Aux_S1_of v hv with rfl | rfl
    · have hw : (3 : Fin 6) = w := by simpa [clause6Aux_branchFM] using! hf
      subst hw
      rw [clause6Aux_adj_from_three] at hadj
      rcases hadj with h | h
      · exact absurd h hne
      · exact h
    · have hw : (4 : Fin 6) = w := by simpa [clause6Aux_branchFM] using! hf
      subst hw
      rw [clause6Aux_adj_from_four] at hadj
      rcases hadj with h | h
      · exact absurd h hne
      · exact h
  · intro h
    subst h
    exact ⟨0, 3, by decide, by simp [clause6Aux_branchFM], by simp,
      by simp [mbqcAdj, clause6Aux_branchGraph]⟩

theorem clause6Aux_corr_s1 (u : Fin 6) :
    flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS1 u =
      if u = 2 then pauliZ else if u = 3 then pauliX else if u = 4 then pauliX else 1 := by
  unfold flowCorrection
  rw [if_congr (clause6Aux_xcond_s1 u) (by rfl) (by rfl),
    if_congr (clause6Aux_zcond_s1 u) (by rfl) (by rfl)]
  fin_cases u <;> simp [pauliX, pauliZ]

theorem clause6Aux_corr_s1_0 : flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS1 0 = 1 := by
  have h2 : ¬((0 : Fin 6) = 2) := by decide
  have h3 : ¬((0 : Fin 6) = 3) := by decide
  have h4 : ¬((0 : Fin 6) = 4) := by decide
  rw [clause6Aux_corr_s1, if_neg h2, if_neg h3, if_neg h4]

theorem clause6Aux_corr_s1_1 : flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS1 1 = 1 := by
  have h2 : ¬((1 : Fin 6) = 2) := by decide
  have h3 : ¬((1 : Fin 6) = 3) := by decide
  have h4 : ¬((1 : Fin 6) = 4) := by decide
  rw [clause6Aux_corr_s1, if_neg h2, if_neg h3, if_neg h4]

theorem clause6Aux_corr_s1_2 : flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS1 2 = pauliZ := by
  rw [clause6Aux_corr_s1, if_pos rfl]

theorem clause6Aux_corr_s1_3 : flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS1 3 = pauliX := by
  have h2 : ¬((3 : Fin 6) = 2) := by decide
  rw [clause6Aux_corr_s1, if_neg h2, if_pos rfl]

theorem clause6Aux_corr_s1_4 : flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS1 4 = pauliX := by
  have h2 : ¬((4 : Fin 6) = 2) := by decide
  have h3 : ¬((4 : Fin 6) = 3) := by decide
  rw [clause6Aux_corr_s1, if_neg h2, if_neg h3, if_pos rfl]

theorem clause6Aux_corr_s1_5 : flowCorrection clause6Aux_branchGraph clause6Aux_branchFM clause6Aux_branchS1 5 = 1 := by
  have h2 : ¬((5 : Fin 6) = 2) := by decide
  have h3 : ¬((5 : Fin 6) = 3) := by decide
  have h4 : ¬((5 : Fin 6) = 4) := by decide
  rw [clause6Aux_corr_s1, if_neg h2, if_neg h3, if_neg h4]

theorem clause6Aux_plane0 (a b : Fin 2) :
    MbqcPlaneBasis MbqcPlane.XY 0 false a b = (2 : ℂ)⁻¹ := by
  have h : MbqcPlaneBasis MbqcPlane.XY 0 false
      = (2 : ℂ)⁻¹ • ((1 : Operator 2) + pauliX) := by
    unfold MbqcPlaneBasis
    rw [if_neg (by simp : ¬(false = true))]
    simp only [mbqcPlaneAxisA, mbqcPlaneAxisB]
    rw [Real.cos_zero, Real.sin_zero]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, add_zero]
  rw [h]
  fin_cases a <;> fin_cases b <;> simp [pauliX]

theorem clause6Aux_plane1 (a b : Fin 2) :
    MbqcPlaneBasis MbqcPlane.XY 0 true a b
      = if a = b then (2 : ℂ)⁻¹ else -(2 : ℂ)⁻¹ := by
  have h : MbqcPlaneBasis MbqcPlane.XY 0 true
      = (2 : ℂ)⁻¹ • ((1 : Operator 2) - pauliX) := by
    unfold MbqcPlaneBasis
    rw [if_pos rfl]
    simp only [mbqcPlaneAxisA, mbqcPlaneAxisB]
    rw [Real.cos_zero, Real.sin_zero]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, add_zero,
      neg_smul, sub_eq_add_neg]
  rw [h]
  fin_cases a <;> fin_cases b <;> simp [pauliX]

theorem clause6Aux_plane0Z (a b : Fin 2) :
    (MbqcPlaneBasis MbqcPlane.XY 0 false * pauliZ) a b
      = if b = 0 then (2 : ℂ)⁻¹ else -(2 : ℂ)⁻¹ := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases b <;> simp [clause6Aux_plane0, pauliZ]

theorem clause6Aux_px (a b : Fin 2) : pauliX a b = if a ≠ b then (1 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [pauliX]

noncomputable def clause6Aux_branchLocal (s : Fin 6 → Bool) : Fin 6 → Operator 2 :=
  fun v => if v ∈ clause6Aux_branchO then flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v
    else MbqcPlaneBasis MbqcPlane.XY 0 (s v) * flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v

theorem clause6Aux_local_s0 (v : Fin 6) (a b : Fin 2) :
    clause6Aux_branchLocal clause6Aux_branchS0 v a b
      = if v ∈ clause6Aux_branchO then (if a = b then (1 : ℂ) else 0) else (2 : ℂ)⁻¹ := by
  unfold clause6Aux_branchLocal
  by_cases hv : v ∈ clause6Aux_branchO
  · rw [if_pos hv, clause6Aux_corr_s0, Matrix.one_apply]
    simp [hv]
  · have hs : clause6Aux_branchS0 v = false := rfl
    rw [if_neg hv, hs, clause6Aux_corr_s0, mul_one, clause6Aux_plane0]
    simp [hv]

theorem clause6Aux_local_s1 (v : Fin 6) (a b : Fin 2) :
    clause6Aux_branchLocal clause6Aux_branchS1 v a b
      = if v = 0 ∨ v = 1 then (if a = b then (2 : ℂ)⁻¹ else -(2 : ℂ)⁻¹)
      else if v = 2 then (if b = 0 then (2 : ℂ)⁻¹ else -(2 : ℂ)⁻¹)
      else if v = 3 ∨ v = 4 then (if a ≠ b then (1 : ℂ) else 0)
      else (if a = b then (1 : ℂ) else 0) := by
  unfold clause6Aux_branchLocal
  have hO : ∀ w : Fin 6, w ∈ clause6Aux_branchO ↔ w = 3 ∨ w = 4 ∨ w = 5 := clause6Aux_branchO_mem
  by_cases h0 : v = 0
  · subst v
    have hs : clause6Aux_branchS1 0 = true := rfl
    rw [if_neg (by simp [hO]), clause6Aux_corr_s1_0, mul_one, hs, clause6Aux_plane1]
    simp
  · by_cases h1 : v = 1
    · subst v
      have hs : clause6Aux_branchS1 1 = true := rfl
      rw [if_neg (by simp [hO]), clause6Aux_corr_s1_1, mul_one, hs, clause6Aux_plane1]
      simp
    · by_cases h2 : v = 2
      · subst v
        have hs : clause6Aux_branchS1 2 = false := rfl
        rw [if_neg (by simp [hO]), hs, clause6Aux_corr_s1_2, clause6Aux_plane0Z]
        simp
      · by_cases h3 : v = 3
        · subst v
          rw [if_pos (by simp [hO]), clause6Aux_corr_s1_3, clause6Aux_px]
          simp
        · by_cases h4 : v = 4
          · subst v
            rw [if_pos (by simp [hO]), clause6Aux_corr_s1_4, clause6Aux_px]
            simp
          · by_cases h5 : v = 5
            · subst v
              rw [if_pos (by simp [hO]), clause6Aux_corr_s1_5, Matrix.one_apply]
              simp
            · omega

noncomputable def clause6Aux_czSign (y : Reg 6) : ℂ :=
  ∏ e ∈ clause6Aux_branchGraph.edges, if y e.1 && y e.2 then (-1 : ℂ) else 1

theorem clause6Aux_czSign_eq (y : Reg 6) :
    clause6Aux_czSign y =
      (if y 0 && y 3 then (-1 : ℂ) else 1) * (if y 1 && y 4 then (-1 : ℂ) else 1)
        * (if y 2 && y 3 then (-1 : ℂ) else 1) * (if y 2 && y 4 then (-1 : ℂ) else 1)
        * (if y 2 && y 5 then (-1 : ℂ) else 1) := by
  unfold clause6Aux_czSign
  show (∏ e ∈ ({(0, 3), (1, 4), (2, 3), (2, 4), (2, 5)} : Finset (Fin 6 × Fin 6)),
      if y e.1 && y e.2 then (-1 : ℂ) else 1) = _
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ring

def clause6Aux_rowZ (z : Fin 6 → Bool) : Reg 6 :=
  fun v => if v ∈ clause6Aux_branchO then false else z v

theorem clause6Aux_prod_delta (x y : Reg 6) :
    (∏ v : Fin 6, (if x v = y v then (1 : ℂ) else 0)) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst h
    simp
  · have hex : ∃ i : Fin 6, x i ≠ y i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := hex
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]

theorem clause6Aux_inFrame (x : Fin (2 ^ 6)) (y : Fin (2 ^ clause6Aux_branchI.card)) :
    mbqcInputFrame clause6Aux_branchI x y = ((2 : ℂ)⁻¹) ^ 3 := by
  have hI : ∀ v : Fin 6, ¬(v ∈ clause6Aux_branchI) := by
    intro v hv
    simp [clause6Aux_branchI] at hv
  unfold mbqcInputFrame
  simp only [Matrix.of_apply]
  have hp : (∏ v : Fin 6,
      (if h : v ∈ clause6Aux_branchI then
        if (bitVecEquiv 6).symm x v
            = (bitVecEquiv clause6Aux_branchI.card).symm y (clause6Aux_branchI.equivFin ⟨v, h⟩)
          then (1 : ℂ) else 0
      else (Real.sqrt 2 : ℂ)⁻¹))
      = (∏ v : Fin 6, (Real.sqrt 2 : ℂ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro v hv
    rw [dif_neg (hI v)]
  rw [hp, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hinv : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
    rw [inv_pow, hs]
  calc ((Real.sqrt 2 : ℂ)⁻¹) ^ 6 = (((Real.sqrt 2 : ℂ)⁻¹) ^ 2) ^ 3 := by ring
    _ = ((2 : ℂ)⁻¹) ^ 3 := by rw [hinv]

theorem clause6Aux_outFrame (z : Reg 6) (x : Fin (2 ^ 6)) :
    mbqcOutputFrame clause6Aux_branchO z 0 x
      = if (bitVecEquiv 6).symm x = clause6Aux_rowZ z then (1 : ℂ) else 0 := by
  have hz : (bitVecEquiv clause6Aux_branchO.card).symm 0 = (ZeroStr clause6Aux_branchO.card) :=
    (Equiv.symm_apply_eq (bitVecEquiv clause6Aux_branchO.card)).mpr (bitVecEquiv_zeroStr _).symm
  unfold mbqcOutputFrame
  simp only [Matrix.of_apply]
  have hp : (∏ v : Fin 6,
      (if h : v ∈ clause6Aux_branchO then
        if (bitVecEquiv 6).symm x v
            = (bitVecEquiv clause6Aux_branchO.card).symm 0 (clause6Aux_branchO.equivFin ⟨v, h⟩)
          then (1 : ℂ) else 0
        else if (bitVecEquiv 6).symm x v = z v then (1 : ℂ) else 0))
      = (∏ v : Fin 6,
        if (bitVecEquiv 6).symm x v = clause6Aux_rowZ z v then (1 : ℂ) else 0) := by
    apply Finset.prod_congr rfl
    intro v hv
    by_cases h : v ∈ clause6Aux_branchO
    · have hz1 : (bitVecEquiv clause6Aux_branchO.card).symm 0 (clause6Aux_branchO.equivFin ⟨v, h⟩)
          = false := by
        rw [hz]
        rfl
      have hrow : clause6Aux_rowZ z v = false := by
        unfold clause6Aux_rowZ
        rw [if_pos h]
      rw [dif_pos h, hz1, hrow]
    · have hrow : clause6Aux_rowZ z v = z v := by
        unfold clause6Aux_rowZ
        rw [if_neg h]
      rw [dif_neg h, hrow]
  rw [hp]
  exact clause6Aux_prod_delta _ _

theorem clause6Aux_foldl_perm_gen {n : ℕ} {ι : Type} [Fintype ι]
    (g : Fin n → Matrix ι ι ℂ) :
    ∀ (L L' : List (Fin n)), L.Perm L' → ∀ (init : Matrix ι ι ℂ),
      (∀ a b : Fin n, a ∈ L → b ∈ L → g a * g b = g b * g a) →
      (∀ a : Fin n, a ∈ L → g a * init = init * g a) →
      L.foldl (fun acc v => g v * acc) init = L'.foldl (fun acc v => g v * acc) init := by
  intro L L' hp
  induction hp with
  | nil =>
    intro init _ _
    rfl
  | cons a _hp ih =>
    intro init hcomm hinit
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · intro b c hb hc
      exact hcomm b c (List.mem_cons_of_mem a hb) (List.mem_cons_of_mem a hc)
    · intro b hb
      have hba : g b * g a = g a * g b :=
        hcomm b a (List.mem_cons_of_mem a hb) List.mem_cons_self
      have hbi : g b * init = init * g b := hinit b (List.mem_cons_of_mem a hb)
      calc g b * (g a * init) = (g b * g a) * init := by rw [mul_assoc]
        _ = (g a * g b) * init := by rw [hba]
        _ = g a * (g b * init) := by rw [← mul_assoc]
        _ = g a * (init * g b) := by rw [hbi]
        _ = (g a * init) * g b := by rw [mul_assoc]
  | swap a b l =>
    intro init hcomm hinit
    simp only [List.foldl_cons]
    congr 1
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact hcomm a b (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
  | trans h1 h2 ih1 ih2 =>
    intro init hcomm hinit
    rw [ih1 init hcomm hinit]
    apply ih2
    · intro a b ha hb
      exact hcomm a b (h1.mem_iff.mpr ha) (h1.mem_iff.mpr hb)
    · intro a ha
      exact hinit a (h1.mem_iff.mpr ha)

theorem clause6Aux_execOrder_eq (r : Fin 6 → Fin 6) :
    mbqcExecOrder clause6Aux_branchO r = ({0, 1, 2} : Finset (Fin 6)).sort (mbqcExecLe r) := by
  unfold mbqcExecOrder
  have h : (Finset.univ : Finset (Fin 6)) \ clause6Aux_branchO = ({0, 1, 2} : Finset (Fin 6)) := by
    decide
  rw [h]

theorem clause6Aux_execOrder_perm (r : Fin 6 → Fin 6) :
    (mbqcExecOrder clause6Aux_branchO r).Perm [0, 1, 2] := by
  apply Multiset.coe_eq_coe.mp
  rw [clause6Aux_execOrder_eq, Finset.sort_eq]
  exact (by decide : (([0, 1, 2] : List (Fin 6)) : Multiset (Fin 6))
    = ({0, 1, 2} : Finset (Fin 6)).val).symm

theorem clause6Aux_mem_three (a : Fin 6) (ha : a ∈ ({0, 1, 2} : Finset (Fin 6))) :
    a ∉ clause6Aux_branchO := by
  have h : a = 0 ∨ a = 1 ∨ a = 2 := by simpa using! ha
  rcases h with h | h | h <;> subst h <;> simp [clause6Aux_branchO]

noncomputable def clause6Aux_foldG (s : Fin 6 → Bool) : Fin 6 → Operator (2 ^ 6) :=
  fun v => mbqcWireGate v
    (MbqcPlaneBasis MbqcPlane.XY 0 (s v) * flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v)

noncomputable def clause6Aux_initG (s : Fin 6 → Bool) : Operator (2 ^ 6) :=
  relabelGate (bitVecEquiv 6)
    (pauliProductDensity fun v =>
      if v ∈ clause6Aux_branchO then flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v else 1)

theorem clause6Aux_foldG_eq (s : Fin 6 → Bool) (v : Fin 6) :
    clause6Aux_foldG s v = relabelGate (bitVecEquiv 6)
      (pauliProductDensity fun i => if i = v then
        MbqcPlaneBasis MbqcPlane.XY 0 (s v) * flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v
        else 1) := by
  unfold clause6Aux_foldG mbqcWireGate
  rw [mbqcRegWireGate_eq]

theorem clause6Aux_foldG_comm (s : Fin 6 → Bool) {a b : Fin 6} (hab : a ≠ b) :
    clause6Aux_foldG s a * clause6Aux_foldG s b = clause6Aux_foldG s b * clause6Aux_foldG s a :=
  clause6Aux_wireGate_comm hab _ _

theorem clause6Aux_foldG_init_comm (s : Fin 6 → Bool) (a : Fin 6) (ha : a ∉ clause6Aux_branchO) :
    clause6Aux_foldG s a * clause6Aux_initG s = clause6Aux_initG s * clause6Aux_foldG s a := by
  rw [clause6Aux_foldG_eq s a]
  show relabelGate (bitVecEquiv 6) _ * clause6Aux_initG s = clause6Aux_initG s * relabelGate
      (bitVecEquiv 6) _
  unfold clause6Aux_initG
  rw [clause6Aux_relabelGate_mul, clause6Aux_relabelGate_mul]
  congr 1
  rw [pauliProductDensity_mul, pauliProductDensity_mul]
  congr 1
  funext i
  by_cases hi : i = a
  · subst hi
    simp [ha]
  · simp [hi]

theorem clause6Aux_interleaved_eq (r : Fin 6 → Fin 6) (s : Fin 6 → Bool) :
    mbqcInterleavedGate clause6Aux_branchO r (fun _ => MbqcPlane.XY) clause6Aux_branchA
      (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s
      = relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s)) := by
  unfold mbqcInterleavedGate
  show (mbqcExecOrder clause6Aux_branchO r).foldl
      (fun acc v => mbqcWireGate v (MbqcPlaneBasis MbqcPlane.XY 0 (s v))
        * mbqcWireGate v (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v) * acc)
      (relabelGate (bitVecEquiv 6) (pauliProductDensity fun v =>
        if v ∈ clause6Aux_branchO then flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v else 1))
    = relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s))
  have hstep : (fun acc v => mbqcWireGate v (MbqcPlaneBasis MbqcPlane.XY 0 (s v))
        * mbqcWireGate v (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s v) * acc)
      = (fun acc v => clause6Aux_foldG s v * acc) := by
    funext acc v
    unfold clause6Aux_foldG
    rw [clause6Aux_wireGate_mul]
  rw [hstep]
  change (mbqcExecOrder clause6Aux_branchO r).foldl (fun acc v => clause6Aux_foldG s v * acc)
      (clause6Aux_initG s) = _
  have hcomm : ∀ a b : Fin 6, a ∈ mbqcExecOrder clause6Aux_branchO r → b ∈ mbqcExecOrder clause6Aux_branchO r
      → clause6Aux_foldG s a * clause6Aux_foldG s b = clause6Aux_foldG s b * clause6Aux_foldG s a := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab]
    · exact clause6Aux_foldG_comm s hab
  have hinit : ∀ a : Fin 6, a ∈ mbqcExecOrder clause6Aux_branchO r
      → clause6Aux_foldG s a * clause6Aux_initG s = clause6Aux_initG s * clause6Aux_foldG s a := by
    intro a ha
    have ha' : a ∈ ({0, 1, 2} : Finset (Fin 6)) := by
      rw [clause6Aux_execOrder_eq] at ha
      exact (Finset.mem_sort _).mp ha
    exact clause6Aux_foldG_init_comm s a (clause6Aux_mem_three a ha')
  have hreorder := clause6Aux_foldl_perm_gen (clause6Aux_foldG s) _ _ (clause6Aux_execOrder_perm r) (clause6Aux_initG s)
    hcomm hinit
  rw [hreorder]
  simp only [List.foldl_cons, List.foldl_nil]
  have hg2 : clause6Aux_foldG s 2 = relabelGate (bitVecEquiv 6)
      (pauliProductDensity fun i => if i = 2 then
        MbqcPlaneBasis MbqcPlane.XY 0 (s 2) * flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s 2
        else 1) := clause6Aux_foldG_eq s 2
  have hg1 : clause6Aux_foldG s 1 = relabelGate (bitVecEquiv 6)
      (pauliProductDensity fun i => if i = 1 then
        MbqcPlaneBasis MbqcPlane.XY 0 (s 1) * flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s 1
        else 1) := clause6Aux_foldG_eq s 1
  have hg0 : clause6Aux_foldG s 0 = relabelGate (bitVecEquiv 6)
      (pauliProductDensity fun i => if i = 0 then
        MbqcPlaneBasis MbqcPlane.XY 0 (s 0) * flowCorrection clause6Aux_branchGraph clause6Aux_branchFM s 0
        else 1) := clause6Aux_foldG_eq s 0
  rw [hg2, hg1, hg0]
  show relabelGate (bitVecEquiv 6) _
      * (relabelGate (bitVecEquiv 6) _ * (relabelGate (bitVecEquiv 6) _
        * relabelGate (bitVecEquiv 6) _))
      = relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s))
  rw [clause6Aux_relabelGate_mul, clause6Aux_relabelGate_mul, clause6Aux_relabelGate_mul]
  congr 1
  rw [pauliProductDensity_mul, pauliProductDensity_mul, pauliProductDensity_mul]
  congr 1
  funext i
  fin_cases i <;> simp [clause6Aux_branchLocal, clause6Aux_branchO_mem, mul_one, one_mul]

theorem clause6Aux_relabel_apply (M : Matrix (Reg 6) (Reg 6) ℂ) (i j : Fin (2 ^ 6)) :
    relabelGate (bitVecEquiv 6) M i j = M ((bitVecEquiv 6).symm i) ((bitVecEquiv 6).symm j) := by
  simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem clause6Aux_czDiag (x y : Reg 6) :
    czMatrix clause6Aux_branchGraph.edges x y = if x = y then clause6Aux_czSign x else 0 := by
  unfold clause6Aux_czSign
  simp [czMatrix, Matrix.diagonal_apply]

set_option maxHeartbeats 4000000 in

theorem clause6Aux_kraus_entry (r : Fin 6 → Fin 6) (s : Fin 6 → Bool) (z : Fin 6 → Bool) :
    (mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
      clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s z) 0 0
    = ((2 : ℂ)⁻¹) ^ 3 *
      ∑ y : Reg 6,
        pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) y * clause6Aux_czSign y := by
  have hrelabel : ∀ M : Matrix (Reg 6) (Reg 6) ℂ, ∀ i j : Fin (2 ^ 6),
      relabelGate (bitVecEquiv 6) M i j = M ((bitVecEquiv 6).symm i) ((bitVecEquiv 6).symm j) :=
    fun M i j => clause6Aux_relabel_apply M i j
  have hin : ∀ x : Fin (2 ^ 6), mbqcInputFrame clause6Aux_branchI x 0 = ((2 : ℂ)⁻¹) ^ 3 := fun x =>
    clause6Aux_inFrame x 0
  have hout : ∀ i : Fin (2 ^ 6), mbqcOutputFrame clause6Aux_branchO z 0 i
      = if (bitVecEquiv 6).symm i = clause6Aux_rowZ z then (1 : ℂ) else 0 := fun i =>
    clause6Aux_outFrame z i
  unfold mbqcPatternKraus
  rw [clause6Aux_interleaved_eq]
  show (mbqcOutputFrame clause6Aux_branchO z
      * relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s))
      * relabelGate (bitVecEquiv 6) (czMatrix clause6Aux_branchGraph.edges)
      * mbqcInputFrame clause6Aux_branchI) 0 0 = _
  simp only [Matrix.mul_apply]
  simp only [hout, hin]
  have hpick : ∀ j : Fin (2 ^ 6),
      (∑ i : Fin (2 ^ 6),
          (if (bitVecEquiv 6).symm i = clause6Aux_rowZ z then (1 : ℂ) else 0)
            * relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s)) i j)
        = relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s))
            (bitVecEquiv 6 (clause6Aux_rowZ z)) j := by
    intro j
    have hite : ∀ i : Fin (2 ^ 6),
        (if (bitVecEquiv 6).symm i = clause6Aux_rowZ z then (1 : ℂ) else 0)
            * relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s)) i j
          = (if i = bitVecEquiv 6 (clause6Aux_rowZ z) then
              relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s)) i j
              else 0) := by
      intro i
      by_cases h : (bitVecEquiv 6).symm i = clause6Aux_rowZ z
      · have hi : i = bitVecEquiv 6 (clause6Aux_rowZ z) :=
          (Equiv.symm_apply_eq (bitVecEquiv 6)).mp h
        rw [if_pos h, one_mul, if_pos hi]
      · have hi : ¬(i = bitVecEquiv 6 (clause6Aux_rowZ z)) := by
          intro hc
          exact h ((Equiv.symm_apply_eq (bitVecEquiv 6)).mpr hc)
        rw [if_neg h, zero_mul, if_neg hi]
    rw [Finset.sum_congr rfl (fun i _ => hite i)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin (2 ^ 6)))
      (bitVecEquiv 6 (clause6Aux_rowZ z))
      (fun i => relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s)) i j)]
    rw [if_pos (Finset.mem_univ _)]
  have hpoint : ∀ j k : Fin (2 ^ 6),
      relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s))
          (bitVecEquiv 6 (clause6Aux_rowZ z)) j
          * relabelGate (bitVecEquiv 6) (czMatrix clause6Aux_branchGraph.edges) j k
        = pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm j)
            * (if (bitVecEquiv 6).symm j = (bitVecEquiv 6).symm k then
                clause6Aux_czSign ((bitVecEquiv 6).symm j) else 0) := by
    intro j k
    rw [hrelabel, Equiv.symm_apply_apply, hrelabel, clause6Aux_czDiag]
  have hcoll : ∀ k : Fin (2 ^ 6),
      (∑ j : Fin (2 ^ 6),
          pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm j)
            * (if (bitVecEquiv 6).symm j = (bitVecEquiv 6).symm k then
                clause6Aux_czSign ((bitVecEquiv 6).symm j) else 0))
        = pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm k)
            * clause6Aux_czSign ((bitVecEquiv 6).symm k) := by
    intro k
    have hite : ∀ j : Fin (2 ^ 6),
        pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm j)
            * (if (bitVecEquiv 6).symm j = (bitVecEquiv 6).symm k then
                clause6Aux_czSign ((bitVecEquiv 6).symm j) else 0)
          = (if j = k then
              pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm k)
                * clause6Aux_czSign ((bitVecEquiv 6).symm k) else 0) := by
      intro j
      by_cases h : j = k
      · subst h
        rw [if_pos rfl]
        simp
      · have hs : ¬((bitVecEquiv 6).symm j = (bitVecEquiv 6).symm k) :=
          fun hc => h (Equiv.injective (bitVecEquiv 6).symm hc)
        rw [if_neg hs, mul_zero, if_neg h]
    rw [Finset.sum_congr rfl (fun j _ => hite j)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin (2 ^ 6))) k
      (fun _ => pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm k)
        * clause6Aux_czSign ((bitVecEquiv 6).symm k))]
    rw [if_pos (Finset.mem_univ _)]
  have hre : (∑ k : Fin (2 ^ 6),
        (∑ j : Fin (2 ^ 6),
            pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm j)
              * (if (bitVecEquiv 6).symm j = (bitVecEquiv 6).symm k then
                  clause6Aux_czSign ((bitVecEquiv 6).symm j) else 0))
          * (((2 : ℂ)⁻¹) ^ 3))
      = ((2 : ℂ)⁻¹) ^ 3 *
          ∑ y : Reg 6,
            pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) y * clause6Aux_czSign y := by
    have hstep : ∀ k : Fin (2 ^ 6),
        (∑ j : Fin (2 ^ 6),
            pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm j)
              * (if (bitVecEquiv 6).symm j = (bitVecEquiv 6).symm k then
                  clause6Aux_czSign ((bitVecEquiv 6).symm j) else 0))
          * (((2 : ℂ)⁻¹) ^ 3)
        = (pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm k)
            * clause6Aux_czSign ((bitVecEquiv 6).symm k)) * (((2 : ℂ)⁻¹) ^ 3) := by
      intro k
      exact congrArg (fun t : ℂ => t * (((2 : ℂ)⁻¹) ^ 3)) (hcoll k)
    have hmul : ∀ k : Fin (2 ^ 6),
        (pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm k)
            * clause6Aux_czSign ((bitVecEquiv 6).symm k))
          * (((2 : ℂ)⁻¹) ^ 3)
          = (((2 : ℂ)⁻¹) ^ 3)
              * (pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm k)
                * clause6Aux_czSign ((bitVecEquiv 6).symm k)) := by
      intro k
      ring
    rw [Finset.sum_congr rfl (fun k _ => hstep k)]
    rw [Finset.sum_congr rfl (fun k _ => hmul k), ← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (bitVecEquiv 6).symm
      (fun y : Reg 6 =>
        pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) y * clause6Aux_czSign y)
  have hexp :
      (∑ k : Fin (2 ^ 6),
          (∑ j : Fin (2 ^ 6),
              (∑ i : Fin (2 ^ 6),
                  (if (bitVecEquiv 6).symm i = clause6Aux_rowZ z then (1 : ℂ) else 0)
                    * relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s)) i j)
                * relabelGate (bitVecEquiv 6) (czMatrix clause6Aux_branchGraph.edges) j k)
            * (((2 : ℂ)⁻¹) ^ 3))
      = ((2 : ℂ)⁻¹) ^ 3 *
          ∑ y : Reg 6,
            pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) y * clause6Aux_czSign y := by
    have hstep : ∀ k : Fin (2 ^ 6),
        (∑ j : Fin (2 ^ 6),
            (∑ i : Fin (2 ^ 6),
                (if (bitVecEquiv 6).symm i = clause6Aux_rowZ z then (1 : ℂ) else 0)
                  * relabelGate (bitVecEquiv 6) (pauliProductDensity (clause6Aux_branchLocal s)) i j)
              * relabelGate (bitVecEquiv 6) (czMatrix clause6Aux_branchGraph.edges) j k)
          * (((2 : ℂ)⁻¹) ^ 3)
        = (∑ j : Fin (2 ^ 6),
            pauliProductDensity (clause6Aux_branchLocal s) (clause6Aux_rowZ z) ((bitVecEquiv 6).symm j)
              * (if (bitVecEquiv 6).symm j = (bitVecEquiv 6).symm k then
                  clause6Aux_czSign ((bitVecEquiv 6).symm j) else 0))
          * (((2 : ℂ)⁻¹) ^ 3) := by
      intro k
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hpick, hpoint]
    rw [Finset.sum_congr rfl (fun k _ => hstep k)]
    exact hre
  exact hexp

theorem clause6Aux_fin_subsingleton (x : Fin (2 ^ clause6Aux_branchI.card)) : x = 0 := by
  have hc : (2 ^ clause6Aux_branchI.card : ℕ) = 1 := by
    rw [clause6Aux_branch_card_I]
    norm_num
  have hval : x.val = 0 := by
    have hlt := x.isLt
    have hkey : x.val < 1 :=
      Nat.lt_of_lt_of_le hlt (Nat.le_of_eq hc)
    omega
  ext
  exact hval

theorem clause6Aux_sum_fin1 {α : Type} [AddCommMonoid α] (f : Fin (2 ^ clause6Aux_branchI.card) → α) :
    ∑ x, f x = f 0 := by
  rw [Finset.sum_eq_single (0 : Fin (2 ^ clause6Aux_branchI.card))]
  · intro x _ hx
    exact absurd (clause6Aux_fin_subsingleton x) hx
  · intro hx
    exact absurd (Finset.mem_univ _) hx

theorem clause6Aux_branch_entry_eq (s : Fin 6 → Bool) (r : Fin 6 → Fin 6) :
    (mbqcPatternBranch clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
      clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s
      (1 : Operator (2 ^ clause6Aux_branchI.card))) 0 0
    = ∑ z : Fin 6 → Bool,
      (mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
        clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s z) 0 0
        * star ((mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r
          (fun _ => MbqcPlane.XY) clause6Aux_branchA
          (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s z) 0 0) := by
  unfold mbqcPatternBranch mbqcPatternBranchMap
  simp only [LinearMap.sum_apply, conjBranch_apply]
  have hsum : ((∑ z : Fin 6 → Bool,
        (mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
          clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s z)
        * (1 : Operator (2 ^ clause6Aux_branchI.card))
        * (mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
          clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s z).conjTranspose) 0 0)
      = ∑ z : Fin 6 → Bool,
        (mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
          clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s z) 0 0
          * star ((mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r
            (fun _ => MbqcPlane.XY) clause6Aux_branchA
            (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) s z) 0 0) := by
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro z _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply]
    rw [clause6Aux_sum_fin1, clause6Aux_sum_fin1]
    rw [if_pos rfl]
    ring
  exact hsum

noncomputable def clause6Aux_s0K : Fin 6 → Bool → ℂ :=
  fun v b => if v ∈ clause6Aux_branchO then (if b = false then (1 : ℂ) else 0) else (2 : ℂ)⁻¹

noncomputable def clause6Aux_s1K (z : Fin 6 → Bool) : Fin 6 → Bool → ℂ :=
  fun v b =>
    if v = 0 then (2 : ℂ)⁻¹ * (if z 0 = false then (1 : ℂ) else -1)
    else if v = 1 then (2 : ℂ)⁻¹ * (if z 1 = false then (1 : ℂ) else -1)
    else if v = 2 then (2 : ℂ)⁻¹ * (if b then (-1 : ℂ) else 1)
    else if v = 3 then (if b then (1 : ℂ) else 0)
    else if v = 4 then (if b then (1 : ℂ) else 0)
    else (if b = false then (1 : ℂ) else 0)

theorem clause6Aux_localB_s0 (x y : Reg 6) :
    pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS0) x y
      = ∏ i : Fin 6,
        (if i ∈ clause6Aux_branchO then (if x i = y i then (1 : ℂ) else 0) else (2 : ℂ)⁻¹) := by
  unfold pauliProductDensity
  simp only [Matrix.of_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [clause6Aux_local_s0]
  by_cases hi : i ∈ clause6Aux_branchO
  · rw [if_pos hi, if_pos hi]
    by_cases he : x i = y i
    · rw [if_pos he]
      have hb : boolEquivFin2 (x i) = boolEquivFin2 (y i) := by rw [he]
      rw [if_pos hb]
    · have hb : ¬(boolEquivFin2 (x i) = boolEquivFin2 (y i)) :=
        fun h => he (boolEquivFin2.injective h)
      rw [if_neg he, if_neg hb]
  · rw [if_neg hi, if_neg hi]

theorem clause6Aux_localB_s1 (x y : Reg 6) :
    pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS1) x y
      = ∏ i : Fin 6,
        (if i = 0 ∨ i = 1 then (if x i = y i then (2 : ℂ)⁻¹ else -(2 : ℂ)⁻¹)
        else if i = 2 then (if y i = false then (2 : ℂ)⁻¹ else -(2 : ℂ)⁻¹)
        else if i = 3 ∨ i = 4 then (if x i ≠ y i then (1 : ℂ) else 0)
        else (if x i = y i then (1 : ℂ) else 0)) := by
  unfold pauliProductDensity
  simp only [Matrix.of_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [clause6Aux_local_s1]
  by_cases he : x i = y i
  · have hb : boolEquivFin2 (x i) = boolEquivFin2 (y i) := by rw [he]
    have hb0 : (boolEquivFin2 (y i) = 0) ↔ (y i = false) := by
      cases y i <;> simp [boolEquivFin2]
    by_cases h01 : i = 0 ∨ i = 1
    · rw [if_pos h01, if_pos h01, if_pos he, if_pos hb]
    · rw [if_neg h01, if_neg h01]
      by_cases h2 : i = 2
      · rw [if_pos h2, if_pos h2]
        rw [if_congr hb0 (by rfl) (by rfl)]
      · rw [if_neg h2, if_neg h2]
        by_cases h34 : i = 3 ∨ i = 4
        · rw [if_pos h34, if_pos h34,
            if_neg (fun h : boolEquivFin2 (x i) ≠ boolEquivFin2 (y i) => h hb),
            if_neg (fun h : x i ≠ y i => h he)]
        · rw [if_neg h34, if_neg h34, if_pos he, if_pos hb]
  · have hb : ¬(boolEquivFin2 (x i) = boolEquivFin2 (y i)) :=
      fun h => he (boolEquivFin2.injective h)
    have hb0 : (boolEquivFin2 (y i) = 0) ↔ (y i = false) := by
      cases y i <;> simp [boolEquivFin2]
    by_cases h01 : i = 0 ∨ i = 1
    · rw [if_pos h01, if_pos h01, if_neg he, if_neg hb]
    · rw [if_neg h01, if_neg h01]
      by_cases h2 : i = 2
      · rw [if_pos h2, if_pos h2]
        rw [if_congr hb0 (by rfl) (by rfl)]
      · rw [if_neg h2, if_neg h2]
        by_cases h34 : i = 3 ∨ i = 4
        · rw [if_pos h34, if_pos h34, if_pos he, if_pos hb]
        · rw [if_neg h34, if_neg h34, if_neg he, if_neg hb]

theorem clause6Aux_rowZ_of (z : Fin 6 → Bool) (i : Fin 6) (hi : i ∈ clause6Aux_branchO) :
    clause6Aux_rowZ z i = false := by
  unfold clause6Aux_rowZ
  rw [if_pos hi]

theorem clause6Aux_prod6 {α : Type} [CommMonoid α] (f : Fin 6 → α) :
    (∏ i : Fin 6, f i) = f 0 * (f 1 * (f 2 * (f 3 * (f 4 * f 5)))) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ,
    Fin.prod_univ_succ, Fin.prod_univ_one]
  have h5 : ((Fin.succ 0).succ.succ.succ.succ : Fin 6) = 5 := by decide
  have h4 : ((Fin.succ 0).succ.succ.succ : Fin 6) = 4 := by decide
  have h3 : ((Fin.succ 0).succ.succ : Fin 6) = 3 := by decide
  have h2 : ((Fin.succ 0).succ : Fin 6) = 2 := by decide
  have h1 : (Fin.succ 0 : Fin 6) = 1 := by decide
  rw [h5, h4, h3, h2, h1]

theorem clause6Aux_s0_ppd_zero (z : Fin 6 → Bool) (y : Reg 6) (i : Fin 6) (hi : i ∈ clause6Aux_branchO)
    (hy : y i = true) :
    pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS0) (clause6Aux_rowZ z) y = 0 := by
  rw [clause6Aux_localB_s0]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [if_pos hi, clause6Aux_rowZ_of z i hi, hy]
  simp

theorem clause6Aux_s0K_zero (y : Reg 6) (i : Fin 6) (hi : i ∈ clause6Aux_branchO) (hy : y i = true) :
    (∏ j : Fin 6, clause6Aux_s0K j (y j)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [clause6Aux_s0K, hi, hy]

theorem clause6Aux_s0_summand (z : Fin 6 → Bool) (y : Reg 6) :
    pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS0) (clause6Aux_rowZ z) y * clause6Aux_czSign y
      = ∏ i : Fin 6, clause6Aux_s0K i (y i) := by
  cases h3 : y 3 <;> cases h4 : y 4 <;> cases h5 : y 5
  · rw [clause6Aux_localB_s0]
    have hcz : clause6Aux_czSign y = 1 := by
      rw [clause6Aux_czSign_eq]
      simp [h3, h4, h5]
    rw [hcz, mul_one]
    have hp : ∀ i : Fin 6,
        (if i ∈ clause6Aux_branchO then (if clause6Aux_rowZ z i = y i then (1 : ℂ) else 0) else (2 : ℂ)⁻¹)
          = clause6Aux_s0K i (y i) := by
      intro i
      by_cases hi : i ∈ clause6Aux_branchO
      · have hfalse : y i = false := by
          rcases (clause6Aux_branchO_mem i).mp hi with h | h | h <;> subst h
          · exact h3
          · exact h4
          · exact h5
        rw [if_pos hi, clause6Aux_rowZ_of z i hi, hfalse]
        simp [clause6Aux_s0K, hi]
      · rw [if_neg hi]
        simp [clause6Aux_s0K, hi]
    rw [Finset.prod_congr rfl (fun i _ => hp i)]
  · rw [clause6Aux_s0_ppd_zero z y 5 (by simp [clause6Aux_branchO]) h5, zero_mul,
      clause6Aux_s0K_zero y 5 (by simp [clause6Aux_branchO]) h5]
  · rw [clause6Aux_s0_ppd_zero z y 4 (by simp [clause6Aux_branchO]) h4, zero_mul,
      clause6Aux_s0K_zero y 4 (by simp [clause6Aux_branchO]) h4]
  · rw [clause6Aux_s0_ppd_zero z y 4 (by simp [clause6Aux_branchO]) h4, zero_mul,
      clause6Aux_s0K_zero y 4 (by simp [clause6Aux_branchO]) h4]
  · rw [clause6Aux_s0_ppd_zero z y 3 (by simp [clause6Aux_branchO]) h3, zero_mul,
      clause6Aux_s0K_zero y 3 (by simp [clause6Aux_branchO]) h3]
  · rw [clause6Aux_s0_ppd_zero z y 3 (by simp [clause6Aux_branchO]) h3, zero_mul,
      clause6Aux_s0K_zero y 3 (by simp [clause6Aux_branchO]) h3]
  · rw [clause6Aux_s0_ppd_zero z y 3 (by simp [clause6Aux_branchO]) h3, zero_mul,
      clause6Aux_s0K_zero y 3 (by simp [clause6Aux_branchO]) h3]
  · rw [clause6Aux_s0_ppd_zero z y 3 (by simp [clause6Aux_branchO]) h3, zero_mul,
      clause6Aux_s0K_zero y 3 (by simp [clause6Aux_branchO]) h3]

theorem clause6Aux_s1_ppd_zero (z : Fin 6 → Bool) (y : Reg 6) (i : Fin 6) (hi : i = 3 ∨ i = 4)
    (hy : y i = false) :
    pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS1) (clause6Aux_rowZ z) y = 0 := by
  rw [clause6Aux_localB_s1]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with h | h
  · subst h
    have hc : ((3 : Fin 6) = 3) ∨ ((3 : Fin 6) = 4) := Or.inl rfl
    rw [if_pos hc, clause6Aux_rowZ_of z 3 (by simp [clause6Aux_branchO]), hy]
    simp
  · subst h
    have hc : ((4 : Fin 6) = 3) ∨ ((4 : Fin 6) = 4) := Or.inr rfl
    rw [if_pos hc, clause6Aux_rowZ_of z 4 (by simp [clause6Aux_branchO]), hy]
    simp

theorem clause6Aux_s1_ppd_zero5 (z : Fin 6 → Bool) (y : Reg 6) (hy : y 5 = true) :
    pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS1) (clause6Aux_rowZ z) y = 0 := by
  rw [clause6Aux_localB_s1]
  apply Finset.prod_eq_zero (Finset.mem_univ (5 : Fin 6))
  have hc1 : ¬(((5 : Fin 6) = 0) ∨ ((5 : Fin 6) = 1)) := by decide
  have hc2 : ¬((5 : Fin 6) = 2) := by decide
  have hc3 : ¬(((5 : Fin 6) = 3) ∨ ((5 : Fin 6) = 4)) := by decide
  rw [if_neg hc1, if_neg hc2, if_neg hc3, clause6Aux_rowZ_of z 5 (by simp [clause6Aux_branchO]), hy]
  simp

theorem clause6Aux_s1K_zero (z : Fin 6 → Bool) (y : Reg 6) (i : Fin 6) (hi : i = 3 ∨ i = 4)
    (hy : y i = false) :
    (∏ j : Fin 6, clause6Aux_s1K z j (y j)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with h | h <;> subst h <;> simp [clause6Aux_s1K, hy]

theorem clause6Aux_s1K_zero5 (z : Fin 6 → Bool) (y : Reg 6) (hy : y 5 = true) :
    (∏ j : Fin 6, clause6Aux_s1K z j (y j)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ (5 : Fin 6))
  simp [clause6Aux_s1K, hy]

set_option maxHeartbeats 4000000 in

theorem clause6Aux_s1_summand (z : Fin 6 → Bool) (y : Reg 6) :
    pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS1) (clause6Aux_rowZ z) y * clause6Aux_czSign y
      = ∏ i : Fin 6, clause6Aux_s1K z i (y i) := by
  cases h3 : y 3 <;> cases h4 : y 4 <;> cases h5 : y 5
  · rw [clause6Aux_s1_ppd_zero z y 3 (Or.inl rfl) h3, zero_mul,
      clause6Aux_s1K_zero z y 3 (Or.inl rfl) h3]
  · rw [clause6Aux_s1_ppd_zero z y 3 (Or.inl rfl) h3, zero_mul,
      clause6Aux_s1K_zero z y 3 (Or.inl rfl) h3]
  · rw [clause6Aux_s1_ppd_zero z y 3 (Or.inl rfl) h3, zero_mul,
      clause6Aux_s1K_zero z y 3 (Or.inl rfl) h3]
  · rw [clause6Aux_s1_ppd_zero z y 3 (Or.inl rfl) h3, zero_mul,
      clause6Aux_s1K_zero z y 3 (Or.inl rfl) h3]
  · rw [clause6Aux_s1_ppd_zero z y 4 (Or.inr rfl) h4, zero_mul,
      clause6Aux_s1K_zero z y 4 (Or.inr rfl) h4]
  · rw [clause6Aux_s1_ppd_zero z y 4 (Or.inr rfl) h4, zero_mul,
      clause6Aux_s1K_zero z y 4 (Or.inr rfl) h4]
  · rw [clause6Aux_localB_s1]
    cases hz0 : z 0 <;> cases hz1 : z 1 <;> cases hy0 : y 0 <;> cases hy1 : y 1 <;>
      cases hy2 : y 2
    all_goals
      simp only [clause6Aux_prod6, clause6Aux_czSign_eq]
      simp [clause6Aux_s1K, clause6Aux_rowZ, clause6Aux_branchO, h3, h4, h5, hz0, hz1, hy0, hy1,
          hy2]
  · rw [clause6Aux_s1_ppd_zero5 z y h5, zero_mul, clause6Aux_s1K_zero5 z y h5]

theorem clause6Aux_s0_sum (z : Fin 6 → Bool) :
    ∑ y : Reg 6, pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS0) (clause6Aux_rowZ z) y
        * clause6Aux_czSign y = 1 := by
  rw [Finset.sum_congr rfl (fun y _ => clause6Aux_s0_summand z y), clause6Aux_sum_prod_pi]
  apply Finset.prod_eq_one
  intro i _
  by_cases hi : i ∈ clause6Aux_branchO
  · simp [clause6Aux_s0K, hi]
  · simp [clause6Aux_s0K, hi]

theorem clause6Aux_s1_sum (z : Fin 6 → Bool) :
    ∑ y : Reg 6, pauliProductDensity (clause6Aux_branchLocal clause6Aux_branchS1) (clause6Aux_rowZ z) y
        * clause6Aux_czSign y = 0 := by
  rw [Finset.sum_congr rfl (fun y _ => clause6Aux_s1_summand z y), clause6Aux_sum_prod_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ (2 : Fin 6))
  simp [clause6Aux_s1K]

theorem clause6Aux_branch_entry_zero : clause6Aux_branch_entry_zero_obl := by
  intro r
  rw [clause6Aux_branch_entry_eq]
  have hk : ∀ z : Fin 6 → Bool,
      (mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
        clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS0 z) 0 0
        = ((2 : ℂ)⁻¹) ^ 3 := by
    intro z
    rw [clause6Aux_kraus_entry, clause6Aux_s0_sum, mul_one]
  simp only [hk]
  have hstar : star (((2 : ℂ)⁻¹) ^ 3) = ((2 : ℂ)⁻¹) ^ 3 := by
    rw [star_pow, star_inv₀, star_ofNat]
  simp only [hstar]
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (Fin 6 → Bool) = 64 := by
    simp [Fintype.card_bool, Fintype.card_fin]
  rw [hcard]
  norm_num

theorem clause6Aux_branch_entry_one : clause6Aux_branch_entry_one_obl := by
  intro r
  rw [clause6Aux_branch_entry_eq]
  have hk : ∀ z : Fin 6 → Bool,
      (mbqcPatternKraus clause6Aux_branchGraph clause6Aux_branchI clause6Aux_branchO r (fun _ => MbqcPlane.XY)
        clause6Aux_branchA (flowCorrection clause6Aux_branchGraph clause6Aux_branchFM) clause6Aux_branchS1 z) 0 0
        = 0 := by
    intro z
    rw [clause6Aux_kraus_entry, clause6Aux_s1_sum, mul_zero]
  simp only [hk]
  simp

theorem clause6Aux_clause4_branch_refuted : ¬ Qatlib.Concepts.MbqcFlow.FlowDecision.clause6Aux_clause4_branchObligation :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.clause6Aux_clause4_branch_refuted_of_entries
    Qatlib.Concepts.MbqcFlow.FlowDecision.clause6Aux_branch_entry_zero
    Qatlib.Concepts.MbqcFlow.FlowDecision.clause6Aux_branch_entry_one
end Qatlib.Concepts.MbqcFlow.FlowDecision
