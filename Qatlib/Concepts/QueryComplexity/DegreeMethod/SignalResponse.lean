/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseDefs
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.AdaptiveSignalTree
open Qatlib.Concepts.QueryComplexity.DegreeMethod.OracleAccessModel
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalBranchLaw
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponse

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators ComplexOrder ENNReal Matrix.Norms.L2Operator
set_option warningAsError false

private theorem isometry_norm_le_one {H O : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] {L : Matrix H O ℂ} (h : IsIsometry L) :
    ‖L‖ ≤ 1 := by
  have hsq : ‖L‖ * ‖L‖ = ‖(1 : Matrix O O ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self L, h]
  have h1 : ‖(1 : Matrix O O ℂ)‖ ≤ 1 := l2_norm_one_le
  have h2 : ‖L‖ ^ 2 ≤ 1 := by
    nlinarith [hsq, h1, sq_nonneg (‖L‖), norm_nonneg L]
  exact (sq_le_one_iff₀ (norm_nonneg L)).mp h2

private theorem compress_sub {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (A B : Matrix H H ℂ) :
    compress L A R - compress L B R = Lᴴ * (A - B) * R := by
  show Lᴴ * A * R - Lᴴ * B * R = Lᴴ * (A - B) * R
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]

private theorem compress_contract {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (A B : Matrix H H ℂ)
    (hL : IsIsometry L) (hR : IsIsometry R) :
    ‖compress L A R - compress L B R‖ ≤ ‖A - B‖ := by
  have hnormL : ‖Lᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_norm_le_one hL
  have hnormR : ‖R‖ ≤ 1 := isometry_norm_le_one hR
  have hΔ : 0 ≤ ‖A - B‖ := norm_nonneg _
  rw [compress_sub L R A B]
  refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
  refine le_trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)) ?_
  have step1 : ‖Lᴴ‖ * ‖A - B‖ ≤ ‖A - B‖ :=
    le_trans (mul_le_mul_of_nonneg_right hnormL hΔ) (by rw [one_mul])
  refine le_trans (mul_le_mul_of_nonneg_left hnormR (mul_nonneg (norm_nonneg _) hΔ)) ?_
  rw [mul_one]
  exact step1

theorem clause2_matrix_family_response_lower_bound :
    ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix H I ℂ) (O₁ O₂ : Matrix H H ℂ)
      (word : List (AdjointStep H)) (A B : Matrix I I ℂ) (eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    0 ≤ eps →
    ‖A - compress L (evaluate O₁ word) R‖ ≤ eps →
    ‖B - compress L (evaluate O₂ word) R‖ ≤ eps →
    max 0 (‖A - B‖ - 2 * eps) ≤ (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ := by
  intro H I _ _ _ _ _ L R O₁ O₂ word A B eps hL hR hWF hguard heps ha hb
  have hdiff : ‖compress L (evaluate O₁ word) R - compress L (evaluate O₂ word) R‖ ≤
      ‖evaluate O₁ word - evaluate O₂ word‖ :=
    compress_contract L R _ _ hL hR
  have hhyb : ‖evaluate O₁ word - evaluate O₂ word‖ ≤
      (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ :=
    clause2_general_hybrid_bound H O₁ O₂ word hWF hguard
  have hchain : ‖A - B‖ ≤ eps + ((adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ + eps) := by
    have h1 : ‖A - B‖ ≤ ‖A - compress L (evaluate O₁ word) R‖ +
        ‖compress L (evaluate O₁ word) R - compress L (evaluate O₂ word) R‖ +
        ‖compress L (evaluate O₂ word) R - B‖ := by
      have h1' : ‖A - B‖ ≤ ‖A - compress L (evaluate O₁ word) R‖ +
          ‖compress L (evaluate O₁ word) R - B‖ :=
        norm_sub_le_norm_sub_add_norm_sub A (compress L (evaluate O₁ word) R) B
      have h2' : ‖compress L (evaluate O₁ word) R - B‖ ≤
          ‖compress L (evaluate O₁ word) R - compress L (evaluate O₂ word) R‖ +
            ‖compress L (evaluate O₂ word) R - B‖ :=
        norm_sub_le_norm_sub_add_norm_sub (compress L (evaluate O₁ word) R)
          (compress L (evaluate O₂ word) R) B
      linarith
    have h3 : ‖compress L (evaluate O₂ word) R - B‖ ≤ eps := by
      rw [norm_sub_rev]
      exact hb
    linarith
  apply max_le
  · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  · linarith

theorem clause1_matrix_family_adaptive_lower_bound :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (p : List Bool) (A B : Matrix I I ℂ) (eps : ℝ),
    IsIsometry L → IsIsometry R → tree.WellFormed →
    (∀ c ∈ tree.pathWord p, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    0 ≤ eps →
    ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ ≤ eps →
    ‖B - compress L (evaluate O₂ (tree.pathWord p)) R‖ ≤ eps →
    max 0 (‖A - B‖ - 2 * eps) ≤ (tree.pathQueries p : ℝ) * ‖O₁ - O₂‖ := by
  intro I _ _ _ L R O₁ O₂ tree p A B eps hL hR hWF hguard heps ha hb
  have hdiff : ‖compress L (evaluate O₁ (tree.pathWord p)) R
        - compress L (evaluate O₂ (tree.pathWord p)) R‖ ≤
      ‖evaluate O₁ (tree.pathWord p) - evaluate O₂ (tree.pathWord p)‖ :=
    compress_contract L R _ _ hL hR
  have hhyb : ‖evaluate O₁ (tree.pathWord p) - evaluate O₂ (tree.pathWord p)‖ ≤
      (tree.pathQueries p : ℝ) * ‖O₁ - O₂‖ :=
    clause2_measurement_feedback_covered I O₁ O₂ tree p hWF hguard
  have hchain : ‖A - B‖ ≤ eps + ((tree.pathQueries p : ℝ) * ‖O₁ - O₂‖ + eps) := by
    have h1 : ‖A - B‖ ≤ ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ +
        ‖compress L (evaluate O₁ (tree.pathWord p)) R
            - compress L (evaluate O₂ (tree.pathWord p)) R‖ +
        ‖compress L (evaluate O₂ (tree.pathWord p)) R - B‖ := by
      have h1' : ‖A - B‖ ≤ ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ +
          ‖compress L (evaluate O₁ (tree.pathWord p)) R - B‖ :=
        norm_sub_le_norm_sub_add_norm_sub A (compress L (evaluate O₁ (tree.pathWord p)) R) B
      have h2' : ‖compress L (evaluate O₁ (tree.pathWord p)) R - B‖ ≤
          ‖compress L (evaluate O₁ (tree.pathWord p)) R
              - compress L (evaluate O₂ (tree.pathWord p)) R‖ +
            ‖compress L (evaluate O₂ (tree.pathWord p)) R - B‖ :=
        norm_sub_le_norm_sub_add_norm_sub (compress L (evaluate O₁ (tree.pathWord p)) R)
          (compress L (evaluate O₂ (tree.pathWord p)) R) B
      linarith
    have h3 : ‖compress L (evaluate O₂ (tree.pathWord p)) R - B‖ ≤ eps := by
      rw [norm_sub_rev]
      exact hb
    linarith
  apply max_le
  · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  · linarith

theorem clause3_query_bound_trips_the_machine_ledgers :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)) (q : ℝ),
    0 ≤ q → q ≤ (adjointQueryCount word : ℝ) →
    (M.minAccessGateCost O : ℝ) * q ≤ (GateCount (M.signalWordCircuit O word) : ℝ) ∧
    (M.minAccessBitCost O : ℝ) * q ≤ (M.signalWordAccount O word).classicalBits ∧
    (adjointQueryCount word : ℕ) ≤ (M.signalWordAccount O word).depth := by
  intro I _ _ M O word q hq hle
  have hgate : (M.minAccessGateCost O : ℝ) * (adjointQueryCount word : ℝ) ≤
      (GateCount (M.signalWordCircuit O word) : ℝ) := clause3_gate_cost_lower_bound I M O word
  have hbit : (M.minAccessBitCost O : ℝ) * (adjointQueryCount word : ℝ) ≤
      (M.signalWordAccount O word).classicalBits := clause3_bit_cost_lower_bound I M O word
  have htime : (adjointQueryCount word : ℕ) ≤ (M.signalWordAccount O word).depth :=
    clause3_bit_time_lower_bound I M O word
  have hng : 0 ≤ (M.minAccessGateCost O : ℝ) := Nat.cast_nonneg _
  have hnb : 0 ≤ (M.minAccessBitCost O : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_, htime⟩
  · exact le_trans (mul_le_mul_of_nonneg_left hle hng) hgate
  · exact le_trans (mul_le_mul_of_nonneg_left hle hnb) hbit

private theorem foldl_max_ge_base : ∀ (l : List ℕ) (m : ℕ), m ≤ l.foldl max m := by
  intro l
  induction l with
  | nil => intro m; exact Nat.le_refl _
  | cons a l ih =>
    intro m
    have h1 : m ≤ max m a := le_max_left m a
    have h2 : max m a ≤ l.foldl max (max m a) := ih (max m a)
    have h3 : (a :: l).foldl max m = l.foldl max (max m a) := rfl
    rw [h3]
    exact le_trans h1 h2

private theorem foldl_max_monotone : ∀ (l : List ℕ) (m n : ℕ), m ≤ n →
    l.foldl max m ≤ l.foldl max n := by
  intro l
  induction l with
  | nil => intro m n h; exact h
  | cons a l ih =>
    intro m n h
    have h1 : max m a ≤ max n a := max_le_max h (Nat.le_refl a)
    have h2 : (a :: l).foldl max m = l.foldl max (max m a) := rfl
    have h3 : (a :: l).foldl max n = l.foldl max (max n a) := rfl
    rw [h2, h3]
    exact ih (max m a) (max n a) h1

private theorem foldl_max_ge_mem : ∀ (l : List ℕ) (x : ℕ), x ∈ l →
    x ≤ l.foldl max 0 := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hx
    · subst x
      have h1 : max 0 a ≤ l.foldl max (max 0 a) := foldl_max_ge_base l (max 0 a)
      have h2 : a ≤ max 0 a := le_max_right 0 a
      have h3 : (a :: l).foldl max 0 = l.foldl max (max 0 a) := rfl
      rw [h3]
      exact le_trans h2 h1
    · have h3 : (a :: l).foldl max 0 = l.foldl max (max 0 a) := rfl
      have hmono : l.foldl max 0 ≤ l.foldl max (max 0 a) :=
        foldl_max_monotone l 0 (max 0 a) (Nat.zero_le _)
      rw [h3]
      exact le_trans (ih x hx) hmono

private theorem paths_ne_nil : ∀ (H : Type) [Fintype H] [DecidableEq H]
    (tree : AdaptiveSignalTree H), tree.paths ≠ [] := by
  intro H _ _ tree
  induction tree with
  | leaf => simp [AdaptiveSignalTree.paths]
  | node w t0 t1 ih0 ih1 =>
    intro hcontra
    have hcat : (AdaptiveSignalTree.paths t0).map (fun p => false :: p) ++
        (AdaptiveSignalTree.paths t1).map (fun p => true :: p) = [] := by
      rw [AdaptiveSignalTree.paths] at hcontra
      exact hcontra
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ ih0
    have hmem : false :: p ∈ (AdaptiveSignalTree.paths t0).map (fun q => false :: q) :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    have h1 : (AdaptiveSignalTree.paths t0).map (fun q => false :: q) ≠ [] :=
      List.ne_nil_of_mem hmem
    have h2 : (AdaptiveSignalTree.paths t0).map (fun q => false :: q) ++
        (AdaptiveSignalTree.paths t1).map (fun q => true :: q) ≠ [] := by
      exact List.ne_nil_of_mem (List.mem_append_left _ hmem)
    exact absurd hcat h2

private theorem list_sum_le_sum_pointwise {α : Type} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, g x ≤ f x) (hg : ∀ x ∈ l, 0 ≤ g x) :
    (l.map g).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (List.mem_cons_self)
    have hag := hg a (List.mem_cons_self)
    have hrest : (l.map g).sum ≤ (l.map f).sum :=
      ih (fun x hx => h x (List.mem_cons_of_mem a hx)) (fun x hx => hg x (List.mem_cons_of_mem a hx))
    simp only [List.map_cons, List.sum_cons]
    linarith

private theorem list_sum_const_mul {α : Type} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map (fun a => f a * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

private theorem list_sum_split {α : Type} (l : List α) (P : α → Bool) (f : α → ℝ) :
    (l.map f).sum =
      ((l.filter P).map f).sum + ((l.filter (fun a => ! P a)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a
    · have h1 : (a :: l).filter P = a :: l.filter P := by simp [h]
      have h2 : (a :: l).filter (fun x => ! P x) = l.filter (fun x => ! P x) := by simp [h]
      rw [h1, h2]
      simp only [List.map_cons, List.sum_cons]
      linarith
    · have h1 : (a :: l).filter P = l.filter P := by simp [h]
      have h2 : (a :: l).filter (fun x => ! P x) = a :: l.filter (fun x => ! P x) := by simp [h]
      rw [h1, h2]
      simp only [List.map_cons, List.sum_cons]
      linarith

private theorem list_sum_nonneg_of {α : Type} (l : List α) (f : α → ℝ)
    (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self)
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    linarith

private theorem list_sum_filter_eq_indicator {α : Type} (l : List α) (P : α → Bool)
    (f : α → ℝ) :
    ((l.filter P).map f).sum = (l.map (fun a => if P a then f a else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : P a
    · simp [List.filter, h, ih]
    · simp [List.filter, h, ih]

private theorem filter_all_false {α : Type} (l : List α) (P : α → Bool)
    (h : ∀ a ∈ l, P a = false) : l.filter P = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : P a = false := h a (List.mem_cons_self)
    have hrest : ∀ b ∈ l, P b = false := fun b hb => h b (List.mem_cons_of_mem a hb)
    simp [List.filter, ha, ih hrest]

private theorem filter_mem_eq (l : List (List Bool × ℝ)) (S : List (List Bool)) :
    l.filter (fun e => e.1 ∈ S) = l.filter (fun e => decide (e.1 ∈ S)) := by
  apply congrArg (fun g => l.filter g)
  funext e
  rfl

theorem clause1_matrix_family_joint_distribution :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (S : List (List Bool)) (law : SignalBranchLaw)
      (A B : Matrix I I ℂ) (eps : ℝ),
    0 ≤ eps → 0 < ‖O₁ - O₂‖ →
    IsIsometry L → IsIsometry R → tree.WellFormed →
    (∀ p : List Bool, ∀ c ∈ tree.pathWord p,
      ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    (∀ p ∈ S, ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p ∈ S, ‖B - compress L (evaluate O₂ (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p ∈ S, responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖
        ≤ tree.pathQueries p) ∧
    (∀ k : ℕ, k < responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ →
      branchQualifyingLevelMass tree law S k = 0) ∧
    law.expectedQueries tree =
        ((law.support.filter (fun e => decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum +
        ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ∧
    law.expectedQueries tree ≥
        (responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ : ℝ) * law.mass S ∧
    law.mass S + law.tailMass S = 1 := by
  intro I _ _ _ L R O₁ O₂ tree S law A B eps heps hd hL hR hWF hguard ha hb
  have hpath : ∀ p ∈ S, (tree.pathQueries p : ℝ) * ‖O₁ - O₂‖ ≥
      matrixResponseConstant A B eps := by
    intro p hp
    have h := clause1_matrix_family_adaptive_lower_bound I L R O₁ O₂ tree p A B eps
      hL hR hWF (fun c hc => hguard p c hc) heps (ha p hp) (hb p hp)
    simpa only [matrixResponseConstant] using! h
  have hconf : ∀ p ∈ S, responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖
      ≤ tree.pathQueries p := by
    intro p hp
    exact (responseQueryThreshold_spec hd).mpr (hpath p hp)
  have hlevel : ∀ k : ℕ, k < responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ →
      branchQualifyingLevelMass tree law S k = 0 := by
    intro k hk
    have hempty : law.support.filter (fun e =>
        decide (e.1 ∈ S) && decide (tree.pathQueries e.1 = k)) = [] := by
      apply filter_all_false
      intro e he
      by_cases hmem : e.1 ∈ S
      · by_cases hq : tree.pathQueries e.1 = k
        · have h3 := hconf e.1 hmem
          have h4 : responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ ≤ k :=
              h3.trans_eq hq
          exfalso
          exact absurd (hk.trans_le h4) (Nat.lt_irrefl _)
        · simp [hmem, hq]
      · simp [hmem]
    rw [branchQualifyingLevelMass, hempty]
    simp
  have hmass : law.mass S =
      ((law.support.filter (fun e => decide (e.1 ∈ S))).map (fun e => e.2)).sum := by
    have h := filter_mem_eq law.support S
    rw [SignalBranchLaw.mass, h]
  have htailmass : ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
      (fun e => e.2)).sum = law.tailMass S := by
    have h2 : law.support.filter (fun e => e.1 ∉ S)
        = law.support.filter (fun e => ! decide (e.1 ∈ S)) := by
      apply congrArg (fun g => law.support.filter g)
      funext e
      show decide (e.1 ∉ S) = ! decide (e.1 ∈ S)
      by_cases h : e.1 ∈ S
      · simp [h]
      · simp [h]
    rw [SignalBranchLaw.tailMass, h2]
  have hexp : law.expectedQueries tree =
        ((law.support.filter (fun e => decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum +
        ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum := by
    rw [SignalBranchLaw.expectedQueries]
    exact list_sum_split law.support (fun e => decide (e.1 ∈ S))
      (fun e => e.2 * (tree.pathQueries e.1 : ℝ))
  have hsum : ((law.support.filter (fun e => decide (e.1 ∈ S))).map
        (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ≥
      ((law.support.filter (fun e => decide (e.1 ∈ S))).map
        (fun e => e.2 *
          (responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ : ℝ))).sum := by
    apply list_sum_le_sum_pointwise
    · intro e he
      have hmem := List.mem_filter.mp he
      have hmem' : e.1 ∈ S := of_decide_eq_true hmem.2
      have hnonneg : 0 ≤ e.2 := law.nonneg e hmem.1
      have h4 := hconf e.1 hmem'
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 h4) hnonneg
    · intro e he
      have hmem := List.mem_filter.mp he
      exact mul_nonneg (law.nonneg e hmem.1) (Nat.cast_nonneg _)
  have htailnonneg : ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
        (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ≥ 0 := by
    exact list_sum_nonneg_of _ _ fun e he => by
      have hmem := List.mem_filter.mp he
      exact mul_nonneg (law.nonneg e hmem.1) (Nat.cast_nonneg _)
  have hconst : ((law.support.filter (fun e => decide (e.1 ∈ S))).map
        (fun e => e.2 *
          (responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ : ℝ))).sum =
      (responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ : ℝ) * law.mass S := by
    rw [list_sum_const_mul, hmass]
    ring
  refine ⟨hconf, hlevel, hexp, ?_, ?_⟩
  · linarith [hsum, htailnonneg, hconst, hexp]
  · have hsplit : (law.support.map (fun e => e.2)).sum =
        ((law.support.filter (fun e => decide (e.1 ∈ S))).map (fun e => e.2)).sum +
        ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map (fun e => e.2)).sum :=
      list_sum_split law.support (fun e => decide (e.1 ∈ S)) (fun e => e.2)
    linarith [law.total, hsplit, hmass, htailmass]

theorem clause1_matrix_family_worst_case_and_expected_lower_bound :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (A B : Matrix I I ℂ) (eps : ℝ),
    IsIsometry L → IsIsometry R → tree.WellFormed →
    (∀ p : List Bool, ∀ c ∈ tree.pathWord p,
      ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    0 ≤ eps →
    (∀ p : List Bool, ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p : List Bool, ‖B - compress L (evaluate O₂ (tree.pathWord p)) R‖ ≤ eps) →
    (tree.worstCaseQueries : ℝ) * ‖O₁ - O₂‖ ≥ matrixResponseConstant A B eps ∧
    (∀ law : SignalBranchLaw, law.expectedQueries tree * ‖O₁ - O₂‖ ≥
      matrixResponseConstant A B eps) := by
  intro I _ _ _ L R O₁ O₂ tree A B eps hL hR hWF hguard heps ha hb
  have hpath : ∀ p : List Bool, (tree.pathQueries p : ℝ) * ‖O₁ - O₂‖ ≥
      matrixResponseConstant A B eps := by
    intro p
    have h := clause1_matrix_family_adaptive_lower_bound I L R O₁ O₂ tree p A B eps
      hL hR hWF (fun c hc => hguard p c hc) heps (ha p) (hb p)
    simpa [matrixResponseConstant] using! h
  have hworst : (tree.worstCaseQueries : ℝ) * ‖O₁ - O₂‖ ≥ matrixResponseConstant A B eps := by
    have hmem : ∀ p ∈ tree.paths, tree.pathQueries p ≤ tree.worstCaseQueries := by
      intro p hp
      have hmem' : tree.pathQueries p ∈ (tree.paths.map (tree.pathQueries) : List ℕ) :=
        List.mem_map.mpr ⟨p, hp, rfl⟩
      have h := foldl_max_ge_mem (tree.paths.map (tree.pathQueries)) (tree.pathQueries p) hmem'
      simpa only [AdaptiveSignalTree.worstCaseQueries] using! h
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (paths_ne_nil I tree)
    have hq : (tree.pathQueries p : ℝ) ≤ (tree.worstCaseQueries : ℝ) :=
      Nat.cast_le.2 (hmem p hp)
    have hd : 0 ≤ ‖O₁ - O₂‖ := norm_nonneg _
    exact le_trans (hpath p) (mul_le_mul_of_nonneg_right hq hd)
  have hexp : ∀ law : SignalBranchLaw, law.expectedQueries tree * ‖O₁ - O₂‖ ≥
      matrixResponseConstant A B eps := by
    intro law
    have hsum : (law.support.map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ) * ‖O₁ - O₂‖)).sum ≥
        (law.support.map (fun e => e.2 * matrixResponseConstant A B eps)).sum := by
      apply list_sum_le_sum_pointwise
      · intro e he
        have h1 : (tree.pathQueries e.1 : ℝ) * ‖O₁ - O₂‖ ≥ matrixResponseConstant A B eps :=
          hpath e.1
        calc
          e.2 * (tree.pathQueries e.1 : ℝ) * ‖O₁ - O₂‖ =
              e.2 * ((tree.pathQueries e.1 : ℝ) * ‖O₁ - O₂‖) := by ring
          _ ≥ e.2 * matrixResponseConstant A B eps :=
            mul_le_mul_of_nonneg_left h1 (law.nonneg e he)
      · intro e he
        exact mul_nonneg (law.nonneg e he) (le_max_left _ _)
    calc
      law.expectedQueries tree * ‖O₁ - O₂‖ =
          (law.support.map (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum * ‖O₁ - O₂‖ := by
            rw [SignalBranchLaw.expectedQueries]
      _ = (law.support.map
            (fun e => e.2 * (tree.pathQueries e.1 : ℝ) * ‖O₁ - O₂‖)).sum := by
            rw [← list_sum_const_mul law.support
              (fun e => e.2 * (tree.pathQueries e.1 : ℝ)) ‖O₁ - O₂‖]
      _ ≥ (law.support.map (fun e => e.2 * matrixResponseConstant A B eps)).sum := hsum
      _ = (law.support.map (fun e => e.2)).sum * matrixResponseConstant A B eps := by
            rw [list_sum_const_mul law.support (fun e => e.2) (matrixResponseConstant A B eps)]
      _ = 1 * matrixResponseConstant A B eps := by rw [law.total]
      _ = matrixResponseConstant A B eps := one_mul _
  exact ⟨hworst, hexp⟩

theorem clause1_matrix_family_structural_tail_transport :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (tree : AdaptiveSignalTree I) (S : List (List Bool)) (law : SignalBranchLaw)
      (A B : Matrix I I ℂ) (eps d : ℝ),
    0 ≤ d →
    (∀ p ∈ S, (tree.pathQueries p : ℝ) * d ≥ matrixResponseConstant A B eps) →
    law.expectedQueries tree * d ≥ matrixResponseConstant A B eps * law.mass S := by
  intro I _ _ tree S law A B eps d hd hS
  have hexp : law.expectedQueries tree =
      ((law.support.filter (fun e => decide (e.1 ∈ S))).map
        (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum +
      ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
        (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum := by
    rw [SignalBranchLaw.expectedQueries]
    exact list_sum_split law.support (fun e => decide (e.1 ∈ S))
      (fun e => e.2 * (tree.pathQueries e.1 : ℝ))
  have hgood : ((law.support.filter (fun e => decide (e.1 ∈ S))).map
      (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum * d ≥
      ((law.support.filter (fun e => decide (e.1 ∈ S))).map
        (fun e => e.2 * matrixResponseConstant A B eps)).sum := by
    calc
      ((law.support.filter (fun e => decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum * d =
          ((law.support.filter (fun e => decide (e.1 ∈ S))).map
            (fun e => e.2 * (tree.pathQueries e.1 : ℝ) * d)).sum := by
              rw [← list_sum_const_mul _ _ d]
      _ ≥ ((law.support.filter (fun e => decide (e.1 ∈ S))).map
            (fun e => e.2 * matrixResponseConstant A B eps)).sum := by
            apply list_sum_le_sum_pointwise
            · intro e he
              have hmem := List.mem_filter.mp he
              have h1 : (tree.pathQueries e.1 : ℝ) * d ≥ matrixResponseConstant A B eps :=
                hS e.1 (of_decide_eq_true hmem.2)
              calc
                e.2 * (tree.pathQueries e.1 : ℝ) * d =
                    e.2 * ((tree.pathQueries e.1 : ℝ) * d) := by ring
                _ ≥ e.2 * matrixResponseConstant A B eps :=
                  mul_le_mul_of_nonneg_left h1 (law.nonneg e hmem.1)
            · intro e he
              have hmem := List.mem_filter.mp he
              exact mul_nonneg (law.nonneg e hmem.1) (le_max_left _ _)
  have hbad : ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
      (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum * d ≥ 0 := by
    have hnonneg : ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
        (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ≥ 0 :=
      list_sum_nonneg_of _ _ fun e he => by
        have hmem := List.mem_filter.mp he
        exact mul_nonneg (law.nonneg e hmem.1) (Nat.cast_nonneg _)
    exact mul_nonneg hnonneg hd
  have hconst : ((law.support.filter (fun e => decide (e.1 ∈ S))).map
      (fun e => e.2 * matrixResponseConstant A B eps)).sum =
      law.mass S * matrixResponseConstant A B eps := by
    rw [list_sum_const_mul]
    rfl
  calc
    law.expectedQueries tree * d = (law.support.map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum * d := by
            rw [SignalBranchLaw.expectedQueries]
    _ = (law.support.map (fun e => e.2 * (tree.pathQueries e.1 : ℝ) * d)).sum := by
            rw [← list_sum_const_mul law.support
              (fun e => e.2 * (tree.pathQueries e.1 : ℝ)) d]
    _ = ((law.support.filter (fun e => decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ) * d)).sum +
        ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ) * d)).sum := by
            rw [list_sum_split law.support (fun e => decide (e.1 ∈ S))
              (fun e => e.2 * (tree.pathQueries e.1 : ℝ) * d)]
    _ = ((law.support.filter (fun e => decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum * d +
        ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum * d := by
            rw [← list_sum_const_mul (law.support.filter (fun e => decide (e.1 ∈ S)))
              (fun e => e.2 * (tree.pathQueries e.1 : ℝ)) d]
            rw [← list_sum_const_mul (law.support.filter (fun e => ! decide (e.1 ∈ S)))
              (fun e => e.2 * (tree.pathQueries e.1 : ℝ)) d]
    _ ≥ law.mass S * matrixResponseConstant A B eps + 0 := by linarith
    _ = matrixResponseConstant A B eps * law.mass S := by ring

theorem clause2_bounded_family_adaptive_response_lower_bound :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (F : MatrixFamily I) (z₁ z₂ : ℝ) (L R : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (A B : Matrix I I ℂ) (eps : ℝ),
    BoundedMatrixFamily F → IsIsometry L → IsIsometry R → tree.WellFormed →
    (∀ p : List Bool, WellFormedGates (tree.pathWord p)) →
    0 ≤ eps →
    (∀ p : List Bool, ‖A - compress L (evaluate (F z₁) (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p : List Bool, ‖B - compress L (evaluate (F z₂) (tree.pathWord p)) R‖ ≤ eps) →
    (tree.worstCaseQueries : ℝ) * ‖F z₁ - F z₂‖ ≥ matrixResponseConstant A B eps ∧
    (∀ law : SignalBranchLaw, law.expectedQueries tree * ‖F z₁ - F z₂‖ ≥
      matrixResponseConstant A B eps) := by
  intro I _ _ _ F z₁ z₂ L R tree A B eps hF hL hR hWF hgates heps ha hb
  have hguard : ∀ p : List Bool, ∀ c ∈ tree.pathWord p,
      ‖instructionMatrix (F z₁) c‖ ≤ 1 ∧ ‖instructionMatrix (F z₂) c‖ ≤ 1 := by
    intro p c hc
    have h₁ := boundedAccessWord_guard
      (boundedFamily_accessWord (F := F) (z := z₁) hF (hgates p)) c hc
    have h₂ := boundedAccessWord_guard
      (boundedFamily_accessWord (F := F) (z := z₂) hF (hgates p)) c hc
    exact ⟨h₁, h₂⟩
  exact clause1_matrix_family_worst_case_and_expected_lower_bound I L R (F z₁) (F z₂)
    tree A B eps hL hR hWF hguard heps ha hb

theorem clause2_family_coincidence_forces_target_gap :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (word : List (AdjointStep I)) (A B : Matrix I I ℂ) (eps : ℝ),
    O₁ = O₂ →
    ‖A - compress L (evaluate O₁ word) R‖ ≤ eps →
    ‖B - compress L (evaluate O₂ word) R‖ ≤ eps →
    ‖A - B‖ ≤ 2 * eps := by
  intro I _ _ L R O₁ O₂ word A B eps hEq ha hb
  have hsame : compress L (evaluate O₁ word) R = compress L (evaluate O₂ word) R := by
    rw [hEq]
  have hchain : ‖A - B‖ ≤ ‖A - compress L (evaluate O₁ word) R‖ +
      ‖compress L (evaluate O₁ word) R - B‖ :=
    norm_sub_le_norm_sub_add_norm_sub A (compress L (evaluate O₁ word) R) B
  have h3 : ‖compress L (evaluate O₁ word) R - B‖ ≤ eps := by
    have hb' : ‖B - compress L (evaluate O₁ word) R‖ ≤ eps := by
      rw [← hsame] at hb
      exact hb
    rwa [norm_sub_rev] at hb'
  linarith

theorem sharpness_evaluate_forward (O : Matrix Unit Unit ℂ) :
    evaluate O sharpnessWord = O := by
  simp [sharpnessWord, evaluate, instructionMatrix]

theorem sharpness_compress_identity (O : Matrix Unit Unit ℂ) :
    compress (1 : Matrix Unit Unit ℂ) O (1 : Matrix Unit Unit ℂ) = O := by
  simp [compress, Matrix.conjTranspose_one]

theorem clause2_matrix_family_slab_is_sharp :
    (‖sharpnessTargetOne - compress (1 : Matrix Unit Unit ℂ)
        (evaluate sharpnessOracleOne sharpnessWord) (1 : Matrix Unit Unit ℂ)‖ = sharpnessEps) ∧
    ‖sharpnessTargetTwo - compress (1 : Matrix Unit Unit ℂ)
        (evaluate sharpnessOracleTwo sharpnessWord) (1 : Matrix Unit Unit ℂ)‖ = sharpnessEps ∧
    ‖sharpnessOracleOne - sharpnessOracleTwo‖ = 1 / 2 ∧
    ‖sharpnessTargetOne - sharpnessTargetTwo‖ = 1 ∧
    matrixResponseConstant sharpnessTargetOne sharpnessTargetTwo sharpnessEps = 1 / 2 ∧
    (adjointQueryCount sharpnessWord : ℝ) * ‖sharpnessOracleOne - sharpnessOracleTwo‖ = 1 / 2 ∧
    max 0 (‖sharpnessTargetOne - sharpnessTargetTwo‖ - sharpnessEps) = 3 / 4 ∧
    3 / 4 > (adjointQueryCount sharpnessWord : ℝ) * ‖sharpnessOracleOne - sharpnessOracleTwo‖ := by
  have hone : ‖(1 : Matrix Unit Unit ℂ)‖ = 1 := l2_norm_one_eq
  have hreal : ∀ c : ℝ, ‖(c : ℂ)‖ = |c| := by
    intro c
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hsub : ∀ a b : ℝ, ((a : ℂ) • (1 : Matrix Unit Unit ℂ)) -
      ((b : ℂ) • (1 : Matrix Unit Unit ℂ)) =
      (((a - b : ℝ) : ℂ)) • (1 : Matrix Unit Unit ℂ) := by
    intro a b
    rw [← sub_smul]
    congr 1
    push_cast
    rfl
  have h1 : ‖sharpnessTargetOne - sharpnessOracleOne‖ = 1 / 4 := by
    rw [show sharpnessTargetOne = ((5 / 4 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [show sharpnessOracleOne = ((1 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [hsub]
    rw [show ((5 / 4 : ℝ) - 1 : ℝ) = 1 / 4 by norm_num]
    rw [norm_smul, hone, hreal (1 / 4), abs_of_nonneg (by norm_num), mul_one]
  have h2 : ‖sharpnessTargetTwo - sharpnessOracleTwo‖ = 1 / 4 := by
    rw [show sharpnessTargetTwo = ((1 / 4 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [show sharpnessOracleTwo = ((1 / 2 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [hsub]
    rw [show ((1 / 4 : ℝ) - 1 / 2 : ℝ) = -(1 / 4 : ℝ) by norm_num]
    rw [norm_smul, hone, hreal (-(1 / 4)), abs_neg, abs_of_nonneg (by norm_num), mul_one]
  have h3 : ‖sharpnessOracleOne - sharpnessOracleTwo‖ = 1 / 2 := by
    rw [show sharpnessOracleOne = ((1 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [show sharpnessOracleTwo = ((1 / 2 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [hsub]
    rw [show ((1 : ℝ) - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    rw [norm_smul, hone, hreal (1 / 2), abs_of_nonneg (by norm_num), mul_one]
  have h4 : ‖sharpnessTargetOne - sharpnessTargetTwo‖ = 1 := by
    rw [show sharpnessTargetOne = ((5 / 4 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [show sharpnessTargetTwo = ((1 / 4 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [hsub]
    rw [show ((5 / 4 : ℝ) - 1 / 4 : ℝ) = 1 by norm_num]
    rw [norm_smul, hone, hreal 1, abs_of_nonneg (by norm_num), mul_one]
  have h5 : matrixResponseConstant sharpnessTargetOne sharpnessTargetTwo sharpnessEps = 1 / 2 := by
    rw [matrixResponseConstant, h4]
    norm_num [sharpnessEps]
  have hq : (adjointQueryCount sharpnessWord : ℝ) = 1 := by
    simp [sharpnessWord, adjointQueryCount]
  have h6 : (adjointQueryCount sharpnessWord : ℝ) *
      ‖sharpnessOracleOne - sharpnessOracleTwo‖ = 1 / 2 := by
    rw [hq, h3]
    norm_num
  have h7 : max 0 (‖sharpnessTargetOne - sharpnessTargetTwo‖ - sharpnessEps) = 3 / 4 := by
    rw [h4]
    norm_num [sharpnessEps]
  refine ⟨?_, ?_, h3, h4, h5, h6, h7, ?_⟩
  · rw [sharpness_compress_identity, sharpness_evaluate_forward]
    exact h1
  · rw [sharpness_compress_identity, sharpness_evaluate_forward]
    exact h2
  · rw [h6]
    norm_num

theorem clause3_matrix_family_separation_forces_machine_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (M : OracleAccessModel I) (O₁ O₂ : Matrix I I ℂ)
      (word : List (AdjointStep I)) (A B : Matrix I I ℂ) (eps : ℝ),
    0 < ‖O₁ - O₂‖ →
    (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    WellFormedAdjointCircuit word →
    max 0 (‖A - B‖ - 2 * eps) ≤ (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ →
    (M.minAccessGateCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) ≤
        (GateCount (M.signalWordCircuit O₁ word) : ℝ) ∧
    (M.minAccessBitCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) ≤
        (M.signalWordAccount O₁ word).classicalBits ∧
    (adjointQueryCount word : ℕ) ≤ (M.signalWordAccount O₁ word).depth := by
  intro I _ _ _ M O₁ O₂ word A B eps hgap hguard hWF hbound
  have hq : 0 ≤ max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖ :=
    div_nonneg (le_max_left _ _) (le_of_lt hgap)
  have hle : max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖ ≤ (adjointQueryCount word : ℝ) := by
    refine (div_le_iff₀ hgap).mpr ?_
    exact hbound
  exact clause3_query_bound_trips_the_machine_ledgers I M O₁ word
    (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) hq hle

theorem clause3_word_access_counts :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (word : List (AdjointStep I)),
    wordForwardAccesses word + wordBackwardAccesses word = adjointQueryCount word := by
  intro I _ _ word
  induction word with
  | nil => rfl
  | cons c cs ih =>
    cases c <;>
      simp only [wordForwardAccesses, wordBackwardAccesses, adjointQueryCount, List.map_cons,
        List.sum_cons] at ih ⊢ <;> omega

theorem clause3_realized_word_gate_cost_is_direction_resolved :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    M.realizedWordGateCount O word =
        wordForwardAccesses word * M.accessGateCost O false +
          wordBackwardAccesses word * M.accessGateCost O true := by
  intro I _ _ M O word
  induction word with
  | nil =>
    simp [wordForwardAccesses, wordBackwardAccesses, OracleAccessModel.realizedWordGateCount]
  | cons c cs ih =>
    cases c with
    | gate V =>
      simp only [wordForwardAccesses, wordBackwardAccesses, List.map_cons, List.sum_cons,
        OracleAccessModel.realizedWordGateCount] at ih ⊢
      rw [ih]
      ring
    | forward =>
      simp only [wordForwardAccesses, wordBackwardAccesses, List.map_cons, List.sum_cons,
        OracleAccessModel.realizedWordGateCount] at ih ⊢
      rw [ih]
      ring
    | backward =>
      simp only [wordForwardAccesses, wordBackwardAccesses, List.map_cons, List.sum_cons,
        OracleAccessModel.realizedWordGateCount] at ih ⊢
      rw [ih]
      ring

theorem clause3_realized_word_bit_cost_is_direction_resolved :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    M.realizedWordBitCost O word =
        wordForwardAccesses word * M.readBits O false +
          wordBackwardAccesses word * M.readBits O true := by
  intro I _ _ M O word
  induction word with
  | nil =>
    simp [wordForwardAccesses, wordBackwardAccesses, OracleAccessModel.realizedWordBitCost]
  | cons c cs ih =>
    cases c with
    | gate V =>
      simp only [wordForwardAccesses, wordBackwardAccesses, List.map_cons, List.sum_cons,
        OracleAccessModel.realizedWordBitCost] at ih ⊢
      rw [ih]
      ring
    | forward =>
      simp only [wordForwardAccesses, wordBackwardAccesses, List.map_cons, List.sum_cons,
        OracleAccessModel.realizedWordBitCost] at ih ⊢
      rw [ih]
      ring
    | backward =>
      simp only [wordForwardAccesses, wordBackwardAccesses, List.map_cons, List.sum_cons,
        OracleAccessModel.realizedWordBitCost] at ih ⊢
      rw [ih]
      ring

theorem clause3_query_forced_cost_decomposition :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)) (q : ℝ),
    0 ≤ q → q ≤ (adjointQueryCount word : ℝ) →
    (M.realizedWordGateCount O word : ℝ) =
        (M.minAccessGateCost O : ℝ) * q +
          ((M.minAccessGateCost O : ℝ) * ((adjointQueryCount word : ℝ) - q) +
            ((M.accessGateCost O false - M.minAccessGateCost O) * (wordForwardAccesses word : ℝ) +
             (M.accessGateCost O true - M.minAccessGateCost O) * (wordBackwardAccesses word : ℝ))) ∧
    (M.realizedWordBitCost O word : ℝ) =
        (M.minAccessBitCost O : ℝ) * q +
          ((M.minAccessBitCost O : ℝ) * ((adjointQueryCount word : ℝ) - q) +
            ((M.readBits O false - M.minAccessBitCost O) * (wordForwardAccesses word : ℝ) +
             (M.readBits O true - M.minAccessBitCost O) * (wordBackwardAccesses word : ℝ))) := by
  intro I _ _ M O word q hq hle
  have hfb : (wordForwardAccesses word : ℝ) + (wordBackwardAccesses word : ℝ)
      = (adjointQueryCount word : ℝ) := by
    exact_mod_cast clause3_word_access_counts I word
  have hgate : (M.realizedWordGateCount O word : ℝ) =
      (wordForwardAccesses word : ℝ) * (M.accessGateCost O false : ℝ) +
        (wordBackwardAccesses word : ℝ) * (M.accessGateCost O true : ℝ) := by
    rw [clause3_realized_word_gate_cost_is_direction_resolved]
    push_cast
    ring
  have hbit : (M.realizedWordBitCost O word : ℝ) =
      (wordForwardAccesses word : ℝ) * (M.readBits O false : ℝ) +
        (wordBackwardAccesses word : ℝ) * (M.readBits O true : ℝ) := by
    rw [clause3_realized_word_bit_cost_is_direction_resolved]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · calc
      (M.realizedWordGateCount O word : ℝ) =
          (wordForwardAccesses word : ℝ) * (M.accessGateCost O false : ℝ) +
            (wordBackwardAccesses word : ℝ) * (M.accessGateCost O true : ℝ) := hgate
      _ = (M.minAccessGateCost O : ℝ) * ((wordForwardAccesses word : ℝ) +
            (wordBackwardAccesses word : ℝ)) +
          ((M.accessGateCost O false : ℝ) - (M.minAccessGateCost O : ℝ)) *
              (wordForwardAccesses word : ℝ) +
          ((M.accessGateCost O true : ℝ) - (M.minAccessGateCost O : ℝ)) *
              (wordBackwardAccesses word : ℝ) := by ring
      _ = (M.minAccessGateCost O : ℝ) * q +
          ((M.minAccessGateCost O : ℝ) * ((adjointQueryCount word : ℝ) - q) +
            ((M.accessGateCost O false - M.minAccessGateCost O) * (wordForwardAccesses word : ℝ) +
             (M.accessGateCost O true - M.minAccessGateCost O) * (wordBackwardAccesses word : ℝ))) := by
          rw [hfb]
          ring
  · calc
      (M.realizedWordBitCost O word : ℝ) =
          (wordForwardAccesses word : ℝ) * (M.readBits O false : ℝ) +
            (wordBackwardAccesses word : ℝ) * (M.readBits O true : ℝ) := hbit
      _ = (M.minAccessBitCost O : ℝ) * ((wordForwardAccesses word : ℝ) +
            (wordBackwardAccesses word : ℝ)) +
          ((M.readBits O false : ℝ) - (M.minAccessBitCost O : ℝ)) *
              (wordForwardAccesses word : ℝ) +
          ((M.readBits O true : ℝ) - (M.minAccessBitCost O : ℝ)) *
              (wordBackwardAccesses word : ℝ) := by ring
      _ = (M.minAccessBitCost O : ℝ) * q +
          ((M.minAccessBitCost O : ℝ) * ((adjointQueryCount word : ℝ) - q) +
            ((M.readBits O false - M.minAccessBitCost O) * (wordForwardAccesses word : ℝ) +
             (M.readBits O true - M.minAccessBitCost O) * (wordBackwardAccesses word : ℝ))) := by
          rw [hfb]
          ring

theorem clause3_matrix_family_separation_forces_direction_resolved_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (M : OracleAccessModel I) (O₁ O₂ : Matrix I I ℂ)
      (word : List (AdjointStep I)) (A B : Matrix I I ℂ) (eps : ℝ),
    0 < ‖O₁ - O₂‖ →
    (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    WellFormedAdjointCircuit word →
    max 0 (‖A - B‖ - 2 * eps) ≤ (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ →
    (M.minAccessGateCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) ≤
        (M.realizedWordGateCount O₁ word : ℝ) ∧
    (M.minAccessBitCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) ≤
        (M.realizedWordBitCost O₁ word : ℝ) ∧
    (M.realizedWordGateCount O₁ word : ℝ) -
        (M.minAccessGateCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) =
        (M.minAccessGateCost O₁ : ℝ) *
            ((adjointQueryCount word : ℝ) - max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) +
          (((M.accessGateCost O₁ false : ℝ) - (M.minAccessGateCost O₁ : ℝ)) *
              (wordForwardAccesses word : ℝ) +
           ((M.accessGateCost O₁ true : ℝ) - (M.minAccessGateCost O₁ : ℝ)) *
              (wordBackwardAccesses word : ℝ)) ∧
    (M.realizedWordBitCost O₁ word : ℝ) -
        (M.minAccessBitCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) =
        (M.minAccessBitCost O₁ : ℝ) *
            ((adjointQueryCount word : ℝ) - max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) +
          (((M.readBits O₁ false : ℝ) - (M.minAccessBitCost O₁ : ℝ)) *
              (wordForwardAccesses word : ℝ) +
           ((M.readBits O₁ true : ℝ) - (M.minAccessBitCost O₁ : ℝ)) *
              (wordBackwardAccesses word : ℝ)) := by
  intro I _ _ _ M O₁ O₂ word A B eps hgap hguard hWF hbound
  have hq : 0 ≤ max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖ :=
    div_nonneg (le_max_left _ _) (le_of_lt hgap)
  have hle : max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖ ≤ (adjointQueryCount word : ℝ) := by
    refine (div_le_iff₀ hgap).mpr ?_
    exact hbound
  have hdec := clause3_query_forced_cost_decomposition I M O₁ word
    (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) hq hle
  have hgate := hdec.1
  have hbit := hdec.2
  have hrest : 0 ≤ (adjointQueryCount word : ℝ) -
      max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖ := by
    linarith [hle]
  have hgf : (M.minAccessGateCost O₁ : ℝ) ≤ (M.accessGateCost O₁ false : ℝ) := by
    exact_mod_cast (min_le_left (M.accessGateCost O₁ false) (M.accessGateCost O₁ true))
  have hgb : (M.minAccessGateCost O₁ : ℝ) ≤ (M.accessGateCost O₁ true : ℝ) := by
    exact_mod_cast (min_le_right (M.accessGateCost O₁ false) (M.accessGateCost O₁ true))
  have hbf : (M.minAccessBitCost O₁ : ℝ) ≤ (M.readBits O₁ false : ℝ) := by
    exact_mod_cast (min_le_left (M.readBits O₁ false) (M.readBits O₁ true))
  have hbb : (M.minAccessBitCost O₁ : ℝ) ≤ (M.readBits O₁ true : ℝ) := by
    exact_mod_cast (min_le_right (M.readBits O₁ false) (M.readBits O₁ true))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hexc : 0 ≤ (M.minAccessGateCost O₁ : ℝ) *
          ((adjointQueryCount word : ℝ) - max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) +
        (((M.accessGateCost O₁ false : ℝ) - (M.minAccessGateCost O₁ : ℝ)) *
            (wordForwardAccesses word : ℝ) +
         ((M.accessGateCost O₁ true : ℝ) - (M.minAccessGateCost O₁ : ℝ)) *
            (wordBackwardAccesses word : ℝ)) := by
      have h1 : 0 ≤ (M.minAccessGateCost O₁ : ℝ) *
          ((adjointQueryCount word : ℝ) - max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) :=
        mul_nonneg (Nat.cast_nonneg _) hrest
      have h2 : 0 ≤ ((M.accessGateCost O₁ false : ℝ) - (M.minAccessGateCost O₁ : ℝ)) *
          (wordForwardAccesses word : ℝ) := by
        have h : 0 ≤ (M.accessGateCost O₁ false : ℝ) - (M.minAccessGateCost O₁ : ℝ) :=
          sub_nonneg.mpr hgf
        exact mul_nonneg h (Nat.cast_nonneg _)
      have h3 : 0 ≤ ((M.accessGateCost O₁ true : ℝ) - (M.minAccessGateCost O₁ : ℝ)) *
          (wordBackwardAccesses word : ℝ) := by
        have h : 0 ≤ (M.accessGateCost O₁ true : ℝ) - (M.minAccessGateCost O₁ : ℝ) :=
          sub_nonneg.mpr hgb
        exact mul_nonneg h (Nat.cast_nonneg _)
      linarith
    linarith [hgate]
  · have hexc : 0 ≤ (M.minAccessBitCost O₁ : ℝ) *
          ((adjointQueryCount word : ℝ) - max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) +
        (((M.readBits O₁ false : ℝ) - (M.minAccessBitCost O₁ : ℝ)) *
            (wordForwardAccesses word : ℝ) +
         ((M.readBits O₁ true : ℝ) - (M.minAccessBitCost O₁ : ℝ)) *
            (wordBackwardAccesses word : ℝ)) := by
      have h1 : 0 ≤ (M.minAccessBitCost O₁ : ℝ) *
          ((adjointQueryCount word : ℝ) - max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) :=
        mul_nonneg (Nat.cast_nonneg _) hrest
      have h2 : 0 ≤ ((M.readBits O₁ false : ℝ) - (M.minAccessBitCost O₁ : ℝ)) *
          (wordForwardAccesses word : ℝ) := by
        have h : 0 ≤ (M.readBits O₁ false : ℝ) - (M.minAccessBitCost O₁ : ℝ) :=
          sub_nonneg.mpr hbf
        exact mul_nonneg h (Nat.cast_nonneg _)
      have h3 : 0 ≤ ((M.readBits O₁ true : ℝ) - (M.minAccessBitCost O₁ : ℝ)) *
          (wordBackwardAccesses word : ℝ) := by
        have h : 0 ≤ (M.readBits O₁ true : ℝ) - (M.minAccessBitCost O₁ : ℝ) :=
          sub_nonneg.mpr hbb
        exact mul_nonneg h (Nat.cast_nonneg _)
      linarith
    linarith [hbit]
  · rw [hgate]
    ring
  · rw [hbit]
    ring

structure JointDistributionReceipt where

  oneAccessBranch : jointInstanceTree.pathQueries [false, false] = 1

  twoAccessBranch : jointInstanceTree.pathQueries [true, false] = 2

  worstCase : jointInstanceTree.worstCaseQueries = 2

  expectedCount : jointInstanceLaw.expectedQueries jointInstanceTree = 3 / 2

  qualifyingMass : jointInstanceLaw.mass jointInstanceQualifying = 1 / 2

  tailMass : jointInstanceLaw.tailMass jointInstanceQualifying = 1 / 2

  levelOne : branchLevelMass jointInstanceTree jointInstanceLaw 1 = 1 / 2

  levelTwo : branchLevelMass jointInstanceTree jointInstanceLaw 2 = 1 / 2

  qualifyingLevelOne :
    branchQualifyingLevelMass jointInstanceTree jointInstanceLaw jointInstanceQualifying 1 = 0

  qualifyingLevelTwo :
    branchQualifyingLevelMass jointInstanceTree jointInstanceLaw jointInstanceQualifying 2 = 1 / 2

  responseConstant :
    matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps = 3 / 4

  operatorGap : ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ = 1 / 2

  threshold :
    responseQueryThreshold
        (matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps)
        ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ = 2

  additiveCharge :
    (responseQueryThreshold
        (matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps)
        ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ : ℝ) *
          jointInstanceLaw.mass jointInstanceQualifying = 1

  additiveHolds :
    jointInstanceLaw.expectedQueries jointInstanceTree ≥
      (responseQueryThreshold
        (matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps)
        ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ : ℝ) *
          jointInstanceLaw.mass jointInstanceQualifying

  multiplicative :
    jointInstanceLaw.expectedQueries jointInstanceTree *
        ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ = 3 / 4

  multiplicativeCharge :
    matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps *
        jointInstanceLaw.mass jointInstanceQualifying = 3 / 8

theorem clause1_joint_distribution_concrete_instance : JointDistributionReceipt := by
  have hone : ‖(1 : Matrix Unit Unit ℂ)‖ = 1 := l2_norm_one_eq
  have hreal : ∀ c : ℝ, ‖(c : ℂ)‖ = |c| := by
    intro c
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hsub : ∀ a b : ℝ, ((a : ℂ) • (1 : Matrix Unit Unit ℂ)) -
      ((b : ℂ) • (1 : Matrix Unit Unit ℂ)) =
      (((a - b : ℝ) : ℂ)) • (1 : Matrix Unit Unit ℂ) := by
    intro a b
    rw [← sub_smul]
    congr 1
    push_cast
    rfl
  have hA : ‖jointInstanceTargetOne - jointInstanceTargetTwo‖ = 5 / 4 := by
    rw [show jointInstanceTargetTwo = (0 : Matrix Unit Unit ℂ) by rfl, sub_zero]
    rw [show jointInstanceTargetOne = ((5 / 4 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [norm_smul, hone, hreal (5 / 4), abs_of_nonneg (by norm_num), mul_one]
  have hd : ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ = 1 / 2 := by
    rw [show jointInstanceOracleOne = ((1 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [show jointInstanceOracleTwo = ((1 / 2 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [hsub]
    rw [show ((1 : ℝ) - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    rw [norm_smul, hone, hreal (1 / 2), abs_of_nonneg (by norm_num), mul_one]
  have hconst : matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo
      jointInstanceEps = 3 / 4 := by
    rw [matrixResponseConstant, hA]
    norm_num [jointInstanceEps]
  have hthr : responseQueryThreshold
      (matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps)
      ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ = 2 := by
    apply Nat.le_antisymm
    · exact (responseQueryThreshold_spec (by rw [hd]; norm_num)).mpr (by rw [hconst, hd]; norm_num)
    · have hnot : ¬ (responseQueryThreshold
          (matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps)
          ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ ≤ 1) := by
        intro h1
        have hle : ((1 : ℕ) : ℝ) * ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ ≥
            matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps :=
          (responseQueryThreshold_spec (by rw [hd]; norm_num)).mp h1
        rw [hd, hconst] at hle
        norm_num at hle
      exact Nat.succ_le_of_lt (Nat.lt_of_not_le hnot)
  have hq1 : jointInstanceTree.pathQueries [false, false] = 1 := rfl
  have hq3 : jointInstanceTree.pathQueries [true, false] = 2 := rfl
  have hworst : jointInstanceTree.worstCaseQueries = 2 := rfl
  have hexp : jointInstanceLaw.expectedQueries jointInstanceTree = 3 / 2 := by
    have h : jointInstanceLaw.expectedQueries jointInstanceTree =
        (1 / 2 : ℝ) * (jointInstanceTree.pathQueries [false, false] : ℝ) +
          (1 / 2 : ℝ) * (jointInstanceTree.pathQueries [true, false] : ℝ) := by
      simp [SignalBranchLaw.expectedQueries, jointInstanceLaw, jointInstanceSupport,
        jointInstanceTree]
    rw [h, hq1, hq3]
    ring
  have hmass : jointInstanceLaw.mass jointInstanceQualifying = 1 / 2 := by
    norm_num [SignalBranchLaw.mass, jointInstanceLaw, jointInstanceSupport,
      jointInstanceQualifying]
  have htail : jointInstanceLaw.tailMass jointInstanceQualifying = 1 / 2 := by
    norm_num [SignalBranchLaw.tailMass, jointInstanceLaw, jointInstanceSupport,
      jointInstanceQualifying]
  have hlev1 : branchLevelMass jointInstanceTree jointInstanceLaw 1 = 1 / 2 := by
    simp (config := { decide := true }) [List.filter, branchLevelMass, jointInstanceLaw,
      jointInstanceSupport, jointInstanceTree]
  have hlev2 : branchLevelMass jointInstanceTree jointInstanceLaw 2 = 1 / 2 := by
    simp (config := { decide := true }) [List.filter, branchLevelMass, jointInstanceLaw,
      jointInstanceSupport, jointInstanceTree]
  have hqlev1 : branchQualifyingLevelMass jointInstanceTree jointInstanceLaw
      jointInstanceQualifying 1 = 0 := by
    simp (config := { decide := true }) [List.filter, branchQualifyingLevelMass,
      jointInstanceLaw, jointInstanceSupport, jointInstanceQualifying, jointInstanceTree]
  have hqlev2 : branchQualifyingLevelMass jointInstanceTree jointInstanceLaw
      jointInstanceQualifying 2 = 1 / 2 := by
    simp (config := { decide := true }) [List.filter, branchQualifyingLevelMass,
      jointInstanceLaw, jointInstanceSupport, jointInstanceQualifying, jointInstanceTree]
  exact JointDistributionReceipt.mk hq1 hq3 hworst hexp hmass htail hlev1 hlev2 hqlev1 hqlev2
    hconst hd hthr (by rw [hthr, hmass]; norm_num) (by rw [hthr, hmass, hexp]; norm_num)
    (by rw [hexp, hd]; norm_num) (by rw [hconst, hmass]; norm_num)

theorem clause1_joint_distribution_instance_qualifying :
    jointInstanceTree.pathQueries [false, false] = 1 ∧
    jointInstanceTree.pathQueries [true, false] = 2 ∧
    (jointInstanceTree.pathQueries [false, false] : ℝ) *
        ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ <
      matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps ∧
    matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo jointInstanceEps ≤
      (jointInstanceTree.pathQueries [true, false] : ℝ) *
        ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ := by
  have hone : ‖(1 : Matrix Unit Unit ℂ)‖ = 1 := l2_norm_one_eq
  have hreal : ∀ c : ℝ, ‖(c : ℂ)‖ = |c| := by
    intro c
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hsub : ∀ a b : ℝ, ((a : ℂ) • (1 : Matrix Unit Unit ℂ)) -
      ((b : ℂ) • (1 : Matrix Unit Unit ℂ)) =
      (((a - b : ℝ) : ℂ)) • (1 : Matrix Unit Unit ℂ) := by
    intro a b
    rw [← sub_smul]
    congr 1
    push_cast
    rfl
  have hA : ‖jointInstanceTargetOne - jointInstanceTargetTwo‖ = 5 / 4 := by
    rw [show jointInstanceTargetTwo = (0 : Matrix Unit Unit ℂ) by rfl, sub_zero]
    rw [show jointInstanceTargetOne = ((5 / 4 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [norm_smul, hone, hreal (5 / 4), abs_of_nonneg (by norm_num), mul_one]
  have hd : ‖jointInstanceOracleOne - jointInstanceOracleTwo‖ = 1 / 2 := by
    rw [show jointInstanceOracleOne = ((1 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [show jointInstanceOracleTwo = ((1 / 2 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) by rfl]
    rw [hsub]
    rw [show ((1 : ℝ) - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    rw [norm_smul, hone, hreal (1 / 2), abs_of_nonneg (by norm_num), mul_one]
  have hconst : matrixResponseConstant jointInstanceTargetOne jointInstanceTargetTwo
      jointInstanceEps = 3 / 4 := by
    rw [matrixResponseConstant, hA]
    norm_num [jointInstanceEps]
  have hq1 : jointInstanceTree.pathQueries [false, false] = 1 := rfl
  have hq3 : jointInstanceTree.pathQueries [true, false] = 2 := rfl
  refine ⟨hq1, hq3, ?_, ?_⟩
  · rw [hq1, hd, hconst]
    norm_num
  · rw [hq3, hd, hconst]
    norm_num

structure DirectionResolvedMachineReceipt where

  forwardGateCost : asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) false = 1

  backwardGateCost : asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) true = 3

  minGateCost : asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) = 1

  forwardReadBits : asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) false = 1

  backwardReadBits : asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) true = 2

  minBitCost : asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) = 1

  forwardAccesses : wordForwardAccesses mixedDirectionWord = 1

  backwardAccesses : wordBackwardAccesses mixedDirectionWord = 1

  queryCount : adjointQueryCount mixedDirectionWord = 2

  realizedGateCost :
    asymmetricAccessModel.realizedWordGateCount (1 : Matrix Unit Unit ℂ) mixedDirectionWord = 4

  realizedBitCost :
    asymmetricAccessModel.realizedWordBitCost (1 : Matrix Unit Unit ℂ) mixedDirectionWord = 3

  gateDecomposition :
    (asymmetricAccessModel.realizedWordGateCount (1 : Matrix Unit Unit ℂ)
        mixedDirectionWord : ℝ) =
      (asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ) * 2 +
        ((asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ) * ((2 : ℝ) - 2) +
          (((asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) false : ℝ) -
              (asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1 +
           ((asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) true : ℝ) -
              (asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1))

  bitDecomposition :
    (asymmetricAccessModel.realizedWordBitCost (1 : Matrix Unit Unit ℂ)
        mixedDirectionWord : ℝ) =
      (asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ) * 2 +
        ((asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ) * ((2 : ℝ) - 2) +
          (((asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) false : ℝ) -
              (asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1 +
           ((asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) true : ℝ) -
              (asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1))

theorem clause3_direction_resolved_machine_cost_concrete_instance :
    DirectionResolvedMachineReceipt := by
  have hcost : asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) false = 1 ∧
      asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) true = 3 ∧
      asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) false = 1 ∧
      asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) true = 2 := by
    simp [OracleAccessModel.accessGateCost, GateCount, asymmetricAccessModel]
  have hmin : asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) = 1 ∧
      asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) = 1 := by
    simp [OracleAccessModel.minAccessGateCost, OracleAccessModel.minAccessBitCost, hcost]
  have hcnt : wordForwardAccesses mixedDirectionWord = 1 ∧
      wordBackwardAccesses mixedDirectionWord = 1 ∧
      adjointQueryCount mixedDirectionWord = 2 := by
    simp [wordForwardAccesses, wordBackwardAccesses, adjointQueryCount, mixedDirectionWord]
  have hreal : asymmetricAccessModel.realizedWordGateCount (1 : Matrix Unit Unit ℂ)
        mixedDirectionWord = 4 ∧
      asymmetricAccessModel.realizedWordBitCost (1 : Matrix Unit Unit ℂ)
        mixedDirectionWord = 3 := by
    simp [OracleAccessModel.realizedWordGateCount, OracleAccessModel.realizedWordBitCost, hcost,
      mixedDirectionWord]
  have hdec : (asymmetricAccessModel.realizedWordGateCount (1 : Matrix Unit Unit ℂ)
        mixedDirectionWord : ℝ) =
      (asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ) * 2 +
        ((asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ) * ((2 : ℝ) - 2) +
          (((asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) false : ℝ) -
              (asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1 +
           ((asymmetricAccessModel.accessGateCost (1 : Matrix Unit Unit ℂ) true : ℝ) -
              (asymmetricAccessModel.minAccessGateCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1)) ∧
      (asymmetricAccessModel.realizedWordBitCost (1 : Matrix Unit Unit ℂ)
        mixedDirectionWord : ℝ) =
      (asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ) * 2 +
        ((asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ) * ((2 : ℝ) - 2) +
          (((asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) false : ℝ) -
              (asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1 +
           ((asymmetricAccessModel.readBits (1 : Matrix Unit Unit ℂ) true : ℝ) -
              (asymmetricAccessModel.minAccessBitCost (1 : Matrix Unit Unit ℂ) : ℝ)) * 1)) := by
    simp [hreal, hmin, hcost]
    constructor <;> norm_num
  exact DirectionResolvedMachineReceipt.mk hcost.1 hcost.2.1 hmin.1 hcost.2.2.1 hcost.2.2.2 hmin.2
    hcnt.1 hcnt.2.1 hcnt.2.2 hreal.1 hreal.2 hdec.1 hdec.2

theorem clause1_endpoint :
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (p : List Bool) (A B : Matrix I I ℂ) (eps : ℝ),
      IsIsometry L → IsIsometry R → tree.WellFormed →
      (∀ c ∈ tree.pathWord p, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
      0 ≤ eps →
      ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ ≤ eps →
      ‖B - compress L (evaluate O₂ (tree.pathWord p)) R‖ ≤ eps →
      max 0 (‖A - B‖ - 2 * eps) ≤ (tree.pathQueries p : ℝ) * ‖O₁ - O₂‖) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (A B : Matrix I I ℂ) (eps : ℝ),
      IsIsometry L → IsIsometry R → tree.WellFormed →
      (∀ p : List Bool, ∀ c ∈ tree.pathWord p,
        ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
      0 ≤ eps →
      (∀ p : List Bool, ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ ≤ eps) →
      (∀ p : List Bool, ‖B - compress L (evaluate O₂ (tree.pathWord p)) R‖ ≤ eps) →
      (tree.worstCaseQueries : ℝ) * ‖O₁ - O₂‖ ≥ max 0 (‖A - B‖ - 2 * eps) ∧
      (∀ law : SignalBranchLaw, law.expectedQueries tree * ‖O₁ - O₂‖ ≥
        max 0 (‖A - B‖ - 2 * eps))) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I]
      (tree : AdaptiveSignalTree I) (S : List (List Bool)) (law : SignalBranchLaw)
      (A B : Matrix I I ℂ) (eps d : ℝ),
      0 ≤ d →
      (∀ p ∈ S, (tree.pathQueries p : ℝ) * d ≥ max 0 (‖A - B‖ - 2 * eps)) →
      law.expectedQueries tree * d ≥ max 0 (‖A - B‖ - 2 * eps) * law.mass S) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (S : List (List Bool)) (law : SignalBranchLaw)
      (A B : Matrix I I ℂ) (eps : ℝ),
      0 ≤ eps → 0 < ‖O₁ - O₂‖ →
      IsIsometry L → IsIsometry R → tree.WellFormed →
      (∀ p : List Bool, ∀ c ∈ tree.pathWord p,
        ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
      (∀ p ∈ S, ‖A - compress L (evaluate O₁ (tree.pathWord p)) R‖ ≤ eps) →
      (∀ p ∈ S, ‖B - compress L (evaluate O₂ (tree.pathWord p)) R‖ ≤ eps) →
      (∀ p ∈ S, responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖
          ≤ tree.pathQueries p) ∧
      (∀ k : ℕ, k < responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ →
        branchQualifyingLevelMass tree law S k = 0) ∧
      law.expectedQueries tree =
          ((law.support.filter (fun e => decide (e.1 ∈ S))).map
            (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum +
          ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
            (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ∧
      law.expectedQueries tree ≥
          (responseQueryThreshold (matrixResponseConstant A B eps) ‖O₁ - O₂‖ : ℝ) * law.mass S ∧
      law.mass S + law.tailMass S = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I _ _ _ L R O₁ O₂ tree p A B eps hL hR hWF hguard heps ha hb
    exact clause1_matrix_family_adaptive_lower_bound I L R O₁ O₂ tree p A B eps hL hR hWF hguard
      heps ha hb
  · intro I _ _ _ L R O₁ O₂ tree A B eps hL hR hWF hguard heps ha hb
    have h := clause1_matrix_family_worst_case_and_expected_lower_bound I L R O₁ O₂ tree A B eps
      hL hR hWF hguard heps ha hb
    simpa [matrixResponseConstant] using! h
  · intro I _ _ tree S law A B eps d hd hS
    have h := clause1_matrix_family_structural_tail_transport I tree S law A B eps d hd hS
    simpa [matrixResponseConstant] using! h
  · intro I _ _ _ L R O₁ O₂ tree S law A B eps heps hd hL hR hWF hguard ha hb
    exact clause1_matrix_family_joint_distribution I L R O₁ O₂ tree S law A B eps
      heps hd hL hR hWF hguard ha hb

theorem clause2_endpoint :
    (∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix H I ℂ) (O₁ O₂ : Matrix H H ℂ)
      (word : List (AdjointStep H)) (A B : Matrix I I ℂ) (eps : ℝ),
      IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
      (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
      0 ≤ eps →
      ‖A - compress L (evaluate O₁ word) R‖ ≤ eps →
      ‖B - compress L (evaluate O₂ word) R‖ ≤ eps →
      max 0 (‖A - B‖ - 2 * eps) ≤ (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (F : MatrixFamily I) (z₁ z₂ : ℝ) (L R : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (A B : Matrix I I ℂ) (eps : ℝ),
      BoundedMatrixFamily F → IsIsometry L → IsIsometry R → tree.WellFormed →
      (∀ p : List Bool, WellFormedGates (tree.pathWord p)) →
      0 ≤ eps →
      (∀ p : List Bool, ‖A - compress L (evaluate (F z₁) (tree.pathWord p)) R‖ ≤ eps) →
      (∀ p : List Bool, ‖B - compress L (evaluate (F z₂) (tree.pathWord p)) R‖ ≤ eps) →
      (tree.worstCaseQueries : ℝ) * ‖F z₁ - F z₂‖ ≥ max 0 (‖A - B‖ - 2 * eps) ∧
      (∀ law : SignalBranchLaw, law.expectedQueries tree * ‖F z₁ - F z₂‖ ≥
        max 0 (‖A - B‖ - 2 * eps))) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I]
      (L R : Matrix I I ℂ) (O₁ O₂ : Matrix I I ℂ)
      (word : List (AdjointStep I)) (A B : Matrix I I ℂ) (eps : ℝ),
      O₁ = O₂ →
      ‖A - compress L (evaluate O₁ word) R‖ ≤ eps →
      ‖B - compress L (evaluate O₂ word) R‖ ≤ eps →
      ‖A - B‖ ≤ 2 * eps) := by
  refine ⟨?_, ?_, ?_⟩
  · intro H I _ _ _ _ _ L R O₁ O₂ word A B eps hL hR hWF hguard heps ha hb
    exact clause2_matrix_family_response_lower_bound H I L R O₁ O₂ word A B eps hL hR hWF hguard
      heps ha hb
  · intro I _ _ _ F z₁ z₂ L R tree A B eps hF hL hR hWF hgates heps ha hb
    have h := clause2_bounded_family_adaptive_response_lower_bound I F z₁ z₂ L R tree A B eps
      hF hL hR hWF hgates heps ha hb
    simpa [matrixResponseConstant] using! h
  · intro I _ _ L R O₁ O₂ word A B eps hEq ha hb
    exact clause2_family_coincidence_forces_target_gap I L R O₁ O₂ word A B eps hEq ha hb

theorem clause3_realized_word_total_bit_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    M.realizedWordBitCost O word + wordAddressBits word =
        wordForwardAccesses word * (M.readBits O false + accessAddressBits (Fintype.card I)) +
          wordBackwardAccesses word * (M.readBits O true + accessAddressBits (Fintype.card I)) := by
  intro I _ _ M O word
  rw [clause3_realized_word_bit_cost_is_direction_resolved]
  simp only [wordAddressBits]
  ring

theorem clause3_query_forces_address_bit_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I)
      (O : Matrix I I ℂ) (word : List (AdjointStep I)) (q : ℝ),
    0 ≤ q → q ≤ (adjointQueryCount word : ℝ) →
      (wordAddressBits word : ℝ) ≥ q * (accessAddressBits (Fintype.card I) : ℝ) := by
  intro I _ _ M O word q hq hle
  have hcount : wordForwardAccesses word + wordBackwardAccesses word = adjointQueryCount word :=
    clause3_word_access_counts I word
  have h1 : ((wordForwardAccesses word + wordBackwardAccesses word : ℕ) : ℝ)
      = (adjointQueryCount word : ℝ) := by exact_mod_cast hcount
  have hab : (0 : ℝ) ≤ (accessAddressBits (Fintype.card I) : ℝ) := by positivity
  have hmul : q * (accessAddressBits (Fintype.card I) : ℝ)
      ≤ (adjointQueryCount word : ℝ) * (accessAddressBits (Fintype.card I) : ℝ) :=
    mul_le_mul_of_nonneg_right hle hab
  have h2 : (wordAddressBits word : ℝ)
      = ((wordForwardAccesses word + wordBackwardAccesses word : ℕ) : ℝ) *
        (accessAddressBits (Fintype.card I) : ℝ) := by
    simp only [wordAddressBits]
    push_cast
    ring
  rw [h2, h1]
  exact hmul

theorem clause3_address_bits_sufficient :
    ∀ (I : Type) [Fintype I], Fintype.card I < 2 ^ accessAddressBits (Fintype.card I) := by
  intro I _
  exact Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs.addressBitsFor_sufficient
      (Fintype.card I)

theorem clause3_endpoint :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)) (q : ℝ),
      0 ≤ q → q ≤ (adjointQueryCount word : ℝ) →
      (M.minAccessGateCost O : ℝ) * q ≤ (GateCount (M.signalWordCircuit O word) : ℝ) ∧
      (M.minAccessBitCost O : ℝ) * q ≤ (M.signalWordAccount O word).classicalBits ∧
      (adjointQueryCount word : ℕ) ≤ (M.signalWordAccount O word).depth) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (M : OracleAccessModel I) (O₁ O₂ : Matrix I I ℂ)
      (word : List (AdjointStep I)) (A B : Matrix I I ℂ) (eps : ℝ),
      0 < ‖O₁ - O₂‖ →
      (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
      WellFormedAdjointCircuit word →
      max 0 (‖A - B‖ - 2 * eps) ≤ (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ →
      (M.minAccessGateCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) ≤
          (GateCount (M.signalWordCircuit O₁ word) : ℝ) ∧
      (M.minAccessBitCost O₁ : ℝ) * (max 0 (‖A - B‖ - 2 * eps) / ‖O₁ - O₂‖) ≤
          (M.signalWordAccount O₁ word).classicalBits ∧
      (adjointQueryCount word : ℕ) ≤ (M.signalWordAccount O₁ word).depth) ∧
    (‖sharpnessTargetOne - compress (1 : Matrix Unit Unit ℂ)
        (evaluate sharpnessOracleOne sharpnessWord) (1 : Matrix Unit Unit ℂ)‖ = sharpnessEps ∧
      ‖sharpnessTargetTwo - compress (1 : Matrix Unit Unit ℂ)
        (evaluate sharpnessOracleTwo sharpnessWord) (1 : Matrix Unit Unit ℂ)‖ = sharpnessEps ∧
      ‖sharpnessOracleOne - sharpnessOracleTwo‖ = 1 / 2 ∧
      ‖sharpnessTargetOne - sharpnessTargetTwo‖ = 1 ∧
      matrixResponseConstant sharpnessTargetOne sharpnessTargetTwo sharpnessEps = 1 / 2 ∧
      (adjointQueryCount sharpnessWord : ℝ) *
        ‖sharpnessOracleOne - sharpnessOracleTwo‖ = 1 / 2 ∧
      max 0 (‖sharpnessTargetOne - sharpnessTargetTwo‖ - sharpnessEps) = 3 / 4 ∧
      3 / 4 > (adjointQueryCount sharpnessWord : ℝ) *
        ‖sharpnessOracleOne - sharpnessOracleTwo‖) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)) (q : ℝ),
      0 ≤ q → q ≤ (adjointQueryCount word : ℝ) →
      (M.realizedWordGateCount O word : ℝ) =
          (M.minAccessGateCost O : ℝ) * q +
            ((M.minAccessGateCost O : ℝ) * ((adjointQueryCount word : ℝ) - q) +
              ((M.accessGateCost O false - M.minAccessGateCost O) * (wordForwardAccesses word : ℝ) +
               (M.accessGateCost O true - M.minAccessGateCost O) * (wordBackwardAccesses word : ℝ))) ∧
      (M.realizedWordBitCost O word : ℝ) =
          (M.minAccessBitCost O : ℝ) * q +
            ((M.minAccessBitCost O : ℝ) * ((adjointQueryCount word : ℝ) - q) +
              ((M.readBits O false - M.minAccessBitCost O) * (wordForwardAccesses word : ℝ) +
               (M.readBits O true - M.minAccessBitCost O) * (wordBackwardAccesses word : ℝ)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I _ _ M O word q hq hle
    exact clause3_query_bound_trips_the_machine_ledgers I M O word q hq hle
  · intro I _ _ _ M O₁ O₂ word A B eps hgap hguard hWF hbound
    exact clause3_matrix_family_separation_forces_machine_cost I M O₁ O₂ word A B eps
      hgap hguard hWF hbound
  · exact clause2_matrix_family_slab_is_sharp
  · intro I _ _ M O word q hq hle
    exact clause3_query_forced_cost_decomposition I M O word q hq hle

theorem clause3_machine_ledger_endpoint :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)) (q : ℝ),
      0 ≤ q → q ≤ (adjointQueryCount word : ℝ) →
        (wordAddressBits word : ℝ) ≥ q * (accessAddressBits (Fintype.card I) : ℝ)) ∧
    (∀ (I : Type) [Fintype I],
      Fintype.card I < 2 ^ accessAddressBits (Fintype.card I)) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
      M.realizedWordBitCost O word + wordAddressBits word =
        wordForwardAccesses word * (M.readBits O false + accessAddressBits (Fintype.card I)) +
          wordBackwardAccesses word * (M.readBits O true + accessAddressBits (Fintype.card I))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _ _ M O word q hq hle
    exact clause3_query_forces_address_bit_cost I M O word q hq hle
  · intro I _
    exact clause3_address_bits_sufficient I
  · intro I _ _ M O word
    exact clause3_realized_word_total_bit_cost I M O word

end Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponse
