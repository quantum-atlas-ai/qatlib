/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBoundDefs

/-!
# Hybrid signal-response lower bounds

This module derives scalar signal-response query lower bounds from a hybrid estimate
for well-formed words with contractive instruction matrices. Isometric compression
transfers oracle separation to approximate scalar targets, using the method of
[BennettEtAl1997].

Pathwise bounds extend to worst-case and branch-law expected counts, with examples
distinguishing expected from worst-case queries and showing the failure of comparing
different oracle-dependent words. Machine realizations then transfer query lower
bounds to gate, read-bit, and depth charges with explicit ledger identities.

## Main statements

* `clause2_general_hybrid_bound`: word output distance is at most query count times oracle
  distance.
* `clause1_adaptive_worst_case_and_expected_lower_bound`: scalar response bounds for adaptive
  trees.
* `clause1_oracle_dependent_branch_counterexample`: a failure when the compared words differ.
* `clause3_endpoint`: machine cost bounds, zero peak ledger fields, and realization semantics.

## References

* [Bennett et al., 1997][BennettEtAl1997]
* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.AdaptiveSignalTree
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalBranchLaw
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {H I W : Type}

/-- An isometric matrix has operator norm at most one. -/
private theorem isometry_norm_le_one {H O : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] {L : Matrix H O ℂ} (h : IsIsometry L) :
    ‖L‖ ≤ 1 := by
  have hsq : ‖L‖ * ‖L‖ = ‖(1 : Matrix O O ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self L, h]
  have h1 : ‖(1 : Matrix O O ℂ)‖ ≤ 1 := l2_norm_one_le
  have h2 : ‖L‖ ^ 2 ≤ 1 := by
    nlinarith [hsq, h1, sq_nonneg (‖L‖), norm_nonneg L]
  exact (sq_le_one_iff₀ (norm_nonneg L)).mp h2

/-- The difference of compressed matrices equals `Lᴴ * (A - B) * R`. -/
private theorem compress_sub {H O I : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (A B : Matrix H H ℂ) :
    compress L A R - compress L B R = Lᴴ * (A - B) * R := by
  show Lᴴ * A * R - Lᴴ * B * R = Lᴴ * (A - B) * R
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]

/-- Compression by two isometries does not increase the operator-norm distance between matrices. -/
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

/-- A word whose instruction matrices all have norm at most one evaluates to a matrix of norm at
most one. -/
private theorem norm_evaluate_le_one : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (cs : List (AdjointStep I)),
    (∀ c ∈ cs, ‖instructionMatrix O c‖ ≤ 1) → ‖evaluate O cs‖ ≤ 1 := by
  intro I _ _ O cs
  induction cs with
  | nil =>
    intro _
    have hE : evaluate O ([] : List (AdjointStep I)) = 1 := rfl
    rw [hE]
    exact l2_norm_one_le
  | cons c cs ih =>
    intro hg
    have hc : ‖instructionMatrix O c‖ ≤ 1 := hg c List.mem_cons_self
    have hg' : ∀ d ∈ cs, ‖instructionMatrix O d‖ ≤ 1 :=
      fun d hd => hg d (List.mem_cons_of_mem c hd)
    have hE : evaluate O (c :: cs) = instructionMatrix O c * evaluate O cs := rfl
    rw [hE]
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    have hmul : ‖instructionMatrix O c‖ * ‖evaluate O cs‖ ≤ (1 : ℝ) * 1 :=
      mul_le_mul hc (ih hg') (norm_nonneg _) (by norm_num)
    rwa [one_mul] at hmul

/-- A pointwise comparison of real functions on a list gives the corresponding comparison of
mapped sums, under the stated nonnegativity hypothesis. -/
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

/-- A fixed right multiplicative factor can be moved outside a mapped real sum. -/
private theorem list_sum_const_mul {α : Type} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map (fun a => f a * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- A mapped real sum splits into the sums over a Boolean filter and its complement. -/
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

/-- A mapped real sum is nonnegative if each summand on the list is nonnegative. -/
private theorem list_sum_nonneg_of {α : Type} (l : List α) (f : α → ℝ)
    (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self)
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    linarith

/-- Folding maximum over a natural-number list gives a result at least its initial accumulator. -/
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

/-- Folding maximum over a natural-number list is monotone in its initial accumulator. -/
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

/-- Every member of a natural-number list is at most its maximum obtained by folding from zero. -/
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

/-- Every adaptive signal tree has a nonempty list of paths. -/
private theorem paths_ne_nil : ∀ (tree : AdaptiveSignalTree H), tree.paths ≠ [] := by
  intro tree
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

/-- For a well-formed adjoint word whose instructions are contractive under both oracles, the
evaluated matrices differ in norm by at most query count times oracle distance. This is a
word-level hybrid estimate in the spirit of [BennettEtAl1997]. -/
theorem clause2_general_hybrid_bound :
    ∀ (H : Type) [Fintype H] [DecidableEq H] (O₁ O₂ : Matrix H H ℂ)
      (word : List (AdjointStep H)),
    WellFormedAdjointCircuit word →
    (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    ‖evaluate O₁ word - evaluate O₂ word‖ ≤
      (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ := by
  intro H _ _ O₁ O₂ word
  induction word with
  | nil =>
    intro _ _
    have h1 : evaluate O₁ ([] : List (AdjointStep H)) = 1 := rfl
    have h2 : evaluate O₂ ([] : List (AdjointStep H)) = 1 := rfl
    simp [h1, h2, adjointQueryCount]
  | cons c cs ih =>
    intro hWF hg
    obtain ⟨h1c, h2c⟩ := hg c List.mem_cons_self
    have hg' : ∀ d ∈ cs, ‖instructionMatrix O₁ d‖ ≤ 1 ∧ ‖instructionMatrix O₂ d‖ ≤ 1 :=
      fun d hd => hg d (List.mem_cons_of_mem c hd)
    have hWF' : WellFormedAdjointCircuit cs :=
      fun V hV => hWF V (List.mem_cons_of_mem _ hV)
    have h1 : ‖evaluate O₁ cs - evaluate O₂ cs‖ ≤
        (adjointQueryCount cs : ℝ) * ‖O₁ - O₂‖ := ih hWF' hg'
    have h2 : ‖evaluate O₂ cs‖ ≤ 1 :=
      norm_evaluate_le_one H O₂ cs (fun d hd => (hg' d hd).2)
    have hdec : evaluate O₁ (c :: cs) - evaluate O₂ (c :: cs) =
        instructionMatrix O₁ c * (evaluate O₁ cs - evaluate O₂ cs) +
          (instructionMatrix O₁ c - instructionMatrix O₂ c) * evaluate O₂ cs := by
      have hE1 : evaluate O₁ (c :: cs) = instructionMatrix O₁ c * evaluate O₁ cs := rfl
      have hE2 : evaluate O₂ (c :: cs) = instructionMatrix O₂ c * evaluate O₂ cs := rfl
      rw [hE1, hE2, Matrix.mul_sub, Matrix.sub_mul]
      abel
    have htri : ‖evaluate O₁ (c :: cs) - evaluate O₂ (c :: cs)‖ ≤
        ‖instructionMatrix O₁ c‖ * ‖evaluate O₁ cs - evaluate O₂ cs‖ +
          ‖instructionMatrix O₁ c - instructionMatrix O₂ c‖ * ‖evaluate O₂ cs‖ := by
      rw [hdec]
      exact le_trans (norm_add_le _ _)
        (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))
    refine le_trans htri ?_
    cases c with
    | gate V =>
      have h1c' : ‖V‖ ≤ 1 := by simpa [instructionMatrix] using! h1c
      have hq : adjointQueryCount (AdjointStep.gate V :: cs) = adjointQueryCount cs := rfl
      simp only [instructionMatrix, sub_self, norm_zero, zero_mul, _root_.add_zero, hq]
      exact le_trans (mul_le_mul_of_nonneg_right h1c' (norm_nonneg _))
        (by rw [one_mul]; exact h1)
    | forward =>
      have h1c' : ‖O₁‖ ≤ 1 := by simpa [instructionMatrix] using! h1c
      have hq : adjointQueryCount (AdjointStep.forward :: cs) = adjointQueryCount cs + 1 := rfl
      simp only [instructionMatrix, hq]
      push_cast
      have hm1 : ‖O₁‖ * ‖evaluate O₁ cs - evaluate O₂ cs‖ ≤
          1 * ((adjointQueryCount cs : ℝ) * ‖O₁ - O₂‖) :=
        mul_le_mul h1c' h1 (norm_nonneg _) (by norm_num)
      rw [one_mul] at hm1
      have hm2 : ‖O₁ - O₂‖ * ‖evaluate O₂ cs‖ ≤ ‖O₁ - O₂‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      rw [mul_one] at hm2
      nlinarith [norm_nonneg (O₁ - O₂), hm1, hm2]
    | backward =>
      have h1c' : ‖O₁‖ ≤ 1 := by
        rw [← Matrix.l2_opNorm_conjTranspose]
        simpa [instructionMatrix] using! h1c
      have hq : adjointQueryCount (AdjointStep.backward :: cs) =
          adjointQueryCount cs + 1 := rfl
      simp only [instructionMatrix, hq, ← Matrix.conjTranspose_sub,
        Matrix.l2_opNorm_conjTranspose]
      push_cast
      have hm1 : ‖O₁‖ * ‖evaluate O₁ cs - evaluate O₂ cs‖ ≤
          1 * ((adjointQueryCount cs : ℝ) * ‖O₁ - O₂‖) :=
        mul_le_mul h1c' h1 (norm_nonneg _) (by norm_num)
      rw [one_mul] at hm1
      have hm2 : ‖O₁ - O₂‖ * ‖evaluate O₂ cs‖ ≤ ‖O₁ - O₂‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      rw [mul_one] at hm2
      nlinarith [norm_nonneg (O₁ - O₂), hm1, hm2]

/-- With isometric compression, contractive instructions, and scalar-target approximation error
`eps ≥ 0`, `max 0 (|a - b| - 2 * eps)` is at most query count times oracle distance. -/
theorem clause2_general_response_lower_bound :
    ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix H I ℂ) (O₁ O₂ : Matrix H H ℂ)
      (word : List (AdjointStep H)) (a b eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    0 ≤ eps →
    ‖(a : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate O₁ word) R‖ ≤ eps →
    ‖(b : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate O₂ word) R‖ ≤ eps →
    max 0 (|a - b| - 2 * eps) ≤ (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ := by
  intro H I _ _ _ _ _ L R O₁ O₂ word a b eps hL hR hWF hguard heps ha hb
  have hdiff : ‖compress L (evaluate O₁ word) R - compress L (evaluate O₂ word) R‖ ≤
      ‖evaluate O₁ word - evaluate O₂ word‖ :=
    compress_contract L R _ _ hL hR
  have hhyb : ‖evaluate O₁ word - evaluate O₂ word‖ ≤
      (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ :=
    clause2_general_hybrid_bound H O₁ O₂ word hWF hguard
  have htarget : ‖(a : ℂ) • (1 : Matrix I I ℂ) - (b : ℂ) • (1 : Matrix I I ℂ)‖ = |a - b| := by
    rw [← sub_smul, ← Complex.ofReal_sub, norm_smul, l2_norm_one_eq, Complex.norm_real,
      Real.norm_eq_abs, mul_one]
  have hchain : ‖(a : ℂ) • (1 : Matrix I I ℂ) - (b : ℂ) • (1 : Matrix I I ℂ)‖ ≤
      eps + ((adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ + eps) := by
    have h1 : ‖(a : ℂ) • (1 : Matrix I I ℂ) - (b : ℂ) • (1 : Matrix I I ℂ)‖ ≤
        ‖(a : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate O₁ word) R‖ +
          ‖compress L (evaluate O₁ word) R - (b : ℂ) • (1 : Matrix I I ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub ((a : ℂ) • (1 : Matrix I I ℂ))
        (compress L (evaluate O₁ word) R) ((b : ℂ) • (1 : Matrix I I ℂ))
    have h2 : ‖compress L (evaluate O₁ word) R - (b : ℂ) • (1 : Matrix I I ℂ)‖ ≤
        ‖compress L (evaluate O₁ word) R - compress L (evaluate O₂ word) R‖ +
          ‖compress L (evaluate O₂ word) R - (b : ℂ) • (1 : Matrix I I ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub (compress L (evaluate O₁ word) R)
        (compress L (evaluate O₂ word) R) ((b : ℂ) • (1 : Matrix I I ℂ))
    have h3 : ‖compress L (evaluate O₂ word) R - (b : ℂ) • (1 : Matrix I I ℂ)‖ ≤ eps := by
      rw [norm_sub_rev]; exact hb
    have h4 : ‖evaluate O₁ word - evaluate O₂ word‖ ≤
        (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ := hhyb
    linarith
  have htri : |a - b| ≤ eps + ((adjointQueryCount word : ℝ) * ‖O₁ - O₂‖ + eps) := by
    rw [← htarget]
    exact hchain
  apply max_le
  · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  · linarith

/-- For `x` and `y` in `[-1, 1]`, the norm distance of their lifted scalar signals is at most
`scalarSignalDistance x y`. -/
theorem clause2_scalar_family_distance_le :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (x y : ℝ),
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 →
    ‖scalarSignalLift W x - scalarSignalLift W y‖ ≤ scalarSignalDistance x y := by
  intro W _ _ x y hx hy
  have hsub : scalarSignalLift W x - scalarSignalLift W y =
      TensorGate (scalarSignalReflection x - scalarSignalReflection y)
        (1 : Matrix W W ℂ) := by
    rw [scalarSignalLift, scalarSignalLift, tensorGate_sub_left]
  have hone : ‖(1 : Matrix W W ℂ)‖ ≤ 1 := l2_norm_one_le
  have hnn : 0 ≤ ‖scalarSignalReflection x - scalarSignalReflection y‖ := norm_nonneg _
  have hdist : ‖scalarSignalReflection x - scalarSignalReflection y‖ =
      scalarSignalDistance x y :=
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).1
  calc
    ‖scalarSignalLift W x - scalarSignalLift W y‖
        = ‖scalarSignalReflection x - scalarSignalReflection y‖ * ‖(1 : Matrix W W ℂ)‖ := by
          rw [hsub, l2_norm_tensorGate]
    _ ≤ ‖scalarSignalReflection x - scalarSignalReflection y‖ * 1 :=
          mul_le_mul_of_nonneg_left hone hnn
    _ = scalarSignalDistance x y := by rw [hdist, mul_one]

/-- On a nonempty workspace and for `x, y ∈ [-1, 1]`, the lifted scalar-signal norm distance
equals `scalarSignalDistance x y`. -/
theorem clause2_scalar_family_isometric_embedding :
    ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (x y : ℝ),
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 →
    ‖scalarSignalLift W x - scalarSignalLift W y‖ = scalarSignalDistance x y := by
  intro W _ _ _ x y hx hy
  have hsub : scalarSignalLift W x - scalarSignalLift W y =
      TensorGate (scalarSignalReflection x - scalarSignalReflection y)
        (1 : Matrix W W ℂ) := by
    rw [scalarSignalLift, scalarSignalLift, tensorGate_sub_left]
  have hone : ‖(1 : Matrix W W ℂ)‖ = 1 := l2_norm_one_eq
  have hdist : ‖scalarSignalReflection x - scalarSignalReflection y‖ =
      scalarSignalDistance x y :=
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).1
  calc
    ‖scalarSignalLift W x - scalarSignalLift W y‖
        = ‖scalarSignalReflection x - scalarSignalReflection y‖ := by
          rw [hsub, l2_norm_tensorGate, hone, mul_one]
    _ = scalarSignalDistance x y := hdist

/-- For distinct scalar parameters in `[-1, 1]`, a well-formed word approximating scalar targets
through isometric compression needs at least the nonnegative target gap after two errors
divided by scalar signal distance. -/
theorem clause2_general_bound_implies_scalar_bound :
    ∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
      (x y a b eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x ≠ y → 0 ≤ eps →
    ‖(a : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
    ‖(b : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
    (adjointQueryCount word : ℝ) ≥ max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y := by
  intro W I _ _ _ _ _ L R word x y a b eps hL hR hWF hx hy hxy heps ha hb
  have hguard : ∀ c ∈ word,
      ‖instructionMatrix (scalarSignalLift W x) c‖ ≤ 1 ∧
        ‖instructionMatrix (scalarSignalLift W y) c‖ ≤ 1 := by
    intro c hc
    have hxU : scalarSignalLift W x ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
      tensorGate_unitary (scalar_signal_actual_encoding x hx).2.1 (Submonoid.one_mem _)
    have hyU : scalarSignalLift W y ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
      tensorGate_unitary (scalar_signal_actual_encoding y hy).2.1 (Submonoid.one_mem _)
    cases c with
    | gate V =>
      have hV : V ∈ Matrix.unitaryGroup (Bool × W) ℂ := hWF V hc
      refine ⟨?_, ?_⟩ <;> simpa [instructionMatrix] using! l2_norm_unitary_le_one hV
    | forward =>
      refine ⟨?_, ?_⟩
      · simpa [instructionMatrix] using! l2_norm_unitary_le_one hxU
      · simpa [instructionMatrix] using! l2_norm_unitary_le_one hyU
    | backward =>
      refine ⟨?_, ?_⟩
      · simp only [instructionMatrix, Matrix.l2_opNorm_conjTranspose]
        exact l2_norm_unitary_le_one hxU
      · simp only [instructionMatrix, Matrix.l2_opNorm_conjTranspose]
        exact l2_norm_unitary_le_one hyU
  have hgeneral := clause2_general_response_lower_bound (Bool × W) I L R
    (scalarSignalLift W x) (scalarSignalLift W y) word a b eps hL hR hWF hguard heps ha hb
  have hdist : ‖scalarSignalLift W x - scalarSignalLift W y‖ ≤ scalarSignalDistance x y :=
    clause2_scalar_family_distance_le W x y hx hy
  have hpos : 0 < scalarSignalDistance x y :=
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.1 hxy
  refine (div_le_iff₀ hpos).mpr ?_
  have hstep : max 0 (|a - b| - 2 * eps) ≤
      (adjointQueryCount word : ℝ) * ‖scalarSignalLift W x - scalarSignalLift W y‖ := hgeneral
  have hnn : 0 ≤ (adjointQueryCount word : ℝ) := Nat.cast_nonneg _
  exact le_trans hstep (mul_le_mul_of_nonneg_left hdist hnn)

/-- For controlled unitary oracles and a well-formed word with the stated contraction bounds,
evaluated-word distance is at most query count times controlled-oracle distance. -/
theorem clause2_controlled_access_covered :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (O₁ O₂ : Matrix I I ℂ)
      (word : List (AdjointStep (Bool × I))),
    O₁ ∈ Matrix.unitaryGroup I ℂ → O₂ ∈ Matrix.unitaryGroup I ℂ →
    WellFormedAdjointCircuit word →
    (∀ c ∈ word, ‖instructionMatrix (controlOracle O₁) c‖ ≤ 1 ∧
        ‖instructionMatrix (controlOracle O₂) c‖ ≤ 1) →
    ‖evaluate (controlOracle O₁) word - evaluate (controlOracle O₂) word‖ ≤
      (adjointQueryCount word : ℝ) * ‖controlOracle O₁ - controlOracle O₂‖ := by
  intro I _ _ O₁ O₂ word hU₁ hU₂ hWF hguard
  exact clause2_general_hybrid_bound (Bool × I) (controlOracle O₁)
      (controlOracle O₂) word hWF hguard

/-- Each fixed path of a well-formed adaptive tree satisfies the hybrid norm estimate when its
instruction matrices are contractive for both oracles. -/
theorem clause2_measurement_feedback_covered :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (p : List Bool),
    tree.WellFormed →
    (∀ c ∈ tree.pathWord p, ‖instructionMatrix O₁ c‖ ≤ 1 ∧
        ‖instructionMatrix O₂ c‖ ≤ 1) →
    ‖evaluate O₁ (tree.pathWord p) - evaluate O₂ (tree.pathWord p)‖ ≤
      (tree.pathQueries p : ℝ) * ‖O₁ - O₂‖ := by
  intro I _ _ O₁ O₂ tree p hWF hguard
  have hw : WellFormedAdjointCircuit (tree.pathWord p) := tree.pathWord_wellFormed p hWF
  exact clause2_general_hybrid_bound I O₁ O₂ (tree.pathWord p) hw hguard

/-- If every path of a well-formed adaptive tree approximates the two scalar targets through
isometric compression, every path meets the target-gap-to-scalar-distance query lower bound
under the stated parameter and error assumptions. -/
theorem clause1_adaptive_pathwise_response_lower_bound :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (tree : AdaptiveSignalTree (Bool × W))
      (L R : Matrix (Bool × W) Unit ℂ) (x y a b eps : ℝ),
    IsIsometry L → IsIsometry R → tree.WellFormed →
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x ≠ y → 0 ≤ eps →
    (∀ p : List Bool,
      ‖(a : ℂ) • (1 : Matrix Unit Unit ℂ) -
        compress L (evaluate (scalarSignalLift W x) (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p : List Bool,
      ‖(b : ℂ) • (1 : Matrix Unit Unit ℂ) -
        compress L (evaluate (scalarSignalLift W y) (tree.pathWord p)) R‖ ≤ eps) →
    ∀ p : List Bool, (tree.pathQueries p : ℝ) ≥
      max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y := by
  intro W _ _ tree L R x y a b eps hL hR hWF hx hy hxy heps ha hb p
  have hw : WellFormedAdjointCircuit (tree.pathWord p) := tree.pathWord_wellFormed p hWF
  obtain ⟨hbound, _⟩ := scalar_signal_actual_response_query_lower_bound W Unit L R
    (tree.pathWord p) x y a b eps hL hR hw hx hy hxy heps (ha p) (hb p)
  have hq : (tree.pathQueries p : ℝ) = (adjointQueryCount (tree.pathWord p) : ℝ) := rfl
  rw [hq]
  exact hbound

/-- Under the scalar approximation hypotheses on every path, both worst-case queries and
expected queries under every branch law are bounded below by the nonnegative target gap
after two errors divided by scalar signal distance. -/
theorem clause1_adaptive_worst_case_and_expected_lower_bound :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (tree : AdaptiveSignalTree (Bool × W))
      (L R : Matrix (Bool × W) Unit ℂ) (x y a b eps : ℝ),
    IsIsometry L → IsIsometry R → tree.WellFormed →
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x ≠ y → 0 ≤ eps →
    (∀ p : List Bool,
      ‖(a : ℂ) • (1 : Matrix Unit Unit ℂ) -
        compress L (evaluate (scalarSignalLift W x) (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p : List Bool,
      ‖(b : ℂ) • (1 : Matrix Unit Unit ℂ) -
        compress L (evaluate (scalarSignalLift W y) (tree.pathWord p)) R‖ ≤ eps) →
    (tree.worstCaseQueries : ℝ) ≥ max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y ∧
    (∀ law : SignalBranchLaw, law.expectedQueries tree ≥
      max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y) := by
  intro W _ _ tree L R x y a b eps hL hR hWF hx hy hxy heps ha hb
  have hpath : ∀ p : List Bool, (tree.pathQueries p : ℝ) ≥
      max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y :=
    clause1_adaptive_pathwise_response_lower_bound W tree L R x y a b eps hL hR hWF hx hy hxy heps ha hb
  have hc : 0 ≤ max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y :=
    div_nonneg (le_max_left _ _) (le_of_lt
      ((scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.1 hxy))
  have hworst : (tree.worstCaseQueries : ℝ) ≥ max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y := by
    have hmem : ∀ p ∈ tree.paths, tree.pathQueries p ≤ tree.worstCaseQueries := by
      intro p hp
      have hmem' : tree.pathQueries p ∈ (tree.paths.map (tree.pathQueries) : List ℕ) :=
        List.mem_map.mpr ⟨p, hp, rfl⟩
      have h := foldl_max_ge_mem (tree.paths.map (tree.pathQueries)) (tree.pathQueries p) hmem'
      exact h
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (paths_ne_nil tree)
    have hq : (tree.pathQueries p : ℝ) ≤ (tree.worstCaseQueries : ℝ) :=
      Nat.cast_le.2 (hmem p hp)
    exact le_trans (hpath p) hq
  constructor
  · exact hworst
  · intro law
    have hsum : (law.support.map (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ≥
        (law.support.map (fun e => e.2 *
          (max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y))).sum := by
      apply list_sum_le_sum_pointwise
      · intro e he
        exact mul_le_mul_of_nonneg_left (hpath e.1) (law.nonneg e he)
      · intro e he
        exact mul_nonneg (law.nonneg e he) hc
    have hconst : (law.support.map (fun e => e.2 *
          (max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y))).sum =
        (law.support.map (fun e => e.2)).sum *
          (max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y) :=
      list_sum_const_mul _ _ _
    have htotal : (law.support.map (fun e => e.2)).sum = 1 := law.total
    calc
      law.expectedQueries tree =
          (law.support.map (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum := rfl
      _ ≥ (law.support.map (fun e => e.2 *
            (max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y))).sum := hsum
      _ = (law.support.map (fun e => e.2)).sum *
            (max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y) := hconst
      _ = 1 * (max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y) := by rw [htotal]
      _ = max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y := by ring

/-- For a path in the tree's path list, queries already used plus its remaining query budget
equal worst-case queries. -/
theorem clause1_remaining_budget :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (tree : AdaptiveSignalTree (Bool × W))
      (p : List Bool),
    p ∈ tree.paths →
    tree.pathQueries p + tree.remainingQueries p = tree.worstCaseQueries := by
  intro W _ _ tree p hp
  have hmem' : tree.pathQueries p ∈ (tree.paths.map (tree.pathQueries) : List ℕ) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have h := foldl_max_ge_mem (tree.paths.map (tree.pathQueries)) (tree.pathQueries p) hmem'
  have hle : tree.pathQueries p ≤ tree.worstCaseQueries := by
    simpa only [AdaptiveSignalTree.worstCaseQueries] using! h
  simp only [AdaptiveSignalTree.remainingQueries, AdaptiveSignalTree.worstCaseQueries]
  omega

/-- If every path in `S` uses at least `c ≥ 0` queries, expected queries are at least `c` times
the branch-law mass of `S`. -/
theorem clause1_structural_tail_transport :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (tree : AdaptiveSignalTree (Bool × W))
      (S : List (List Bool)) (law : SignalBranchLaw) (c : ℝ),
    0 ≤ c →
    (∀ p ∈ S, (tree.pathQueries p : ℝ) ≥ c) →
    law.expectedQueries tree ≥ c * law.mass S := by
  intro W _ _ tree S law c hc hS
  have hexp : law.expectedQueries tree =
      ((law.support.filter (fun e => decide (e.1 ∈ S))).map
        (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum +
      ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
        (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum := by
    rw [SignalBranchLaw.expectedQueries]
    exact list_sum_split law.support (fun e => decide (e.1 ∈ S))
      (fun e => e.2 * (tree.pathQueries e.1 : ℝ))
  have hgood : ((law.support.filter (fun e => decide (e.1 ∈ S))).map
      (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ≥
      ((law.support.filter (fun e => decide (e.1 ∈ S))).map (fun e => e.2 * c)).sum := by
    apply list_sum_le_sum_pointwise
    · intro e he
      have hmem := List.mem_filter.mp he
      exact mul_le_mul_of_nonneg_left (hS e.1 (of_decide_eq_true hmem.2))
        (law.nonneg e hmem.1)
    · intro e he
      have hmem := List.mem_filter.mp he
      exact mul_nonneg (law.nonneg e hmem.1) hc
  have hbad : ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
      (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum ≥ 0 :=
    list_sum_nonneg_of _ _ fun e he => by
      have hmem := List.mem_filter.mp he
      exact mul_nonneg (law.nonneg e hmem.1) (Nat.cast_nonneg _)
  have hconst : ((law.support.filter (fun e => decide (e.1 ∈ S))).map
      (fun e => e.2 * c)).sum = law.mass S * c := by
    rw [list_sum_const_mul]
    rfl
  calc
    law.expectedQueries tree =
        ((law.support.filter (fun e => decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum +
        ((law.support.filter (fun e => ! decide (e.1 ∈ S))).map
          (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum := hexp
    _ ≥ ((law.support.filter (fun e => decide (e.1 ∈ S))).map (fun e => e.2 * c)).sum + 0 := by
      linarith
    _ = law.mass S * c := by linarith [hconst]
    _ = c * law.mass S := mul_comm _ _

/-- An adaptive tree with one forward query on false-root paths and two forward queries on
true-root paths. -/
def clause1_variableQueryTree : AdaptiveSignalTree (Bool × Unit) :=
  .node [] (.node [.forward] .leaf .leaf) (.node [.forward, .forward] .leaf .leaf)

/-- The one-query path `[false, false]` and the two-query path `[true, false]`, each with weight
`1 / 2`. -/
noncomputable def clause1_variableQuerySupport : List (List Bool × ℝ) :=
  [([false, false], 1 / 2), ([true, false], 1 / 2)]

/-- The branch law giving equal weight to the specified one-query and two-query paths. -/
noncomputable def clause1_variableQueryLaw : SignalBranchLaw where
  support := clause1_variableQuerySupport
  nonneg := by
    intro e he
    have he' : e = ([false, false], 1 / 2) ∨ e = ([true, false], 1 / 2) := by
      rw [clause1_variableQuerySupport] at he
      simpa using! he
    rcases he' with h | h <;> subst h <;> norm_num
  total := by
    simp [clause1_variableQuerySupport]
    norm_num

/-- The example has path counts one and two, worst-case count two, and expected count `3 / 2`,
strictly below its worst-case count. -/
theorem clause1_adaptive_vs_fixed_gap :
    clause1_variableQueryTree.pathQueries [false, false] = 1 ∧
    clause1_variableQueryTree.pathQueries [true, false] = 2 ∧
    clause1_variableQueryTree.worstCaseQueries = 2 ∧
    clause1_variableQueryLaw.expectedQueries clause1_variableQueryTree = 3 / 2 ∧
    (clause1_variableQueryLaw.expectedQueries clause1_variableQueryTree : ℝ) <
        (clause1_variableQueryTree.worstCaseQueries : ℝ) := by
  have h1 : clause1_variableQueryTree.pathQueries [false, false] = 1 := by
    rfl
  have h2 : clause1_variableQueryTree.pathQueries [true, false] = 2 := by
    rfl
  have h3 : clause1_variableQueryTree.worstCaseQueries = 2 := by
    rfl
  have h4 : clause1_variableQueryLaw.expectedQueries clause1_variableQueryTree = 3 / 2 := by
    have hexp : clause1_variableQueryLaw.expectedQueries clause1_variableQueryTree =
        (1 / 2 : ℝ) * (clause1_variableQueryTree.pathQueries [false, false] : ℝ) +
        (1 / 2 : ℝ) * (clause1_variableQueryTree.pathQueries [true, false] : ℝ) := by
      simp [SignalBranchLaw.expectedQueries, clause1_variableQuerySupport, clause1_variableQueryLaw,
        clause1_variableQueryTree]
    rw [hexp, h1, h2]
    ring
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [h4, h3]
  norm_num

/-- The scalar signal distance between `1` and `7 / 8` equals `1 / 2`. -/
theorem clause1_scalarSignalDistance_one_seven_eighth : scalarSignalDistance 1 (7 / 8) = 1 / 2 := by
  have hsq : ((1 : ℝ) - 7 / 8) ^ 2 +
      (Real.sqrt (1 - (1 : ℝ) ^ 2) - Real.sqrt (1 - (7 / 8 : ℝ) ^ 2)) ^ 2 = (1 / 2) ^ 2 := by
    have h1 : Real.sqrt (1 - (1 : ℝ) ^ 2) = 0 := by
      have hz : (1 : ℝ) - (1 : ℝ) ^ 2 = 0 := by norm_num
      rw [hz, Real.sqrt_zero]
    rw [h1]
    have h2 : Real.sqrt (1 - (7 / 8 : ℝ) ^ 2) = Real.sqrt 15 / 8 := by
      have h : (1 : ℝ) - (7 / 8 : ℝ) ^ 2 = 15 / 64 := by norm_num
      rw [h, Real.sqrt_div (by norm_num)]
      have h64 : Real.sqrt 64 = 8 := by
        rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq]
        norm_num
      rw [h64]
    rw [h2]
    have hsq15 : (Real.sqrt 15) ^ 2 = 15 := Real.sq_sqrt (by norm_num)
    have hsq' : (0 - Real.sqrt 15 / 8) ^ 2 = 15 / 64 := by
      rw [show (0 - Real.sqrt 15 / 8) ^ 2 = (Real.sqrt 15) ^ 2 / 8 ^ 2 by ring, hsq15]
      norm_num
    rw [hsq']
    norm_num
  unfold scalarSignalDistance
  have hform : ((1 : ℝ) - 7 / 8) ^ 2 +
      (Real.sqrt (1 - (1 : ℝ) ^ 2) - Real.sqrt (1 - (7 / 8 : ℝ) ^ 2)) ^ 2 = (1 / 4 : ℝ) := by
    linarith [hsq]
  rw [hform]
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    have h1 : Real.sqrt ((1 / 2 : ℝ) ^ 2) = 1 / 2 := by
      rw [Real.sqrt_sq]
      norm_num
    have h2 : (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by ring
    rw [h2]
    exact h1
  exact hsqrt

/-- There exist different words and scalar parameters whose response difference exceeds the
first word's query count times scalar signal distance. -/
theorem clause1_oracle_dependent_branch_counterexample :
    ∃ (wₓ w_y : List (AdjointStep (Bool × Unit))) (x y : ℝ),
      wₓ ≠ w_y ∧
      |fiberResponse x wₓ - fiberResponse y w_y| >
        (adjointQueryCount wₓ : ℝ) * scalarSignalDistance x y := by
  refine ⟨[AdjointStep.forward],
    [AdjointStep.forward, AdjointStep.gate (TensorGate PauliX (1 : Matrix Unit Unit ℂ))],
    1, 7 / 8, ?_⟩
  have hfx : fiberResponse (1 : ℝ) [AdjointStep.forward] = 1 :=
    fiberResponse_forward 1
  have hfy : fiberResponse (7 / 8 : ℝ)
      [AdjointStep.forward, AdjointStep.gate (TensorGate PauliX (1 : Matrix Unit Unit ℂ))] =
        Real.sqrt 15 / 8 := by
    have h := fiberResponse_forward_x (7 / 8 : ℝ)
    have hsq : (1 : ℝ) - (7 / 8 : ℝ) ^ 2 = 15 / 64 := by norm_num
    have hsqrt : Real.sqrt (15 / 64 : ℝ) = Real.sqrt 15 / 8 := by
      rw [Real.sqrt_div (by norm_num)]
      have h64 : Real.sqrt 64 = 8 := by
        rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq]
        norm_num
      rw [h64]
    rwa [hsq, hsqrt] at h
  have hdist := clause1_scalarSignalDistance_one_seven_eighth
  have hq : adjointQueryCount (H := Bool × Unit) [AdjointStep.forward] = 1 := rfl
  have hlt : Real.sqrt 15 < 4 := by
    have h : (15 : ℝ) < 4 ^ 2 := by norm_num
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 h
  have hpos : 0 ≤ Real.sqrt 15 / 8 := by positivity
  constructor
  · intro hcontra
    have : [AdjointStep.forward] =
        [AdjointStep.forward, AdjointStep.gate (TensorGate PauliX (1 : Matrix Unit Unit ℂ))] := hcontra
    cases this
  · rw [hfx, hfy, hq, hdist]
    have habs : |(1 : ℝ) - Real.sqrt 15 / 8| = 1 - Real.sqrt 15 / 8 :=
      abs_of_nonneg (by linarith)
    rw [habs]
    linarith

open Qatlib
set_option warningAsError false

/-- The query counter of a dynamic-step list equals the sum of its step query counters. -/
private theorem counters_queries : ∀ (l : List DynStep),
    (counters l).queries = (l.map (fun s => s.stepAccount.queries)).sum := by
  intro l
  induction l with
  | nil => simp [counters, Account.zero]
  | cons s rest ih =>
    simp only [counters, Account.seq, List.map_cons, List.sum_cons, ih]

/-- The adjoint-query counter of a dynamic-step list equals the sum of its step adjoint-query
counters. -/
private theorem counters_adjoint_queries : ∀ (l : List DynStep),
    (counters l).adjointQueries = (l.map (fun s => s.stepAccount.adjointQueries)).sum := by
  intro l
  induction l with
  | nil => simp [counters, Account.zero]
  | cons s rest ih =>
    simp only [counters, Account.seq, List.map_cons, List.sum_cons, ih]

/-- The macro-gate counter of a dynamic-step list equals the sum of its step macro-gate
counters. -/
private theorem counters_macro_gates : ∀ (l : List DynStep),
    (counters l).macroGates = (l.map (fun s => s.stepAccount.macroGates)).sum := by
  intro l
  induction l with
  | nil => simp [counters, Account.zero]
  | cons s rest ih =>
    simp only [counters, Account.seq, List.map_cons, List.sum_cons, ih]

/-- The classical-bit counter of a dynamic-step list equals the sum of its step classical-bit
counters. -/
private theorem counters_classical_bits : ∀ (l : List DynStep),
    (counters l).classicalBits = (l.map (fun s => s.stepAccount.classicalBits)).sum := by
  intro l
  induction l with
  | nil => simp [counters, Account.zero]
  | cons s rest ih =>
    simp only [counters, Account.seq, List.map_cons, List.sum_cons, ih]

/-- The sum of forward-query step charges in a realized signal word equals the sum of
forward-access indicators in the source word. -/
private theorem word_forward_steps [Fintype I] [DecidableEq I]
    (M : OracleAccessModel I) (O : Matrix I I ℂ) (word : List (AdjointStep I)) :
    ((M.signalWordSteps O word).map (fun s => s.stepAccount.queries)).sum =
      (word.map OracleAccessModel.forwardAccessCount).sum := by
  induction word with
  | nil => simp [OracleAccessModel.signalWordSteps]
  | cons c cs ih =>
    have hsteps : M.signalWordSteps O (c :: cs) =
        M.stepSteps O c ++ M.signalWordSteps O cs := rfl
    rw [hsteps, List.map_append, List.sum_append]
    have hstep : ((M.stepSteps O c).map (fun s => s.stepAccount.queries)).sum =
        OracleAccessModel.forwardAccessCount c := by
      cases c <;>
        simp [OracleAccessModel.stepSteps, DynStep.stepAccount, Account.zero,
          OracleAccessModel.forwardAccessCount]
    rw [hstep, ih]
    simp [List.map_cons, List.sum_cons, OracleAccessModel.forwardAccessCount]

/-- The sum of adjoint-query step charges in a realized signal word equals the sum of
backward-access indicators in the source word. -/
private theorem word_backward_steps [Fintype I] [DecidableEq I]
    (M : OracleAccessModel I) (O : Matrix I I ℂ) (word : List (AdjointStep I)) :
    ((M.signalWordSteps O word).map (fun s => s.stepAccount.adjointQueries)).sum =
      (word.map OracleAccessModel.backwardAccessCount).sum := by
  induction word with
  | nil => simp [OracleAccessModel.signalWordSteps]
  | cons c cs ih =>
    have hsteps : M.signalWordSteps O (c :: cs) =
        M.stepSteps O c ++ M.signalWordSteps O cs := rfl
    rw [hsteps, List.map_append, List.sum_append]
    have hstep : ((M.stepSteps O c).map (fun s => s.stepAccount.adjointQueries)).sum =
        OracleAccessModel.backwardAccessCount c := by
      cases c <;>
        simp [OracleAccessModel.stepSteps, DynStep.stepAccount, Account.zero,
          OracleAccessModel.backwardAccessCount]
    rw [hstep, ih]
    simp [List.map_cons, List.sum_cons, OracleAccessModel.backwardAccessCount]

/-- The sum of macro-gate step charges in a realized signal word equals the sum of source
gate-step indicators. -/
private theorem word_gate_steps [Fintype I] [DecidableEq I]
    (M : OracleAccessModel I) (O : Matrix I I ℂ) (word : List (AdjointStep I)) :
    ((M.signalWordSteps O word).map (fun s => s.stepAccount.macroGates)).sum =
      (word.map OracleAccessModel.gateStepCount).sum := by
  induction word with
  | nil => simp [OracleAccessModel.signalWordSteps]
  | cons c cs ih =>
    have hsteps : M.signalWordSteps O (c :: cs) =
        M.stepSteps O c ++ M.signalWordSteps O cs := rfl
    rw [hsteps, List.map_append, List.sum_append]
    have hstep : ((M.stepSteps O c).map (fun s => s.stepAccount.macroGates)).sum =
        OracleAccessModel.gateStepCount c := by
      cases c <;>
        simp [OracleAccessModel.stepSteps, DynStep.stepAccount, Account.zero,
          OracleAccessModel.gateStepCount]
    rw [hstep, ih]
    simp [List.map_cons, List.sum_cons, OracleAccessModel.gateStepCount]

/-- The sum of classical-bit step charges in a realized signal word equals its realized word bit
cost. -/
private theorem word_bit_steps [Fintype I] [DecidableEq I]
    (M : OracleAccessModel I) (O : Matrix I I ℂ) (word : List (AdjointStep I)) :
    ((M.signalWordSteps O word).map (fun s => s.stepAccount.classicalBits)).sum =
      M.realizedWordBitCost O word := by
  induction word with
  | nil => simp [OracleAccessModel.signalWordSteps, OracleAccessModel.realizedWordBitCost]
  | cons c cs ih =>
    have hsteps : M.signalWordSteps O (c :: cs) =
        M.stepSteps O c ++ M.signalWordSteps O cs := rfl
    rw [hsteps, List.map_append, List.sum_append]
    have hstep : ((M.stepSteps O c).map (fun s => s.stepAccount.classicalBits)).sum =
        OracleAccessModel.instructionBitCost M O c := by
      cases c <;>
        simp [OracleAccessModel.stepSteps, DynStep.stepAccount, Account.zero,
          OracleAccessModel.instructionBitCost]
    rw [hstep, ih]
    simp [OracleAccessModel.realizedWordBitCost, List.map_cons, List.sum_cons,
      OracleAccessModel.instructionBitCost]

/-- The sums of forward- and backward-access indicators together equal the adjoint query count. -/
private theorem word_access_count : ∀ (word : List (AdjointStep I)),
    (word.map OracleAccessModel.forwardAccessCount).sum +
        (word.map OracleAccessModel.backwardAccessCount).sum = adjointQueryCount word := by
  intro word
  induction word with
  | nil => rfl
  | cons c cs ih =>
    cases c <;>
      simp [adjointQueryCount, OracleAccessModel.forwardAccessCount,
        OracleAccessModel.backwardAccessCount, ih] <;>
      omega

/-- The sum of gate-step indicators equals the adjoint gate count. -/
private theorem word_gate_count : ∀ (word : List (AdjointStep I)),
    (word.map OracleAccessModel.gateStepCount).sum = adjointGateCount word := by
  intro word
  induction word with
  | nil => rfl
  | cons c cs ih =>
    cases c <;>
      simp [adjointGateCount, OracleAccessModel.gateStepCount, ih]; omega

/-- The signal-word ledger counts total forward and adjoint queries as the word query count,
macro gates as the word gate count, and classical bits as the realized word bit cost. -/
theorem clause3_account_ledgers :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    (M.signalWordAccount O word).queries + (M.signalWordAccount O word).adjointQueries
        = adjointQueryCount word ∧
      (M.signalWordAccount O word).macroGates = adjointGateCount word ∧
      (M.signalWordAccount O word).classicalBits = M.realizedWordBitCost O word := by
  intro I _ _ M O word
  refine ⟨?_, ?_, ?_⟩
  · rw [OracleAccessModel.signalWordAccount, counters_queries (M.signalWordSteps O word),
      counters_adjoint_queries (M.signalWordSteps O word),
      word_forward_steps M O word, word_backward_steps M O word]
    exact word_access_count word
  · rw [OracleAccessModel.signalWordAccount, counters_macro_gates (M.signalWordSteps O word),
      word_gate_steps M O word]
    exact word_gate_count word
  · rw [OracleAccessModel.signalWordAccount, counters_classical_bits (M.signalWordSteps O word),
      word_bit_steps M O word]

/-- The realized signal-word circuit contains zero primitive circuit queries. -/
theorem clause3_signal_word_circuit_query_free :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    QueryCount (M.signalWordCircuit O word) = 0 := by
  intro I _ _ M O word
  induction word with
  | nil => rfl
  | cons c cs ih =>
    have hsplit : M.signalWordCircuit O (c :: cs) =
        M.signalWordCircuit O cs ++ M.stepCircuit O c := rfl
    rw [hsplit, queryCount_append]
    have hstep : QueryCount (M.stepCircuit O c) = 0 := by
      cases c with
      | gate V => rfl
      | forward => exact M.queryFree O false
      | backward => exact M.queryFree O true
    rw [hstep, ih]

/-- The realized signal-word circuit's gate count equals source gate count plus realized
oracle-access gate count. -/
theorem clause3_signal_word_circuit_gate_count :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    GateCount (M.signalWordCircuit O word) =
      adjointGateCount word + M.realizedWordGateCount O word := by
  intro I _ _ M O word
  induction word with
  | nil => simp [OracleAccessModel.signalWordCircuit, adjointGateCount,
    OracleAccessModel.realizedWordGateCount]
  | cons c cs ih =>
    have hsplit : M.signalWordCircuit O (c :: cs) =
        M.signalWordCircuit O cs ++ M.stepCircuit O c := rfl
    rw [hsplit, gateCount_append, ih]
    have hstep : GateCount (M.stepCircuit O c) =
        OracleAccessModel.instructionCircuitGateCost M O c := by
      cases c <;> rfl
    rw [hstep]
    cases c <;>
      simp only [adjointGateCount, OracleAccessModel.realizedWordGateCount,
        OracleAccessModel.instructionCircuitGateCost,
        List.map_cons, List.sum_cons] <;>
      ring

/-- Running the realized signal-word circuit with the identity oracle acts on every input as the
evaluated word matrix. -/
theorem clause3_signal_word_circuit_run :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)) (ψ : QState I),
    Run (1 : Matrix I I ℂ) (M.signalWordCircuit O word) ψ = evaluate O word *ᵥ ψ := by
  intro I _ _ M O word ψ
  induction word with
  | nil =>
    have h1 : evaluate O ([] : List (AdjointStep I)) = 1 := rfl
    simp [OracleAccessModel.signalWordCircuit, h1, Matrix.one_mulVec]
  | cons c cs ih =>
    have hsplit : M.signalWordCircuit O (c :: cs) =
        M.signalWordCircuit O cs ++ M.stepCircuit O c := rfl
    rw [hsplit, run_append]
    cases c with
    | gate V =>
      simp only [OracleAccessModel.stepCircuit]
      have hrun : Run (1 : Matrix I I ℂ) [Step.gate V]
            (Run (1 : Matrix I I ℂ) (M.signalWordCircuit O cs) ψ) =
          ApplyGate V (Run (1 : Matrix I I ℂ) (M.signalWordCircuit O cs) ψ) := rfl
      rw [hrun, ApplyGate, ih]
      have hE : evaluate O (AdjointStep.gate V :: cs) = V * evaluate O cs := rfl
      rw [hE, Matrix.mulVec_mulVec]
    | forward =>
      simp only [OracleAccessModel.stepCircuit]
      have hrun : Run (1 : Matrix I I ℂ) (M.realize O false)
            (Run (1 : Matrix I I ℂ) (M.signalWordCircuit O cs) ψ) =
          O *ᵥ (Run (1 : Matrix I I ℂ) (M.signalWordCircuit O cs) ψ) := M.forwardRun O _
      rw [hrun, ih]
      have hE : evaluate O (AdjointStep.forward :: cs) = O * evaluate O cs := rfl
      rw [hE, Matrix.mulVec_mulVec]
    | backward =>
      simp only [OracleAccessModel.stepCircuit]
      have hrun : Run (1 : Matrix I I ℂ) (M.realize O true)
            (Run (1 : Matrix I I ℂ) (M.signalWordCircuit O cs) ψ) =
          Oᴴ *ᵥ (Run (1 : Matrix I I ℂ) (M.signalWordCircuit O cs) ψ) := M.backwardRun O _
      rw [hrun, ih]
      have hE : evaluate O (AdjointStep.backward :: cs) = Oᴴ * evaluate O cs := rfl
      rw [hE, Matrix.mulVec_mulVec]

/-- If `k * g x ≤ f x` for every member of a list, then `k` times the sum of mapped `g` is at
most the sum of mapped `f`. -/
private theorem sum_map_ge_map_mul {α : Type} (l : List α) (f g : α → ℕ) (k : ℕ)
    (h : ∀ x ∈ l, k * g x ≤ f x) : k * (l.map g).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self)
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [Nat.mul_add]
    exact Nat.add_le_add ha hrest

/-- The sum of instruction-access indicators equals the adjoint word's query count. -/
private theorem word_access_sum : ∀ (word : List (AdjointStep I)),
    (word.map OracleAccessModel.instructionAccessCount).sum = adjointQueryCount word := by
  intro word
  induction word with
  | nil => rfl
  | cons c cs ih =>
    cases c <;>
      simp only [adjointQueryCount, List.map_cons, List.sum_cons,
        OracleAccessModel.instructionAccessCount, OracleAccessModel.forwardAccessCount,
        OracleAccessModel.backwardAccessCount] at * <;>
      omega

/-- The realized circuit gate count is at least minimum access gate cost times the word's query
count. -/
theorem clause3_gate_cost_lower_bound :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    (M.minAccessGateCost O : ℝ) * (adjointQueryCount word : ℝ) ≤
      (GateCount (M.signalWordCircuit O word) : ℝ) := by
  intro I _ _ M O word
  have hsum : M.realizedWordGateCount O word =
      (word.map (fun c => OracleAccessModel.instructionAccessCost M O c)).sum := by
    induction word with
    | nil => rfl
    | cons c cs ih =>
      cases c <;>
        simp [OracleAccessModel.realizedWordGateCount, OracleAccessModel.instructionAccessCost,
          List.map_cons, List.sum_cons]
  have hcount : (word.map (fun c => OracleAccessModel.instructionAccessCost M O c)).sum
      ≥ M.minAccessGateCost O * (adjointQueryCount word : ℕ) := by
    have hper : ∀ c ∈ word,
        M.minAccessGateCost O * OracleAccessModel.instructionAccessCount c
          ≤ OracleAccessModel.instructionAccessCost M O c := by
      intro c hc
      cases c with
      | gate V =>
        simp [OracleAccessModel.instructionAccessCost, OracleAccessModel.instructionAccessCount,
          OracleAccessModel.forwardAccessCount, OracleAccessModel.backwardAccessCount]
      | forward =>
        simp only [OracleAccessModel.instructionAccessCost, OracleAccessModel.instructionAccessCount,
          OracleAccessModel.forwardAccessCount, OracleAccessModel.backwardAccessCount,
          Nat.add_zero, Nat.mul_one, OracleAccessModel.minAccessGateCost]
        exact min_le_left _ _
      | backward =>
        simp only [OracleAccessModel.instructionAccessCost, OracleAccessModel.instructionAccessCount,
          OracleAccessModel.forwardAccessCount, OracleAccessModel.backwardAccessCount,
          Nat.zero_add, Nat.mul_one, OracleAccessModel.minAccessGateCost]
        exact min_le_right _ _
    have h := sum_map_ge_map_mul word
      (fun c => OracleAccessModel.instructionAccessCost M O c)
      (OracleAccessModel.instructionAccessCount) (M.minAccessGateCost O) hper
    rw [word_access_sum] at h
    exact h
  have hreal : (M.realizedWordGateCount O word : ℝ) ≥
      (M.minAccessGateCost O : ℝ) * (adjointQueryCount word : ℝ) := by
    rw [hsum]
    exact_mod_cast hcount
  have hcircuit : (GateCount (M.signalWordCircuit O word) : ℝ) =
      (adjointGateCount word : ℝ) + (M.realizedWordGateCount O word : ℝ) := by
    rw [clause3_signal_word_circuit_gate_count]
    push_cast
    ring
  rw [hcircuit]
  have hnn : 0 ≤ (adjointGateCount word : ℝ) := Nat.cast_nonneg _
  linarith

/-- The signal-word ledger's classical-bit charge is at least minimum access bit cost times the
word's query count. -/
theorem clause3_bit_cost_lower_bound :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    (M.minAccessBitCost O : ℝ) * (adjointQueryCount word : ℝ) ≤
      (M.signalWordAccount O word).classicalBits := by
  intro I _ _ M O word
  have hbits : (M.signalWordAccount O word).classicalBits = M.realizedWordBitCost O word :=
    (clause3_account_ledgers I M O word).2.2
  rw [hbits]
  have hsum : M.realizedWordBitCost O word =
      (word.map (fun c => OracleAccessModel.instructionBitCost M O c)).sum := by
    induction word with
    | nil => rfl
    | cons c cs ih =>
      cases c <;>
        simp [OracleAccessModel.realizedWordBitCost, OracleAccessModel.instructionBitCost,
          List.map_cons, List.sum_cons]
  have hcount : (word.map (fun c => OracleAccessModel.instructionBitCost M O c)).sum
      ≥ M.minAccessBitCost O * (adjointQueryCount word : ℕ) := by
    have hper : ∀ c ∈ word,
        M.minAccessBitCost O * OracleAccessModel.instructionAccessCount c
          ≤ OracleAccessModel.instructionBitCost M O c := by
      intro c hc
      cases c with
      | gate V =>
        simp [OracleAccessModel.instructionBitCost, OracleAccessModel.instructionAccessCount,
          OracleAccessModel.forwardAccessCount, OracleAccessModel.backwardAccessCount]
      | forward =>
        simp only [OracleAccessModel.instructionBitCost, OracleAccessModel.instructionAccessCount,
          OracleAccessModel.forwardAccessCount, OracleAccessModel.backwardAccessCount,
          Nat.add_zero, Nat.mul_one, OracleAccessModel.minAccessBitCost]
        exact min_le_left _ _
      | backward =>
        simp only [OracleAccessModel.instructionBitCost, OracleAccessModel.instructionAccessCount,
          OracleAccessModel.forwardAccessCount, OracleAccessModel.backwardAccessCount,
          Nat.zero_add, Nat.mul_one, OracleAccessModel.minAccessBitCost]
        exact min_le_right _ _
    have h := sum_map_ge_map_mul word
      (fun c => OracleAccessModel.instructionBitCost M O c)
      (OracleAccessModel.instructionAccessCount) (M.minAccessBitCost O) hper
    rw [word_access_sum] at h
    exact h
  rw [hsum]
  exact_mod_cast hcount

/-- The depth counter of a dynamic-step list equals the sum of its step depth counters. -/
private theorem counters_depth : ∀ (l : List DynStep),
    (counters l).depth = (l.map (fun s => s.stepAccount.depth)).sum := by
  intro l
  induction l with
  | nil => simp [counters, Account.zero]
  | cons s rest ih =>
    simp only [counters, Account.seq, List.map_cons, List.sum_cons, ih]

/-- The sum of depth charges in the realized signal steps equals twice the total access
indicator count plus the source gate-step count. -/
private theorem word_depth_steps [Fintype I] [DecidableEq I]
    (M : OracleAccessModel I) (O : Matrix I I ℂ) (word : List (AdjointStep I)) :
    ((M.signalWordSteps O word).map (fun s => s.stepAccount.depth)).sum =
      2 * (word.map OracleAccessModel.instructionAccessCount).sum +
        (word.map OracleAccessModel.gateStepCount).sum := by
  induction word with
  | nil => simp [OracleAccessModel.signalWordSteps]
  | cons c cs ih =>
    have hsteps : M.signalWordSteps O (c :: cs) =
        M.stepSteps O c ++ M.signalWordSteps O cs := rfl
    rw [hsteps, List.map_append, List.sum_append]
    have hstep : ((M.stepSteps O c).map (fun s => s.stepAccount.depth)).sum =
        2 * OracleAccessModel.instructionAccessCount c +
          OracleAccessModel.gateStepCount c := by
      cases c <;> rfl
    rw [hstep, ih]
    simp [List.map_cons, List.sum_cons, OracleAccessModel.instructionAccessCount,
      OracleAccessModel.gateStepCount]
    ring

/-- The signal-word account depth is at least the adjoint word's query count. -/
theorem clause3_bit_time_lower_bound :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    (adjointQueryCount word : ℕ) ≤ (M.signalWordAccount O word).depth := by
  intro I _ _ M O word
  rw [OracleAccessModel.signalWordAccount, counters_depth, word_depth_steps, word_access_sum]
  have h1 : 0 ≤ (word.map OracleAccessModel.gateStepCount).sum := Nat.cast_nonneg _
  omega

/-- Each dynamic step has zero live-peak and peak-workspace ledger fields. -/
private theorem stepAccount_peak_zero (s : DynStep) :
    s.stepAccount.livePeak = 0 ∧ s.stepAccount.peakWorkspace = 0 := by
  cases s with
  | oracle adj ws => cases adj <;> simp [DynStep.stepAccount, Account.zero]
  | «macro» g => simp [DynStep.stepAccount, Account.zero]
  | evolve t => simp [DynStep.stepAccount, Account.zero]
  | classical bits => simp [DynStep.stepAccount, Account.zero]
  | alloc w => simp [DynStep.stepAccount, Account.zero]
  | releaseClean w => simp [DynStep.stepAccount, Account.zero]
  | releaseDirty w => simp [DynStep.stepAccount, Account.zero]
  | reset w => simp [DynStep.stepAccount, Account.zero]
  | uncompute w => simp [DynStep.stepAccount, Account.zero]

/-- If every step in a list has zero live-peak charge, the combined counter has zero live-peak
charge. -/
private theorem counters_livePeak_zero : ∀ (l : List DynStep),
    (∀ s ∈ l, s.stepAccount.livePeak = 0) → (counters l).livePeak = 0 := by
  intro l
  induction l with
  | nil => simp [counters, Account.zero]
  | cons s rest ih =>
    intro h
    simp only [counters, Account.seq, List.map_cons]
    have hs := h s (List.mem_cons_self)
    have hr := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
    rw [hs, hr]
    simp [Account.zero]

/-- If every step in a list has zero peak-workspace charge, the combined counter has zero
peak-workspace charge. -/
private theorem counters_peakWorkspace_zero : ∀ (l : List DynStep),
    (∀ s ∈ l, s.stepAccount.peakWorkspace = 0) → (counters l).peakWorkspace = 0 := by
  intro l
  induction l with
  | nil => simp [counters, Account.zero]
  | cons s rest ih =>
    intro h
    simp only [counters, Account.seq, List.map_cons]
    have hs := h s (List.mem_cons_self)
    have hr := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
    rw [hs, hr]
    simp [Account.zero]

/-- The signal-word account has zero live-peak and peak-workspace fields. -/
theorem clause3_account_peak_ledgers :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)),
    (M.signalWordAccount O word).livePeak = 0 ∧
    (M.signalWordAccount O word).peakWorkspace = 0 := by
  intro I _ _ M O word
  refine ⟨counters_livePeak_zero _ (fun s _ => (stepAccount_peak_zero s).1),
    counters_peakWorkspace_zero _ (fun s _ => (stepAccount_peak_zero s).2)⟩

/-- A nonnegative lower bound on word queries forces minimum-access gate and bit charges, while
account depth bounds queries and both peak fields vanish. The realized circuit also acts
exactly as the evaluated word on every input. -/
theorem clause3_endpoint :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : OracleAccessModel I) (O : Matrix I I ℂ)
      (word : List (AdjointStep I)) (c : ℝ),
    0 ≤ c → c ≤ (adjointQueryCount word : ℝ) →
    (M.minAccessGateCost O : ℝ) * c ≤ (GateCount (M.signalWordCircuit O word) : ℝ) ∧
    (M.minAccessBitCost O : ℝ) * c ≤ (M.signalWordAccount O word).classicalBits ∧
    (adjointQueryCount word : ℕ) ≤ (M.signalWordAccount O word).depth ∧
    (M.signalWordAccount O word).livePeak = 0 ∧
    (M.signalWordAccount O word).peakWorkspace = 0 ∧
    (∀ ψ : QState I, Run (1 : Matrix I I ℂ) (M.signalWordCircuit O word) ψ =
      evaluate O word *ᵥ ψ) := by
  intro I _ _ M O word c hc hqc
  have hgate : (M.minAccessGateCost O : ℝ) * (adjointQueryCount word : ℝ) ≤
      (GateCount (M.signalWordCircuit O word) : ℝ) := clause3_gate_cost_lower_bound I M O word
  have hbit : (M.minAccessBitCost O : ℝ) * (adjointQueryCount word : ℝ) ≤
      (M.signalWordAccount O word).classicalBits := clause3_bit_cost_lower_bound I M O word
  have htime : (adjointQueryCount word : ℕ) ≤
      (M.signalWordAccount O word).depth := clause3_bit_time_lower_bound I M O word
  have hng : 0 ≤ (M.minAccessGateCost O : ℝ) := Nat.cast_nonneg _
  have hnb : 0 ≤ (M.minAccessBitCost O : ℝ) := Nat.cast_nonneg _
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left hqc hng) hgate
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left hqc hnb) hbit
  constructor
  · exact htime
  constructor
  · exact (clause3_account_peak_ledgers I M O word).1
  constructor
  · exact (clause3_account_peak_ledgers I M O word).2
  · intro ψ
    exact clause3_signal_word_circuit_run I M O word ψ

/-- Collect scalar adaptive pathwise, worst-case, and expected query bounds under the
approximation hypotheses, together with remaining-budget and mass-transport identities, the
variable-query example, and the differing-word counterexample. -/
theorem clause1_endpoint :
    (∀ (W : Type) [Fintype W] [DecidableEq W] (tree : AdaptiveSignalTree (Bool × W))
      (L R : Matrix (Bool × W) Unit ℂ) (x y a b eps : ℝ),
    IsIsometry L → IsIsometry R → tree.WellFormed →
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x ≠ y → 0 ≤ eps →
    (∀ p : List Bool,
      ‖(a : ℂ) • (1 : Matrix Unit Unit ℂ) -
        compress L (evaluate (scalarSignalLift W x) (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p : List Bool,
      ‖(b : ℂ) • (1 : Matrix Unit Unit ℂ) -
        compress L (evaluate (scalarSignalLift W y) (tree.pathWord p)) R‖ ≤ eps) →
    (∀ p : List Bool, (tree.pathQueries p : ℝ) ≥
        max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y) ∧
    (tree.worstCaseQueries : ℝ) ≥ max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y ∧
    (∀ law : SignalBranchLaw, law.expectedQueries tree ≥
        max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y)) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (tree : AdaptiveSignalTree (Bool × W))
      (p : List Bool),
    p ∈ tree.paths →
    tree.pathQueries p + tree.remainingQueries p = tree.worstCaseQueries) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (tree : AdaptiveSignalTree (Bool × W))
      (S : List (List Bool)) (law : SignalBranchLaw) (c : ℝ),
    0 ≤ c → (∀ p ∈ S, (tree.pathQueries p : ℝ) ≥ c) →
    law.expectedQueries tree ≥ c * law.mass S) ∧
    (clause1_variableQueryTree.pathQueries [false, false] = 1 ∧
      clause1_variableQueryTree.pathQueries [true, false] = 2 ∧
      clause1_variableQueryTree.worstCaseQueries = 2 ∧
      clause1_variableQueryLaw.expectedQueries clause1_variableQueryTree = 3 / 2 ∧
      (clause1_variableQueryLaw.expectedQueries clause1_variableQueryTree : ℝ) <
        (clause1_variableQueryTree.worstCaseQueries : ℝ)) ∧
    (∃ (wₓ w_y : List (AdjointStep (Bool × Unit))) (x y : ℝ),
      wₓ ≠ w_y ∧
      |fiberResponse x wₓ - fiberResponse y w_y| >
        (adjointQueryCount wₓ : ℝ) * scalarSignalDistance x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro W _ _ tree L R x y a b eps hL hR hWF hx hy hxy heps ha hb
    have hworst := clause1_adaptive_worst_case_and_expected_lower_bound W tree L R x y a b eps
      hL hR hWF hx hy hxy heps ha hb
    exact ⟨clause1_adaptive_pathwise_response_lower_bound W tree L R x y a b eps hL hR hWF hx hy hxy
      heps ha hb, hworst.1, hworst.2⟩
  · exact clause1_remaining_budget
  · exact clause1_structural_tail_transport
  · exact clause1_adaptive_vs_fixed_gap
  · exact clause1_oracle_dependent_branch_counterexample

/-- Collect scalar-target response bounds, the lifted scalar-signal distance identity, and
hybrid estimates for controlled access and fixed adaptive paths under their stated
hypotheses. -/
theorem clause2_endpoint :
    (∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix H I ℂ) (O₁ O₂ : Matrix H H ℂ)
      (word : List (AdjointStep H)) (a b eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    (∀ c ∈ word, ‖instructionMatrix O₁ c‖ ≤ 1 ∧ ‖instructionMatrix O₂ c‖ ≤ 1) →
    0 ≤ eps →
    ‖(a : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate O₁ word) R‖ ≤ eps →
    ‖(b : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate O₂ word) R‖ ≤ eps →
    max 0 (|a - b| - 2 * eps) ≤ (adjointQueryCount word : ℝ) * ‖O₁ - O₂‖) ∧
    (∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Nonempty I]
      (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
      (x y a b eps : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x ≠ y → 0 ≤ eps →
    ‖(a : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
    ‖(b : ℂ) • (1 : Matrix I I ℂ) - compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
    (adjointQueryCount word : ℝ) ≥ max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (x y : ℝ),
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 →
    ‖scalarSignalLift W x - scalarSignalLift W y‖ = scalarSignalDistance x y) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (O₁ O₂ : Matrix I I ℂ)
      (word : List (AdjointStep (Bool × I))),
    O₁ ∈ Matrix.unitaryGroup I ℂ → O₂ ∈ Matrix.unitaryGroup I ℂ →
    WellFormedAdjointCircuit word →
    (∀ c ∈ word, ‖instructionMatrix (controlOracle O₁) c‖ ≤ 1 ∧
        ‖instructionMatrix (controlOracle O₂) c‖ ≤ 1) →
    ‖evaluate (controlOracle O₁) word - evaluate (controlOracle O₂) word‖ ≤
      (adjointQueryCount word : ℝ) * ‖controlOracle O₁ - controlOracle O₂‖) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (O₁ O₂ : Matrix I I ℂ)
      (tree : AdaptiveSignalTree I) (p : List Bool),
    tree.WellFormed →
    (∀ c ∈ tree.pathWord p, ‖instructionMatrix O₁ c‖ ≤ 1 ∧
        ‖instructionMatrix O₂ c‖ ≤ 1) →
    ‖evaluate O₁ (tree.pathWord p) - evaluate O₂ (tree.pathWord p)‖ ≤
      (tree.pathQueries p : ℝ) * ‖O₁ - O₂‖) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact clause2_general_response_lower_bound
  · exact clause2_general_bound_implies_scalar_bound
  · exact clause2_scalar_family_isometric_embedding
  · exact clause2_controlled_access_covered
  · exact clause2_measurement_feedback_covered

end Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound
