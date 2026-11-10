/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions
import Qatlib.Papers.PottsTutte07.MainResults.Scales
import Qatlib.Papers.PottsTutte07.MainResults.ComplexityDefs
import Qatlib.Papers.PottsTutte07.MainResults.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators
open Finset

theorem lemma8_1_unitary_seeding
    (q : ℂ) (Wodd Weven : Set ℂ) (_h : IsUnitaryType q Wodd Weven)
    (σ1 σ2 : Matrix (Fin 2) (Fin 2) ℂ)
    (_hdet1 : Matrix.det σ1 = 1) (_hdet2 : Matrix.det σ2 = 1)
    (_hcomm : σ1 * σ2 ≠ σ2 * σ1)
    (hdense : DenseIn (SpecialUnitarySet 2)
      (generatedBy ({σ1, σ2} : Set (Matrix (Fin 2) (Fin 2) ℂ)))) :
    ∀ U ∈ SpecialUnitarySet 2, ∀ ε : ℝ, 0 < ε →
      ∃ word : List (Matrix (Fin 2) (Fin 2) ℂ),
        (∀ M ∈ word, M = σ1 ∨ M = σ2) ∧ entryDist (wordEval word) U < ε := by
  intro U hU ε hε
  obtain ⟨word, hword, hd⟩ := dense_word_approx (n := Fin 2) (K := 2) _ _ hdense U hU ε hε
  exact ⟨word, fun M hM => by
    have := hword M hM
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this, hd⟩

theorem lemma9_1_nonunitary_seeding
    (q : ℂ) (Wodd Weven : Set ℂ)
    (_h : IsComplexNonUnitaryType q Wodd Weven ∨ IsRealNonUnitaryType q Wodd Weven)
    (σ1 σ2 : Matrix (Fin 2) (Fin 2) ℂ)
    (_hdet1 : Matrix.det σ1 = 1) (_hdet2 : Matrix.det σ2 = 1)
    (_hcomm : σ1 * σ2 ≠ σ2 * σ1)
    (hdense :
      DenseIn (SpecialLinearSet 2)
          (generatedBy ({σ1, σ2} : Set (Matrix (Fin 2) (Fin 2) ℂ))) ∨
      DenseIn (SpecialLinearRealSet 2)
          (generatedBy ({σ1, σ2} : Set (Matrix (Fin 2) (Fin 2) ℂ)))) :
    (∀ U ∈ SpecialLinearSet 2, ∀ ε : ℝ, 0 < ε →
        ∃ word : List (Matrix (Fin 2) (Fin 2) ℂ),
          (∀ M ∈ word, M = σ1 ∨ M = σ2) ∧ entryDist (wordEval word) U < ε) ∨
    (∀ U ∈ SpecialLinearRealSet 2, ∀ ε : ℝ, 0 < ε →
        ∃ word : List (Matrix (Fin 2) (Fin 2) ℂ),
          (∀ M ∈ word, M = σ1 ∨ M = σ2) ∧ entryDist (wordEval word) U < ε) := by
  rcases hdense with h | h
  · left
    intro U hU ε hε
    obtain ⟨word, hword, hd⟩ := dense_word_approx (n := Fin 2) (K := 2) _ _ h U hU ε hε
    exact ⟨word, fun M hM => by
      have := hword M hM
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this, hd⟩
  · right
    intro U hU ε hε
    obtain ⟨word, hword, hd⟩ := dense_word_approx (n := Fin 2) (K := 2) _ _ h U hU ε hε
    exact ⟨word, fun M hM => by
      have := hword M hM
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this, hd⟩

theorem corollary9_1_jorgensen_sullivan
    (X Y : Matrix (Fin 2) (Fin 2) ℂ)
    (_hX : Matrix.det X = 1) (_hY : Matrix.det Y = 1)
    (_hcomm : X * Y ≠ Y * X)
    (_hrem : ‖Matrix.trace (X * Y - Y * X)‖ < 1)
    (hdense :
      DenseIn (SpecialLinearSet 2)
          (generatedBy ({X, Y} : Set (Matrix (Fin 2) (Fin 2) ℂ))) ∨
      ∃ (g ginv : Matrix (Fin 2) (Fin 2) ℂ), g * ginv = 1 ∧
        DenseIn (SpecialLinearRealSet 2)
          (generatedBy
            ((fun A => g * A * ginv) '' ({X, Y} : Set (Matrix (Fin 2) (Fin 2) ℂ))))) :
    (∀ U ∈ SpecialLinearSet 2, ∀ ε : ℝ, 0 < ε →
        ∃ word : List (Matrix (Fin 2) (Fin 2) ℂ),
          (∀ M ∈ word, M = X ∨ M = Y) ∧ entryDist (wordEval word) U < ε) ∨
    (∃ (g ginv : Matrix (Fin 2) (Fin 2) ℂ), g * ginv = 1 ∧
      ∀ U ∈ SpecialLinearRealSet 2, ∀ ε : ℝ, 0 < ε →
        ∃ word : List (Matrix (Fin 2) (Fin 2) ℂ),
          (∀ M ∈ word,
            ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A ∈ ({X, Y} : Set _) ∧ M = g * A * ginv) ∧
          entryDist (wordEval word) U < ε) := by
  rcases hdense with h | ⟨g, ginv, hg, h⟩
  · left
    intro U hU ε hε
    obtain ⟨word, hword, hd⟩ := dense_word_approx (n := Fin 2) (K := 2) _ _ h U hU ε hε
    exact ⟨word, fun M hM => by
      have := hword M hM
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this, hd⟩
  · refine Or.inr ⟨g, ginv, hg, ?_⟩
    intro U hU ε hε
    obtain ⟨word, hword, hd⟩ := dense_word_approx (n := Fin 2) (K := 2) _ _ h U hU ε hε
    refine ⟨word, ?_, hd⟩
    intro M hM
    have hmem := hword M hM
    rw [Set.mem_image] at hmem
    obtain ⟨A, hA, hMA⟩ := hmem
    exact ⟨A, hA, hMA.symm⟩

theorem trace_conj_eq {n : Type*} [Fintype n] [DecidableEq n]
    (g ginv f : Matrix n n ℂ) (_hg : g * ginv = 1) (hgl : ginv * g = 1) :
    Matrix.trace (g * f * ginv) = Matrix.trace f := by
  rw [Matrix.trace_mul_comm (g * f) ginv, ← Matrix.mul_assoc ginv g f, hgl, Matrix.one_mul]

theorem lemma9_2_normal_sl2r_trace
    (g ginv : Matrix (Fin 2) (Fin 2) ℂ) (hg : g * ginv = 1) (hgl : ginv * g = 1)
    (f : Matrix (Fin 2) (Fin 2) ℂ)
    (hreal : ∀ i j, ((g * f * ginv) i j).im = 0) :
    (Matrix.trace f).im = 0 ∨ (Matrix.trace f).re = 0 := by
  left
  rw [← trace_conj_eq g ginv f hg hgl]
  simp [Matrix.trace, hreal]

theorem lemma9_3_nonunitary_bridge
    (n : ℕ) (SA SB : Set (Matrix (Fin n) (Fin n) ℂ)) (W : Matrix (Fin n) (Fin n) ℂ)
    (S : Submonoid (Matrix (Fin n) (Fin n) ℂ))
    (hSA : SA ⊆ S) (hSB : SB ⊆ S) (hW : W ∈ S) :
    generatedBy (SA ∪ SB ∪ ({W} : Set (Matrix (Fin n) (Fin n) ℂ))) ⊆ S := by
  intro L hL
  have hle : (SA ∪ SB ∪ ({W} : Set (Matrix (Fin n) (Fin n) ℂ))) ⊆ S := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact hSA hx
      · exact hSB hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hW
  exact Submonoid.closure_le.mpr hle hL

def blockDiag {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
  Matrix.fromBlocks A 0 0 B

theorem entryDist_blockDiag {m n : ℕ}
    (A C : Matrix (Fin m) (Fin m) ℂ) (B D : Matrix (Fin n) (Fin n) ℂ) :
    entryDist (blockDiag A B) (blockDiag C D) = entryDist A C + entryDist B D := by
  simp [entryDist, blockDiag, Fintype.sum_sum_type]

theorem lemma9_4_nonunitary_decoupling
    (G : Type*) [Group G]
    (dimA dimB : ℕ) [NeZero dimA] [NeZero dimB] (_hne : dimA ≠ dimB)
    (ρA : G → Matrix (Fin dimA) (Fin dimA) ℂ)
    (ρB : G → Matrix (Fin dimB) (Fin dimB) ℂ)
    (VA : Matrix (Fin dimA) (Fin dimA) ℂ) (VB : Matrix (Fin dimB) (Fin dimB) ℂ)
    (_hdA : VA ∈ SpecialLinearSet dimA) (_hdB : VB ∈ SpecialLinearSet dimB)
    (hcompat : ∀ ε : ℝ, 0 < ε →
      ∃ g : G, entryDist (ρA g) VA < ε ∧ entryDist (ρB g) VB < ε) :
    (∃ g : G, entryDist (ρA g) VA < 1 ∧ entryDist (ρB g) VB < 1) ∧
    (∃ g : G,
      entryDist (blockDiag (ρA g) (ρB g)) (blockDiag VA VB) < 1) := by
  constructor
  · exact hcompat 1 one_pos
  · obtain ⟨g, h1, h2⟩ := hcompat (1 / 2) (by norm_num)
    refine ⟨g, ?_⟩
    rw [entryDist_blockDiag]
    linarith

end Qatlib.Papers.PottsTutte07.MainResults
