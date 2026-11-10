/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.CircuitModel.Source
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QAOASupremacy16.GapModels

open Qatlib.Foundations.PureStateMath

abbrev Language := (n : ℕ) → Reg n → Bool

structure ClassicalGapData (L : Language) (a b : ℝ) where

  prob : (n : ℕ) → Reg n → ℝ

  prob_nonneg : ∀ n x, 0 ≤ prob n x

  completeness : ∀ n x, L n x = true → a ≤ prob n x

  soundness : ∀ n x, L n x = false → prob n x ≤ b

def HasClassicalGap (L : Language) : Prop :=
  ∃ a b : ℝ, b < a ∧ Nonempty (ClassicalGapData L a b)

structure QuantumGapData (L : Language) (a b : ℝ) where

  prob : (n : ℕ) → Reg n → ℝ

  prob_nonneg : ∀ n x, 0 ≤ prob n x

  completeness : ∀ n x, L n x = true → a ≤ prob n x

  soundness : ∀ n x, L n x = false → prob n x ≤ b

def HasQuantumGap (L : Language) : Prop :=
  ∃ a b : ℝ, b < a ∧ Nonempty (QuantumGapData L a b)

theorem HasQuantumGap.congr {L L' : Language} (h : ∀ n x, L n x = L' n x)
    (hL : HasQuantumGap L) : HasQuantumGap L' := by
  obtain ⟨a, b, hlt, proc⟩ := hL
  refine ⟨a, b, hlt, ?_⟩
  obtain ⟨P⟩ := proc
  refine ⟨⟨P.prob, P.prob_nonneg, ?_, ?_⟩⟩
  · intro n x hx
    exact P.completeness n x (by rw [h n x]; exact hx)
  · intro n x hx
    exact P.soundness n x (by rw [h n x]; exact hx)

theorem HasClassicalGap.congr {L L' : Language} (h : ∀ n x, L n x = L' n x)
    (hL : HasClassicalGap L) : HasClassicalGap L' := by
  obtain ⟨a, b, hlt, proc⟩ := hL
  refine ⟨a, b, hlt, ?_⟩
  obtain ⟨P⟩ := proc
  refine ⟨⟨P.prob, P.prob_nonneg, ?_, ?_⟩⟩
  · intro n x hx
    exact P.completeness n x (by rw [h n x]; exact hx)
  · intro n x hx
    exact P.soundness n x (by rw [h n x]; exact hx)

abbrev LanguageHierarchy := ℕ → Set Language

def HierarchyStabilizes (PH : LanguageHierarchy) (k : ℕ) : Prop :=
  ∀ j, k ≤ j → PH j = PH k

structure ConditionalCollapseData (PH : LanguageHierarchy) where

  classicalGap_in_level3 : ∀ L, HasClassicalGap L → L ∈ PH 3

  stabilizes_of_gap_transport :
    (∀ L, HasQuantumGap L → HasClassicalGap L) → HierarchyStabilizes PH 3

theorem level3_of_classicalGap {PH : LanguageHierarchy}
    (facts : ConditionalCollapseData PH) {L : Language} (h : HasClassicalGap L) :
    L ∈ PH 3 :=
  facts.classicalGap_in_level3 L h

end Qatlib.Papers.QAOASupremacy16.GapModels
