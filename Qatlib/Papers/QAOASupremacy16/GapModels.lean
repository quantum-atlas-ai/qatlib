/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.CircuitModel.Source

/-!
# Abstract acceptance gaps and conditional hierarchy data

`ClassicalGapData` and `QuantumGapData` package nonnegative acceptance weights with completeness
and soundness bounds for Boolean languages. The module defines their existential gap predicates
and abstract language hierarchies, together with explicitly supplied implications for
level-three containment and stabilization.

This development accompanies the study of QAOA sampling and postselection in [FarhiHarrow2016].

## Main statements

* `HierarchyStabilizes`: The assertion that every hierarchy level at or above `k` equals level
  `k`.
* `level3_of_classicalGap`: The supplied containment implication places a language with an
  abstract classical gap in level three.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAOASupremacy16.GapModels

open Qatlib.Foundations.PureStateMath

/-- A family of Boolean predicates on finite bit registers, indexed by register length. -/
abbrev Language := (n : ℕ) → Reg n → Bool

/-- A nonnegative real acceptance-weight family with lower bound `a` on yes inputs and upper
bound `b` on no inputs. -/
structure ClassicalGapData (L : Language) (a b : ℝ) where

  prob : (n : ℕ) → Reg n → ℝ

  prob_nonneg : ∀ n x, 0 ≤ prob n x

  completeness : ∀ n x, L n x = true → a ≤ prob n x

  soundness : ∀ n x, L n x = false → prob n x ≤ b

/-- The existence of classical acceptance-weight data with separated bounds `b < a`. -/
def HasClassicalGap (L : Language) : Prop :=
  ∃ a b : ℝ, b < a ∧ Nonempty (ClassicalGapData L a b)

/-- A nonnegative real acceptance-weight family labeled quantum, with lower bound `a` on yes
inputs and upper bound `b` on no inputs. -/
structure QuantumGapData (L : Language) (a b : ℝ) where

  prob : (n : ℕ) → Reg n → ℝ

  prob_nonneg : ∀ n x, 0 ≤ prob n x

  completeness : ∀ n x, L n x = true → a ≤ prob n x

  soundness : ∀ n x, L n x = false → prob n x ≤ b

/-- The existence of quantum acceptance-weight data with separated bounds `b < a`. -/
def HasQuantumGap (L : Language) : Prop :=
  ∃ a b : ℝ, b < a ∧ Nonempty (QuantumGapData L a b)

/-- Pointwise equal languages share the abstract quantum-gap property. -/
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

/-- Pointwise equal languages share the abstract classical-gap property. -/
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

/-- A natural-indexed family of sets of Boolean languages. -/
abbrev LanguageHierarchy := ℕ → Set Language

/-- The assertion that every hierarchy level at or above `k` equals level `k`. -/
def HierarchyStabilizes (PH : LanguageHierarchy) (k : ℕ) : Prop :=
  ∀ j, k ≤ j → PH j = PH k

/-- Supplied implications placing classical-gap languages in level three and deriving
level-three stabilization from transport of quantum gaps to classical gaps. -/
structure ConditionalCollapseData (PH : LanguageHierarchy) where

  classicalGap_in_level3 : ∀ L, HasClassicalGap L → L ∈ PH 3

  stabilizes_of_gap_transport :
    (∀ L, HasQuantumGap L → HasClassicalGap L) → HierarchyStabilizes PH 3

/-- The supplied containment implication places a language with an abstract classical gap in
level three. -/
theorem level3_of_classicalGap {PH : LanguageHierarchy}
    (facts : ConditionalCollapseData PH) {L : Language} (h : HasClassicalGap L) :
    L ∈ PH 3 :=
  facts.classicalGap_in_level3 L h

end Qatlib.Papers.QAOASupremacy16.GapModels
