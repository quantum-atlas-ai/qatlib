/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanProgSt12.MainResults.SourceModel

@[expose] public section


/-! The legacy universal-in-n contracts include n = 0, whose addressed register
is empty and cannot carry a normalized state. This diagnoses the formal interface,
not the asymptotic algorithms of arXiv:1203.2603v1. -/

set_option autoImplicit false

namespace Qatlib.Papers.SpanProgSt12.MainResults

open Qatlib.Papers.SpanProgSt12.MainResults.SourceModel
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath

/-- The zero-vertex addressed register cannot support any query algorithm. -/
theorem noEmptyAlgorithm (F : Type) (toGraph : F → SimpleGraph (Fin 0))
    (Ω : F → Prop) (ε : ℝ) (k : ℕ) :
    ¬ GraphQuerySolvable F toGraph Ω ε k := by
  rintro ⟨_, _, C, ψ, _, hψ, _, _⟩
  have hz : (∑ i : EdgeReg 0, ‖ψ i‖ ^ 2) = 0 := by simp [EdgeReg]
  have hone : (∑ i : EdgeReg 0, ‖ψ i‖ ^ 2) = 1 := hψ
  linarith

/-- In particular, the literal all-n triangle contract is false at n = 0. -/
theorem noUniversalTriangle :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      GraphQuerySolvable (TriangleNotMinorInstance n) (fun G => G.1)
        (fun G => ContainsTriangle G.1) (1 / 3) ⌈c * (n : ℝ)⌉₊ := by
  rintro ⟨c, _, h⟩
  exact noEmptyAlgorithm _ _ _ _ _ (h 0)

/-- Adding workspace to an empty addressed register still leaves no normalized state. -/
theorem noEmptyTimed (F : Type) (toGraph : F → SimpleGraph (Fin 0))
    (Ω : F → Prop) (ε space time : ℝ) (k : ℕ) :
    ¬ TimedSpaceGraphAlgorithm F toGraph Ω ε space time k := by
  rintro ⟨_, _, W, hW, hD, _, C, ψ, _, hψ, _, _, _⟩
  let := hW
  let := hD
  have hz : (∑ i : EdgeReg 0 × W, ‖ψ i‖ ^ 2) = 0 := by simp [EdgeReg]
  have hone : (∑ i : EdgeReg 0 × W, ‖ψ i‖ ^ 2) = 1 := hψ
  linarith

end Qatlib.Papers.SpanProgSt12.MainResults
