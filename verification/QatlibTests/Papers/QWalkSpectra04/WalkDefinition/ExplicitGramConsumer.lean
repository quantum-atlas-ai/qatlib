module

public import Qatlib.Papers.QWalkSpectra04.WalkDefinition.ExplicitGram

/-!
# Concrete consumer for the generalized discriminant Gram blocks

The one-dimensional identity frames are nondegenerate isometries. This module checks the four
entries of their discriminant and the operator norm bound supplied by the general theorem.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Papers.QWalkSpectra04.WalkDefinition

open scoped Matrix.Norms.L2Operator

namespace QatlibTests.Papers.QWalkSpectra04.WalkDefinition

/-- The identity frames give a discriminant with zero diagonal entries, unit off-diagonal
entries, and Euclidean operator norm at most one. -/
theorem explicitGram_fin_one_invoked :
    let D := bipartiteDiscriminant (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (1 : Matrix (Fin 1) (Fin 1) ℂ)
    D (Sum.inl 0) (Sum.inl 0) = 0 ∧
    D (Sum.inr 0) (Sum.inr 0) = 0 ∧
    D (Sum.inl 0) (Sum.inr 0) = 1 ∧
    D (Sum.inr 0) (Sum.inl 0) = 1 ∧
    ‖D‖ ≤ 1 := by
  obtain ⟨C, hC, _, hgeneral⟩ :=
    source_definition_five_explicit_gram_L2_contraction
  obtain ⟨hLeft, hRight, hCross, hCrossAdjoint, hNorm⟩ := hgeneral (Fin 1) (Fin 1) (Fin 1)
    (1 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (by simp [IsIsometry]) (by simp [IsIsometry])
  exact ⟨hLeft 0 0, hRight 0 0, by simpa using hCross 0 0,
    by simpa using hCrossAdjoint 0 0, hC ▸ hNorm⟩

end QatlibTests.Papers.QWalkSpectra04.WalkDefinition
