/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
public import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma5NormBoundQuan
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

@[expose] public section

/-!
# Explicit Gram blocks and contraction for Szegedy's generalized discriminant

This module specializes the generalized two-frame discriminant to nonempty finite index sets.
It expands its four Gram blocks explicitly and records a dimension-independent bound in the
matrix `L2Operator` norm. The uniform constant is chosen before all frame quantifiers, so the
statement cannot hide a dimension-dependent constant.

## Main statements

* `source_definition_five_explicit_gram_L2_contraction`: the generalized discriminant has zero
  diagonal blocks, the two expected cross-Gram blocks, and operator norm at most one.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ReferenceError.RefTraceError

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

/-- For nonempty finite orthonormal systems, the generalized Szegedy discriminant is exactly
the off-diagonal cross-Gram block matrix and is a contraction in the Euclidean operator norm.
The constant `1` is uniform in the ambient and source dimensions. See
[Szegedy, Definition 5 and Lemma 5][Szegedy2004]. -/
theorem source_definition_five_explicit_gram_L2_contraction :
    ∃ C : ℝ, C = 1 ∧ 0 < C ∧
      ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        [Fintype J] [DecidableEq J] [Nonempty I] [Nonempty J]
        (A : Matrix H I ℂ) (B : Matrix H J ℂ),
        IsIsometry A → IsIsometry B →
        (∀ i j : I,
          bipartiteDiscriminant A B (Sum.inl i) (Sum.inl j) = 0) ∧
        (∀ i j : J,
          bipartiteDiscriminant A B (Sum.inr i) (Sum.inr j) = 0) ∧
        (∀ i : I, ∀ j : J,
          bipartiteDiscriminant A B (Sum.inl i) (Sum.inr j) = (Aᴴ * B) i j) ∧
        (∀ i : J, ∀ j : I,
          bipartiteDiscriminant A B (Sum.inr i) (Sum.inl j) = (Bᴴ * A) i j) ∧
        ‖bipartiteDiscriminant A B‖ ≤ C := by
  refine ⟨1, rfl, one_pos, fun H I J _ _ _ _ _ _ _ _ A B hA hB => ?_⟩
  have hsquare := (szegedyLemma5NormBound H I J A B hA hB).1
  have hvector : ∀ x : QState (I ⊕ J),
      ‖toEuclidean_fromVec (bipartiteDiscriminant A B *ᵥ x)‖ ≤
        ‖toEuclidean_fromVec x‖ := by
    intro x
    have hsq := hsquare x
    rw [← norm_toEuclidean_fromVec_sq (bipartiteDiscriminant A B *ᵥ x),
      ← norm_toEuclidean_fromVec_sq x] at hsq
    calc
      ‖toEuclidean_fromVec (bipartiteDiscriminant A B *ᵥ x)‖
          = Real.sqrt (‖toEuclidean_fromVec (bipartiteDiscriminant A B *ᵥ x)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖toEuclidean_fromVec x‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖toEuclidean_fromVec x‖ := Real.sqrt_sq (norm_nonneg _)
  have hnorm : ‖bipartiteDiscriminant A B‖ ≤ 1 :=
    l2_opNorm_le_of_mulVec_le zero_le_one _ fun x => by
      rw [one_mul]
      exact hvector x
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, hnorm⟩

end Qatlib.Papers.QWalkSpectra04.WalkDefinition
