/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Qatlib.Papers.GroupReps08.MainResults.Common

/-!
# Matrix-element estimates for Schur-transform applications

This module supplies the generic matrix-element and Hadamard sampling bounds used in the
Schur-transform discussion of [Jordan2008a]. Under normalization and norm preservation, the
matrix element has norm at most one and the readout sample mean satisfies a variance-based
deviation bound.

## Main statements

* `schur_matrix_element_abs_le_one`: a unit bound on the matrix element.
* `schur_transform_matrix_element_estimate`: the real-part sampling estimate.

## References

* [Jordan, 2008][Jordan2008a]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.GroupReps08.MainResults.Common

namespace Qatlib.Papers.GroupReps08.MainResults.SchurTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For normalized `ψ` and norm-preserving `U`, the complex norm of `⟪ψ, U ψ⟫` is at most one
[Jordan2008a]. -/
theorem schur_matrix_element_abs_le_one (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : ‖⟪ψ, U ψ⟫_ℂ‖ ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) ψ (U ψ)
  rw [hψ, hU ψ, hψ] at h
  simpa using h

/-- For normalized `ψ` and norm-preserving `U`, `L > 0` Hadamard samples estimate the real
matrix element with deviation probability at most `1 / (L * ε^2)` for positive `ε`
[Jordan2008a]. -/
theorem schur_transform_matrix_element_estimate (U : E →L[ℂ] E) (ψ : E)
    (hψ : ‖ψ‖ = 1) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := L) (hadamardLaw U ψ hψ hU)
        (fun ω => ε < |FinDist.avg readout ω - (⟪ψ, U ψ⟫_ℂ).re|)
      ≤ 1 / (L * ε ^ 2) :=
  hadamard_sample_bound U ψ hψ hU L hL ε hε

end Qatlib.Papers.GroupReps08.MainResults.SchurTransform
