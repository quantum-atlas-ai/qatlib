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
# Matrix-element sampling bounds for finite-group applications

This module applies the common Hadamard-test estimates to the matrix-element setting discussed
in [Jordan2008a]. It bounds a diagonal matrix element of a norm-preserving operator and gives
real-part and imaginary-part deviation bounds, with the imaginary part supplied by an explicit
auxiliary real-part identity.

## Main statements

* `finite_group_matrix_element_estimate`: the real-part sampling bound.
* `finite_group_matrix_element_estimate_im`: the bound under an auxiliary imaginary-part
  identity.

## References

* [Jordan, 2008][Jordan2008a]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.GroupReps08.MainResults.Common

namespace Qatlib.Papers.GroupReps08.MainResults.GroupQFTMatrixElement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For normalized `ψ` and norm-preserving `U`, the complex norm of `⟪ψ, U ψ⟫` is at most one
[Jordan2008a]. -/
theorem matrix_element_abs_le_one (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : ‖⟪ψ, U ψ⟫_ℂ‖ ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) ψ (U ψ)
  rw [hψ, hU ψ, hψ] at h
  simpa using h

/-- For normalized `ψ` and norm-preserving `U`, `L > 0` Hadamard samples estimate the real
matrix element with deviation probability at most `1 / (L * ε^2)` for positive `ε`
[Jordan2008a]. -/
theorem finite_group_matrix_element_estimate (U : E →L[ℂ] E) (ψ : E)
    (hψ : ‖ψ‖ = 1) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := L) (hadamardLaw U ψ hψ hU)
        (fun ω => ε < |FinDist.avg readout ω - (⟪ψ, U ψ⟫_ℂ).re|)
      ≤ 1 / (L * ε ^ 2) :=
  hadamard_sample_bound U ψ hψ hU L hL ε hε

/-- If an auxiliary normalized Hadamard test has real matrix element equal to the desired
imaginary part, its sample mean estimates that part with deviation probability at most `1 /
(L * ε^2)` for positive `L` and `ε` [Jordan2008a]. -/
theorem finite_group_matrix_element_estimate_im (U : E →L[ℂ] E) (ψ : E)
    (U' : E →L[ℂ] E) (ψ' : E)
    (hψ' : ‖ψ'‖ = 1) (hU' : ∀ x, ‖U' x‖ = ‖x‖)
    (himag : (⟪ψ', U' ψ'⟫_ℂ).re = (⟪ψ, U ψ⟫_ℂ).im)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := L) (hadamardLaw U' ψ' hψ' hU')
        (fun ω => ε < |FinDist.avg readout ω - (⟪ψ, U ψ⟫_ℂ).im|)
      ≤ 1 / (L * ε ^ 2) := by
  have h := hadamard_sample_bound U' ψ' hψ' hU' L hL ε hε
  rwa [himag] at h

end Qatlib.Papers.GroupReps08.MainResults.GroupQFTMatrixElement
