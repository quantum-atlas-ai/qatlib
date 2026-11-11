/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Qatlib.Papers.GroupReps08.MainResults.Common

/-!
# Linear expansions and highest-weight matrix-element estimates

This module records the linear expansion of a four-term operator expression and the generic
Hadamard-test estimates used in the highest-weight representation setting of [Jordan2008a]. The
sampling conclusion assumes a normalized vector and a norm-preserving operator.

## Main statements

* `gt_hamiltonian_expansion`: linearity on a four-term operator expression.
* `polynomial_highest_weight_matrix_element_estimate`: the real matrix-element deviation bound.

## References

* [Jordan, 2008][Jordan2008a]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.GroupReps08.MainResults.Common

namespace Qatlib.Papers.GroupReps08.MainResults.PolynomialHighestWeight

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A complex linear map on operators distributes over the four-term expression with
coefficients `h11`, `h12`, `star h12`, and `h22` [Jordan2008a]. -/
theorem gt_hamiltonian_expansion
    (a : (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) (h11 h12 h22 : ℂ)
    (E11 E12 E21 E22 : E →L[ℂ] E) :
    a (h11 • E11 + h12 • E12 + star h12 • E21 + h22 • E22)
      = h11 • a E11 + h12 • a E12 + star h12 • a E21 + h22 • a E22 := by
  simp only [map_add, map_smul]

/-- For normalized `ψ` and norm-preserving `U`, the complex norm of the matrix element `⟪ψ, U
ψ⟫` is at most one [Jordan2008a]. -/
theorem gt_matrix_element_abs_le_one (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : ‖⟪ψ, U ψ⟫_ℂ‖ ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) ψ (U ψ)
  rw [hψ, hU ψ, hψ] at h
  simpa using h

/-- For normalized `ψ` and norm-preserving `U`, `L > 0` Hadamard samples estimate the real
matrix element with deviation probability at most `1 / (L * ε^2)` for positive `ε`
[Jordan2008a]. -/
theorem polynomial_highest_weight_matrix_element_estimate (U : E →L[ℂ] E) (ψ : E)
    (hψ : ‖ψ‖ = 1) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := L) (hadamardLaw U ψ hψ hU)
        (fun ω => ε < |FinDist.avg readout ω - (⟪ψ, U ψ⟫_ℂ).re|)
      ≤ 1 / (L * ε ^ 2) :=
  hadamard_sample_bound U ψ hψ hU L hL ε hε

end Qatlib.Papers.GroupReps08.MainResults.PolynomialHighestWeight
