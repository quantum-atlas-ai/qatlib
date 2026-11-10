/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Qatlib.Papers.GroupReps08.MainResults.Common
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.GroupReps08.MainResults.Common

namespace Qatlib.Papers.GroupReps08.MainResults.SchurTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem schur_matrix_element_abs_le_one (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : ‖⟪ψ, U ψ⟫_ℂ‖ ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) ψ (U ψ)
  rw [hψ, hU ψ, hψ] at h
  simpa using h

theorem schur_transform_matrix_element_estimate (U : E →L[ℂ] E) (ψ : E)
    (hψ : ‖ψ‖ = 1) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := L) (hadamardLaw U ψ hψ hU)
        (fun ω => ε < |FinDist.avg readout ω - (⟪ψ, U ψ⟫_ℂ).re|)
      ≤ 1 / (L * ε ^ 2) :=
  hadamard_sample_bound U ψ hψ hU L hL ε hε

end Qatlib.Papers.GroupReps08.MainResults.SchurTransform
