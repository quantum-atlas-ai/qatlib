/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.BranchUnitary.Truncation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Papers.NestedQWalk12.CoherentTrunc
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Foundations.MatrixGeometry.BranchUnitary
variable {Label Sys : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype Sys] [DecidableEq Sys]

def sourceState (α : Label → ℂ) (conditional : Label → State Sys) : State (Label × Sys) :=
  fun x => α x.1 * conditional x.1 x.2

def encode (ψ : State (Label × Sys)) : State (Sys × Label) := fun x => ψ (x.2,x.1)

omit [Fintype Label] [DecidableEq Label] [Fintype Sys] [DecidableEq Sys] in

theorem encode_inverse (ψ : State (Label × Sys)) :
    (fun x : Label × Sys => encode ψ (x.2,x.1)) = ψ := rfl

omit [Fintype Label] [DecidableEq Label] [Fintype Sys] [DecidableEq Sys] in

theorem encoded_source (α : Label → ℂ) (conditional : Label → State Sys) :
    encode (sourceState α conditional) = coherent α conditional := rfl

theorem actual_coherent_conversion (U : Label → Matrix Sys Sys ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup Sys ℂ)
    (α : Label → ℂ) (conditional : Label → State Sys)
    (hα : ∑ i, ‖α i‖ ^ 2 = 1) (hs : ∀ i, Normalized (conditional i))
    (queries : Label → ℕ) (cutoff : ℕ) :
    ‖toHilbert (controlled U *ᵥ encode (sourceState α conditional))‖ = 1 ∧
      ‖toHilbert (controlled (truncated U queries cutoff) *ᵥ
        encode (sourceState α conditional))‖ = 1 ∧
      1 - 2 * tailMass α queries cutoff ≤
        ‖inner ℂ (toHilbert (controlled U *ᵥ encode (sourceState α conditional)))
          (toHilbert (controlled (truncated U queries cutoff) *ᵥ
            encode (sourceState α conditional)))‖ := by
  rw [encoded_source]
  exact truncation_hilbert_overlap U hU α conditional hα hs queries cutoff

theorem actual_mean_overlap (U : Label → Matrix Sys Sys ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup Sys ℂ)
    (α : Label → ℂ) (conditional : Label → State Sys)
    (hα : ∑ i, ‖α i‖ ^ 2 = 1) (hs : ∀ i, Normalized (conditional i))
    (queries : Label → ℕ) (cutoff : ℕ) (hcut : 0 < cutoff) :
    1 - 2 * (meanQueries α queries / cutoff) ≤
      ‖inner ℂ (toHilbert (controlled U *ᵥ encode (sourceState α conditional)))
        (toHilbert (controlled (truncated U queries cutoff) *ᵥ
          encode (sourceState α conditional)))‖ := by
  have ht := tailMass_le_mean α queries cutoff hcut
  have hn := (actual_coherent_conversion U hU α conditional hα hs queries cutoff).2.2
  linarith

end Qatlib.Papers.NestedQWalk12.CoherentTrunc
