/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.BranchUnitary.Truncation

/-!
# Coherent truncation on native registers

This module relates the label-first source state `sourceState` to the system-first native state
`coherent` by the register permutation `encode`. It applies controlled unitary branches and
their identity-replacement truncations to normalized coherent inputs, in the setting of
[JefferyKothariMagniez2013].

`actual_coherent_conversion` proves normalization of both outputs and an overlap lower bound of
1 minus twice the discarded branch mass. `actual_mean_overlap` replaces that mass by the
weighted mean query count divided by a positive cutoff.

## Main statements

* `encode_inverse`: swapping the registers back recovers the source state.
* `encoded_source`: the encoded source state is the native coherent state.
* `actual_coherent_conversion`: normalization and the tail-mass overlap bound.
* `actual_mean_overlap`: the overlap bound in terms of mean query count.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

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

/-- The label-first coherent state with amplitude α i times the conditional system amplitude on
branch i. -/
def sourceState (α : Label → ℂ) (conditional : Label → State Sys) : State (Label × Sys) :=
  fun x => α x.1 * conditional x.1 x.2

/-- Encodes a label-first state on the system-first carrier by swapping its two register
coordinates. -/
def encode (ψ : State (Label × Sys)) : State (Sys × Label) := fun x => ψ (x.2,x.1)

omit [Fintype Label] [DecidableEq Label] [Fintype Sys] [DecidableEq Sys] in

/-- Swapping the register coordinates back after `encode` recovers the original state; this is
the register identification used for [JefferyKothariMagniez2013]. -/
theorem encode_inverse (ψ : State (Label × Sys)) :
    (fun x : Label × Sys => encode ψ (x.2,x.1)) = ψ := rfl

omit [Fintype Label] [DecidableEq Label] [Fintype Sys] [DecidableEq Sys] in

/-- Encoding `sourceState` gives the native `coherent` state, relating the two register
conventions used for [JefferyKothariMagniez2013]. -/
theorem encoded_source (α : Label → ℂ) (conditional : Label → State Sys) :
    encode (sourceState α conditional) = coherent α conditional := rfl

/-- For normalized amplitudes, normalized conditional states, and unitary branches, the full and
truncated controlled outputs both have norm one, and their Hilbert inner-product norm is at
least 1 minus twice `tailMass`. This gives the coherent-truncation overlap estimate
associated with [Jeffery et al., Lemma 3.3][JefferyKothariMagniez2013]. -/
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

/-- For normalized coherent inputs and unitary branches, a positive cutoff gives an output
overlap norm of at least 1 minus twice `meanQueries` divided by the cutoff, using the
weighted tail estimate associated with [JefferyKothariMagniez2013]. -/
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
