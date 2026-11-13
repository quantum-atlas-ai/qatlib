/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitnessDefs

/-!
# Matrices for uniform QMA amplification

This module defines `mwGoodProjector` and `mwBadProjector` from the verifier's output event,
together with the elementary matrices `mwRound` and `mwProcess`. Both latter definitions are the
diagonal rejection projector, and `mwProcess` is independent of its parameter `k`. The notation
is motivated by witness-preserving amplification in [MarriottWatrous2005].

The auxiliary count `mwVerificationWires` subtracts the witness width from the total program
width. These definitions provide matrix and register-size data for subsequent developments.

## Main statements

- `mwGoodProjector` is the diagonal indicator matrix of the accepting output event.
* `mwBadProjector` is its complement, while `mwRound` and `mwProcess` specify the rejecting
  diagonal entries directly.
- `mwVerificationWires` counts the program wires outside the witness register.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib
open Matrix

set_option autoImplicit false

/-- Define the diagonal projector onto computational-basis registers in the verifier's accepting
output event. -/
noncomputable def mwGoodProjector (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun u u' => if u = u' ∧ (u ∈ programOutputEvent p) then 1 else 0

/-- Define the rejecting projector as the identity matrix minus `mwGoodProjector`. -/
noncomputable def mwBadProjector (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  1 - mwGoodProjector p

/-- Define the diagonal matrix with entry zero on accepting basis registers and entry one on
rejecting basis registers. -/
noncomputable def mwRound (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun u u' =>
    if u = u' then (if u ∈ programOutputEvent p then 0 else 1) else 0

/-- Define the diagonal rejection projector for a parameter `k`. The matrix is independent of
`k` and has the same entries as `mwRound`. -/
noncomputable def mwProcess (p : WitnessVerifierProgram) (k : ℕ) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun u u' =>
    if u = u' then (if u ∈ programOutputEvent p then 0 else 1) else 0

/-- Count the non-witness program wires by subtracting the witness width from the total program
width. -/
def mwVerificationWires (p : WitnessVerifierProgram) : ℕ :=
  programQubits p - p.witnessBits

end Qatlib.Concepts.LocalMachine.LocalTransport
