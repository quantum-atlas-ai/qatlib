/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitnessDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib
open Matrix

set_option autoImplicit false

noncomputable def mwGoodProjector (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun u u' => if u = u' ∧ (u ∈ programOutputEvent p) then 1 else 0

noncomputable def mwBadProjector (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  1 - mwGoodProjector p

noncomputable def mwRound (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun u u' =>
    if u = u' then (if u ∈ programOutputEvent p then 0 else 1) else 0

noncomputable def mwProcess (p : WitnessVerifierProgram) (k : ℕ) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun u u' =>
    if u = u' then (if u ∈ programOutputEvent p then 0 else 1) else 0

def mwVerificationWires (p : WitnessVerifierProgram) : ℕ :=
  programQubits p - p.witnessBits

end Qatlib.Concepts.LocalMachine.LocalTransport
