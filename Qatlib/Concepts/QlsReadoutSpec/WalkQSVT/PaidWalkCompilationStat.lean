/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.SpectralModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def PaidWalkPaidWalkCompilation : Prop :=
  ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (G : Matrix H I ℂ) (r : ℕ) (C : Word H r), IsIsometry G → legal 1 C →
    legal 1 (compileWalk G C) ∧ calls (compileWalk G C) 0=calls C 0 ∧
    gateCount (compileWalk G C)=gateCount C+calls C 0 ∧
    ∀ (U : Matrix H H ℂ), U ∈ Matrix.unitaryGroup H ℂ →
      wordMatrix (fun _ =>  U) (compileWalk G C)=wordMatrix (fun _ =>  walk G U) C

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
