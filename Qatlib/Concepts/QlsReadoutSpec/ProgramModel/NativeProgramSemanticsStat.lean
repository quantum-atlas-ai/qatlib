/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.WordComposition.NativeModels

/-!
# Native-program semantics specification

The proposition `Clause36NativeProgramSemantics` collects the semantic guarantees for a legal
native program with two unitary oracle matrices. These guarantees cover unitarity, padding,
resource counts, normalized execution, and conditional density matrices. Related mathematical
background is given in [Watrous2018].

## Main statements

* `Clause36NativeProgramSemantics`: The combined native-program semantic contract.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BitWordCompiler.WordComposition
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
namespace Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The assertion that a legal native program with two unitary oracles has unitary matrix
semantics, exact instruction counts, isometric padding, normalized execution, success mass
at most one, and a positive semidefinite trace-one conditional density whenever its success
mass is positive. -/
def Clause36NativeProgramSemantics : Prop :=
  ∀ (h : ℕ) (p : NativeProgram h) (UA UB : Matrix (Reg h) (Reg h) ℂ),
    nativeLegal p → UA ∈ Matrix.unitaryGroup (Reg h) ℂ →
    UB ∈ Matrix.unitaryGroup (Reg h) ℂ →
    let U := nativeMatrix (fun j => if j=0 then UA else UB) p
    U ∈ Matrix.unitaryGroup (Reg (h+p.ancilla)) ℂ ∧
    nativeCalls p 0+nativeCalls p 1+nativeGates p=p.steps.length ∧
    (nativePadding h p.ancilla)ᴴ*nativePadding h p.ancilla=1 ∧
    ∀ ψ : QState (Reg h), Normalized ψ →
      let out := U *ᵥ (nativePadding h p.ancilla *ᵥ ψ)
      Normalized out ∧ nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out ≤ 1 ∧
      (0 < nativeMass (1 : Matrix (Reg h) (Reg h) ℂ) p out →
        (nativeDensity (1 : Matrix (Reg h) (Reg h) ℂ) p out).PosSemidef ∧
        Matrix.trace (nativeDensity (1 : Matrix (Reg h) (Reg h) ℂ) p out)=1)

end Qatlib.Concepts.QlsReadoutSpec.ProgramModel
