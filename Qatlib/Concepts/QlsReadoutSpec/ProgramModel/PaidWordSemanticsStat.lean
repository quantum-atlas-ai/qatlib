/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels

/-!
# Paid-word semantics specification

The proposition `Clause1PaidWordSemantics` specifies unitarity, composition, adjoint, and
accounting laws for legal words over unitary oracles. It also specifies normalized execution and
the density-matrix properties of the unconditional output. Related mathematical background is
given in [Watrous2018].

## Main statements

* `Clause1PaidWordSemantics`: The combined paid-word semantic contract.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
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
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The assertion collecting unitarity, concatenation, adjoint, legality, and call-count laws
for paid words, together with normalized execution and positive semidefinite trace-one
unconditional output densities for normalized inputs. -/
def Clause1PaidWordSemantics : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (r slots : ℕ)
    (oracles : ℕ → Matrix H H ℂ) (C D : Word H r),
    (∀ j < slots, oracles j ∈ Matrix.unitaryGroup H ℂ) → legal slots C →
    wordMatrix oracles C ∈ Matrix.unitaryGroup (Space H r) ℂ ∧
    wordMatrix oracles (C++D)=wordMatrix oracles D*wordMatrix oracles C ∧
    wordMatrix oracles (wordAdjoint C)=(wordMatrix oracles C)ᴴ ∧
    legal slots (wordAdjoint C) ∧
    (∀ j, calls (wordAdjoint C) j=calls C j ∧ calls (C++D) j=calls C j+calls D j) ∧
    ∀ (hr : 0 < r) (ω : QState H), Normalized ω →
      Normalized (run hr oracles C ω) ∧
      outputMass (1 : Matrix H H ℂ) Finset.univ (run hr oracles C ω)=1 ∧
      (outputDensity (1 : Matrix H H ℂ) Finset.univ (run hr oracles C ω)).PosSemidef ∧
      Matrix.trace (outputDensity (1 : Matrix H H ℂ) Finset.univ (run hr oracles C ω))=1

end Qatlib.Concepts.QlsReadoutSpec.ProgramModel
