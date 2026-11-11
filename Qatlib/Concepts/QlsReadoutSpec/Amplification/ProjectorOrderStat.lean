/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels

/-!
# Specification of orthogonal projector order

`Clause2ProjectorOrder` packages seven equivalent criteria for one orthogonal projector to be
contained in another. The criteria use fixed vectors, kernels, matrix absorption, the difference
projector, positive semidefinite order, and domination of projected vector norms.

The positive semidefinite order viewpoint is standard in matrix analysis [Bhatia1997]. For
partially ordered projections, see [LowSu2026].

## Main statements

* `Clause2ProjectorOrder`: States the equivalent order criteria for two orthogonal projectors.

## References

* [Bhatia, 1997][Bhatia1997]
* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
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
namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The projector-order specification equates `Q * P = P` with range inclusion, reverse kernel
inclusion, the reversed absorption identity, the difference being an orthogonal projector or
positive semidefinite, the compressed identity, and domination of projected norms. -/
def Clause2ProjectorOrder : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (P Q : Matrix H H ℂ),
    IsOrthogonalProjector P → IsOrthogonalProjector Q →
    ((∀ ψ : QState H, P *ᵥ ψ=ψ → Q *ᵥ ψ=ψ) ↔ Q*P=P) ∧
    ((∀ ψ : QState H, Q *ᵥ ψ=0 → P *ᵥ ψ=0) ↔ Q*P=P) ∧
    (Q*P=P ↔ P*Q=P) ∧ (Q*P=P ↔ IsOrthogonalProjector (Q-P)) ∧
    (Q*P=P ↔ P*Q*P=P) ∧ (Q*P=P ↔ (Q-P).PosSemidef) ∧
    (Q*P=P ↔ ∀ ψ : QState H, normVec (P *ᵥ ψ) ≤ normVec (Q *ᵥ ψ))

end Qatlib.Concepts.QlsReadoutSpec.Amplification
