/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioning
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.MatrixAccess.FrameFilterProd
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioningPseudoinverse
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

def BlockPreconditioningCorrectedSubgoal : Prop :=
  (∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ) (b : QState O) (s : ℝ),
    ProjectedUnitaryEncoding A U L R → Normalized b → 0< s → s<1 →
    IsBlockEncoding (preconditionedUnitary L b s U) false (liftedStateScaling L b s*U) 1 ∧
    ProjectedUnitaryEncoding (stateScaling s b*A) (preconditionedUnitary L b s U) (flagFrame L) (flagFrame R) ∧
    Lᴴ*liftedStateScaling L b s=stateScaling s b*Lᴴ ∧
    stateScaling s b*stateScalingInverse s b=1 ∧ stateScalingInverse s b*stateScaling s b=1) ∧
  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (b : QState O) (s : ℝ),
    0< s → s<1 → Normalized b → (∃ z : QState I,A*ᵥz=b) →
    matrixPseudoinverse (stateScaling s b*A)=matrixPseudoinverse A*stateScalingInverse s b ∧
    matrixPseudoinverse (stateScaling s b*A)*ᵥb=((s:ℝ)⁻¹:ℂ)•(matrixPseudoinverse A*ᵥb)) ∧
  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (b : QState O) (κ t c s : ℝ),
    Normalized b → 1<κ → 1< c → 0< t → s=t/(c*κ) →
    (∀ i : Fin (Fintype.card I),0< matrixSingularValues A i → κ⁻¹≤ matrixSingularValues A i) →
    (∃ z : QState I,A*ᵥz=b) →
    (t/c<‖stateVector (matrixPseudoinverse A*ᵥb)‖ ∧ ‖stateVector (matrixPseudoinverse A*ᵥb)‖< c*t) →
    ‖matrixPseudoinverse (stateScaling s b*A)‖≤2*c^2*κ ∧
    ∀ i : Fin (Fintype.card I),0< matrixSingularValues (stateScaling s b*A) i → (2*c^2*κ)⁻¹≤ matrixSingularValues (stateScaling s b*A) i)
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
