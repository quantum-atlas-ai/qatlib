/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverseLine
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.MatrixAccess.FrameFilterProd
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioning
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioningPseudoinverse
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

def OptimalCoefficientBlockEncodingSubgoal : Prop :=
  ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (κ ε t c s : ℝ) (b : QState O),
    1 < κ → 0 < ε → ε < 1 / 2 → 1 < c →
    ProjectedUnitaryEncoding A U L R → Normalized b →
    s = t / (c * κ) → 0 < t →
    (∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      κ⁻¹ ≤ matrixSingularValues A i) →
    (∃ z : QState I, A *ᵥ z = b) →
    t / c < ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ ∧
      ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ < c * t →
    ∃ (m : ℕ) (c₀ : ℝ) (Φ : List ℝ),
      Φ.length = 2 * m + 1 ∧
      (2 * m + 1 : ℝ) ≤ 32 * (2 * c ^ 2 * κ) * Real.log ((2 * c ^ 2 * κ) / ε) ∧
      0 < c₀ ∧ c₀ ≤ (4 * (2 * c ^ 2 * κ))⁻¹ ∧
      BlockEncoding ((c₀ : ℂ) • matrixPseudoinverse (stateScaling s b * A))
        (sourceRealWord (preconditionedUnitary L b s U)
          (rangeProjector (flagFrame R)) (rangeProjector (flagFrame L)) Φ)ᴴ
        (sourceAverageClean (flagFrame R)) (sourceAverageClean (flagFrame L))
        1 (2 * c₀ * ε) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2 * m + 1, 2 * m, 2 * m + 2, 2 * m + 1) ∧
      (c₀ * κ * (1 - 2 * ε)) ^ 2 ≤
        postselectionProbability
          (sourceRealWord (preconditionedUnitary L b s U)
            (rangeProjector (flagFrame R)) (rangeProjector (flagFrame L)) Φ)ᴴ
          (sourceAverageClean (flagFrame R)) (sourceAverageClean (flagFrame L)) b ∧
      ∃ φ : QState I,
        postselectionOutput
          (sourceRealWord (preconditionedUnitary L b s U)
            (rangeProjector (flagFrame R)) (rangeProjector (flagFrame L)) Φ)ᴴ
          (sourceAverageClean (flagFrame R)) (sourceAverageClean (flagFrame L)) b =
            some φ ∧
        Normalized φ ∧
        ‖stateVector φ -
            NormedSpace.normalize (stateVector (matrixPseudoinverse A *ᵥ b))‖ ≤
          4 * ε

end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
