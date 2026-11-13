/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.QsvtCore.LinearSystems.PseudoinverseState

/-!
# Near optimal pseudoinverse specification

This module defines `NearOptimalPseudoinverse` for projected unitary encodings with positive
singular values bounded below by `κ⁻¹`. The specification includes the phase length bound `32 *
κ * log (κ / ε)`, a scaled pseudoinverse encoding, exact compilation counts, and postselection
guarantees for both consistent and least squares inputs. The mathematical background is
developed in [GilyenSuLowWiebe2019].

## Main statements

* `NearOptimalPseudoinverse`: the combined encoding, cost, and solution state assertion.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Matrix

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The assertion that a gapped projected unitary encoding has a phase word of length at most
`32 * κ * log (κ / ε)` giving a positive scaled pseudoinverse encoding with error `2 * c *
ε` and explicit counts. It also specifies minimum norm and least squares solution state
errors and success probability bounds. -/
def NearOptimalPseudoinverse : Prop :=
  ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ ε : ℝ),
    1 < κ → 0 < ε → ε < 1 / 2 → ProjectedUnitaryEncoding A U L R →
    (∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      κ⁻¹ ≤ matrixSingularValues A i) →
    ∃ (m : ℕ) (c : ℝ) (Φ : List ℝ),
      Φ.length = 2 * m + 1 ∧
      (2 * m + 1 : ℝ) ≤ 32 * κ * Real.log (κ / ε) ∧
      0 < c ∧ c ≤ (4 * κ)⁻¹ ∧
      BlockEncoding ((c : ℂ) • matrixPseudoinverse A)
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
        (sourceAverageClean R) (sourceAverageClean L) 1 (2 * c * ε) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) = (2 * m + 1, 2 * m, 2 * m + 2, 2 * m + 1) ∧
      (∀ v : QState O, Normalized v → (∃ z : QState I, A *ᵥ z = v) →
        (c * (1 - 2 * ε)) ^ 2 ≤
          postselectionProbability (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
            (sourceAverageClean R) (sourceAverageClean L) v ∧
        ∃ φ : QState I,
          postselectionOutput (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
            (sourceAverageClean R) (sourceAverageClean L) v = some φ ∧
          IsMinimumNormSolutionState A v φ (4 * ε)) ∧
      (∀ v : QState O, Normalized v → 2 * ε < leastSquaresOverlap A v →
        (c * (leastSquaresOverlap A v - 2 * ε)) ^ 2 ≤
          postselectionProbability (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
            (sourceAverageClean R) (sourceAverageClean L) v ∧
        ∃ φ : QState I,
          postselectionOutput (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
            (sourceAverageClean R) (sourceAverageClean L) v = some φ ∧
          IsLeastSquaresSolutionState A v φ (4 * ε / leastSquaresOverlap A v))

end Qatlib.Concepts.QsvtCore.LinearSystems
