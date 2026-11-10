/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.RectDilation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
namespace Qatlib.Papers.LinearSystems09.HermitianLift
open Matrix

theorem source_rectangular_solution (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ)
    (b : QState (Fin M)) :
    (Matrix.fromBlocks (0 : Matrix (Fin M) (Fin M) ℂ) A Aᴴ 0).IsHermitian ∧
    matrixPseudoinverse (Matrix.fromBlocks 0 A Aᴴ 0) *ᵥ
      Sum.elim b (0 : QState (Fin N)) =
      Sum.elim (0 : QState (Fin M)) (leastSquaresVector A b) ∧
    IsEuclideanLeastSquares A b (leastSquaresVector A b) ∧
    (∀ y : QState (Fin N), IsEuclideanLeastSquares A b y →
      ‖stateVector y‖ = ‖stateVector (leastSquaresVector A b)‖ → y = leastSquaresVector A b) ∧
    (leastSquaresOverlap A b = 0 ↔ leastSquaresVector A b = 0) ∧
    ‖stateVector b‖^2 = (leastSquaresOverlap A b)^2 +
      ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖^2 := by
  have h := Qatlib.Concepts.QlsReadoutSpec.RectDilation.rectangular_dilation_solution A b
  have hi : Qatlib.Concepts.QlsReadoutSpec.RectDilation.dilationInput (I := Fin N) b =
      Sum.elim b (0 : QState (Fin N)) := by
    funext i
    cases i <;> rfl
  rw [hi] at h
  simpa only [Qatlib.Concepts.QlsReadoutSpec.RectDilation.hermitianDilation_eq_fromBlocks] using h

end Qatlib.Papers.LinearSystems09.HermitianLift
