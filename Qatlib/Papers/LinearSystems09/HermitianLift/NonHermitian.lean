/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinearSystems09.HermitianLift.Basic
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtModulusTransport
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Non-Hermitian systems and signed singular values

This module exposes the rectangular-to-Hermitian reduction from [HarrowHassidimLloyd2009]
together with its signed singular spectrum. The block formula
`source_A33_dilation_eq_fromBlocks` identifies the dilation, and
`source_A33_rectangular_reduction` records the resulting least-squares solution properties.

## Main statements

* `source_A33_rectangular_reduction`: Packages the pseudoinverse reduction and least-squares
  identities.
* `source_A33_signed_singular_spectrum`: Identifies each dilation eigenvalue as a signed
  singular value.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.HermitianLift.NonHermitian

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability

/-- The rectangular Hermitian lift is Hermitian and its pseudoinverse produces the embedded
least-squares vector, with uniqueness among least-squares vectors of equal norm. It also
satisfies the zero-overlap equivalence and squared residual identity for the non-Hermitian
reduction in [HarrowHassidimLloyd2009]. -/
theorem source_A33_rectangular_reduction (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ)
    (b : QState (Fin M)) :
    (Matrix.fromBlocks (0 : Matrix (Fin M) (Fin M) ℂ) A Aᴴ 0).IsHermitian ∧
      matrixPseudoinverse (Matrix.fromBlocks 0 A Aᴴ 0) *ᵥ
          Sum.elim b (0 : QState (Fin N)) =
        Sum.elim (0 : QState (Fin M)) (leastSquaresVector A b) ∧
      IsEuclideanLeastSquares A b (leastSquaresVector A b) ∧
      (∀ y : QState (Fin N), IsEuclideanLeastSquares A b y →
        ‖stateVector y‖ = ‖stateVector (leastSquaresVector A b)‖ →
          y = leastSquaresVector A b) ∧
      (leastSquaresOverlap A b = 0 ↔ leastSquaresVector A b = 0) ∧
      ‖stateVector b‖ ^ 2 = (leastSquaresOverlap A b) ^ 2 +
        ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ ^ 2 :=
  Qatlib.Papers.LinearSystems09.HermitianLift.source_rectangular_solution M N A b

/-- Each ordered eigenvalue of the Hermitian dilation is a singular value of `A` or its
negative, as used in the non-Hermitian reduction of [HarrowHassidimLloyd2009]. -/
theorem source_A33_signed_singular_spectrum {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ)
    (j : Fin (Fintype.card (Fin M ⊕ Fin N))) :
    ∃ k : ℕ,
      orderedHermitianValues (hermitianDilation_adjoint A) j = matrixSingularValues A k ∨
        orderedHermitianValues (hermitianDilation_adjoint A) j = -matrixSingularValues A k :=
  dilation_orderedValue_signed_singular A j

/-- The Hermitian dilation of `A` has zero diagonal blocks and off-diagonal blocks `A` and `Aᴴ`
[HarrowHassidimLloyd2009]. -/
theorem source_A33_dilation_eq_fromBlocks {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) :
    hermitianDilation A = Matrix.fromBlocks (0 : Matrix (Fin M) (Fin M) ℂ) A Aᴴ 0 :=
  rfl

end Qatlib.Papers.LinearSystems09.HermitianLift.NonHermitian
