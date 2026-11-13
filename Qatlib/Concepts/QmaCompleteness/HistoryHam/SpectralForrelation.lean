/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Spectral forrelation and witness mass

This module defines the characteristic projector `charProjector`, the squared operator norm
`spectralForrelation` of a projector-Hadamard-projector product, and its squared output norm on
a witness, `forrWitnessMass`. These quantities provide the matrix formulation used by the
forrelation verifier constructions.

The finite-dimensional state and operator framework follows the standard quantum-information
setting of [Watrous2018].

## Main statements

* `charProjector`: the diagonal projector associated with a Boolean predicate.
* `spectralForrelation`: squared operator norm of the restricted Hadamard transform.
* `forrWitnessMass`: squared Euclidean norm of its action on a witness.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

open Qatlib
open scoped Matrix.Norms.L2Operator

variable (n : ℕ)

/-- The diagonal matrix on `Reg n` with diagonal entry one where `f` is true and zero elsewhere. -/
def charProjector (f : Reg n → Bool) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if f x then 1 else 0

/-- The square of the Euclidean operator norm of `charProjector n U * HadamardN n *
charProjector n S`. -/
noncomputable def spectralForrelation (S U : Reg n → Bool) : ℝ :=
  (‖charProjector n U * HadamardN n * charProjector n S‖ : ℝ) ^ 2

/-- The squared Euclidean norm of the vector obtained by applying `charProjector n U * HadamardN
n * charProjector n S` to the witness vector `ψ`. -/
noncomputable def forrWitnessMass (S U : Reg n → Bool) (ψ : QState (Reg n)) : ℝ :=
  ‖toEuclidean_fromVec ((charProjector n U * HadamardN n * charProjector n S).mulVec ψ)‖ ^ 2

end Qatlib.Concepts.QmaCompleteness.HistoryHam
