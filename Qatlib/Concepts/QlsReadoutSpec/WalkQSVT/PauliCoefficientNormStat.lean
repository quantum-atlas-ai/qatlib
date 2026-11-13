/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.SpectralModels

/-!
# Pauli coefficient-norm specification

The proposition `Clause13PauliCoefficientNorm` specifies the operator-norm distance and
Gram-matrix identities for the four-real-parameter matrix `pauliCoefficients`. These identities
connect matrix errors with Euclidean coefficient errors. Related mathematical background is
given in [LowSu2026].

## Main statements

* `Clause13PauliCoefficientNorm`: The Pauli coefficient norm and Gram identities.

## References

* [Low and Su, 2026, Lemma 21][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- The assertion that real Pauli coefficient matrices have operator-norm distance equal to
Euclidean coefficient distance and Gram matrix equal to the identity scaled by the sum of
squared coefficients. -/
def Clause13PauliCoefficientNorm : Prop :=
  ∀ a b c d a' b' c' d' : ℝ,
    ‖pauliCoefficients a b c d-pauliCoefficients a' b' c' d'‖=
      Real.sqrt ((a-a')^2+(b-b')^2+(c-c')^2+(d-d')^2) ∧
    (pauliCoefficients a b c d)ᴴ*pauliCoefficients a b c d=
      (((a^2+b^2+c^2+d^2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
