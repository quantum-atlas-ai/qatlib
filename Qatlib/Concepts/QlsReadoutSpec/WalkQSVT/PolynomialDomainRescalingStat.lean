/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels

/-!
# Polynomial domain-rescaling specification

The proposition `Clause27PolynomialDomainRescaling` specifies a same-length coefficient vector
representing the original Chebyshev expansion at twice its argument. It also equates the
half-interval and full-interval suprema and relates evaluation at two matrix normalizations.
Related mathematical background is given in [LowSu2026].

## Main statements

* `Clause27PolynomialDomainRescaling`: The scalar and matrix domain-rescaling contract.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
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

/-- The assertion that every finite Chebyshev expansion has a same-length coefficient vector for
evaluation at twice the argument, with equal half-interval and full-interval suprema and the
corresponding matrix-normalization identity. -/
def Clause27PolynomialDomainRescaling : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ), ∃ q : Fin n → ℂ,
    (∀ x : ℝ, chebValue q x=chebValue c (2*x)) ∧
    polynomialSup q (1/2)=polynomialSup c 1 ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (αA : ℝ),
      0 < αA → chebOperator q ((2*αA : ℂ)⁻¹ • A)=
        chebOperator c ((αA : ℂ)⁻¹ • A)

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
