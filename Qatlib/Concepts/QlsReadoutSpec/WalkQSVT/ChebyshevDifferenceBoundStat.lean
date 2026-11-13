/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels

/-!
# Chebyshev difference-bound specification

The proposition `Clause21ChebyshevDifferenceBound` states pointwise and supremum bounds for
Chebyshev expansions on [-1/2, 1/2] in terms of `differenceNorm`. It distinguishes strict bounds
for nonzero coefficient vectors from the identically zero case. Related mathematical background
is given in [LowSu2026].

## Main statements

* `Clause21ChebyshevDifferenceBound`: The finite Chebyshev coefficient-difference estimate.

## References

* [Low and Su, 2026, Lemma 9][LowSu2026]
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

/-- The assertion bounding a finite Chebyshev expansion on the half interval by `sqrt n` times
its coefficient-difference norm, with strict supremum inequality for nonzero coefficients
and vanishing quantities for zero coefficients. -/
def Clause21ChebyshevDifferenceBound : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ),
    (∀ x : ℝ, -1/2 ≤ x → x ≤ 1/2 →
      ‖chebValue c x‖ ≤ Real.sqrt n*differenceNorm c) ∧
    ((∃ k, c k≠0) → polynomialSup c (1/2) < Real.sqrt n*differenceNorm c) ∧
    ((∀ k, c k=0) → polynomialSup c (1/2)=0 ∧ differenceNorm c=0)

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
