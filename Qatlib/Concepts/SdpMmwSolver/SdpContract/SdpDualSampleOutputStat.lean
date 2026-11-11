/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros

/-!
# Dual sample output contract

`SdpDualSampleOutput` specifies how the dual certificate is encoded by a positive scale and a
probability distribution after `sdpDualCertRounds` rounds. It also states the exact formula for
the scale.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpDualSampleOutput`: The contract asserting positivity and normalization of the dual
  sampling output, exact certificate factorization, and the correction-plus-average formula for
  its scale.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SdpDuality.ConeSeparation

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The contract asserting positivity and normalization of the dual sampling output, exact
certificate factorization, and the correction-plus-average formula for its scale. -/
def SdpDualSampleOutput : Prop :=
  ∀ (D m : ℕ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ η : ℝ),
    0 < α → 0 < R → 0 < δ → (∀ t i, 0 ≤ y t i) →
    (0 < sdpDualSampleScale m δ α R j₀ y (sdpDualCertRounds D R δ η) ∧
    (∀ i, 0 ≤ sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) ∧
    (∑ i, sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) = 1 ∧
    (∀ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i =
      sdpDualSampleScale m δ α R j₀ y (sdpDualCertRounds D R δ η) *
        sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) ∧
    sdpDualSampleScale m δ α R j₀ y (sdpDualCertRounds D R δ η) =
      δ*α/(2*R) +
        (∑ t ∈ Finset.range (sdpDualCertRounds D R δ η), ∑ i, y t i)/
          (sdpDualCertRounds D R δ η))

end Qatlib.Concepts.SdpMmwSolver.SdpContract
