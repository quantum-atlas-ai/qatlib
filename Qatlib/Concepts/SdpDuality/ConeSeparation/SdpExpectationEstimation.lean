/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.NormNum

/-!
# Refutation of the SDP expectation estimation contract

This module proves `not_sdpExpectationEstimation`, the negation of the diagnostic contract
`SdpExpectationEstimation`. Its proof specializes the contract to fixed numerical parameters and
derives incompatible bounds on the measurement count.

Expectation estimation is an ingredient in quantum SDP algorithms such as [BrandaoSvore2017];
the result here concerns the specific formal diagnostic contract.

## Main statements

* `not_sdpExpectationEstimation`: refutation of `SdpExpectationEstimation`.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SdpMmwSolver.OracleError

set_option autoImplicit false
namespace Qatlib.Concepts.SdpDuality.ConeSeparation

/-- The diagnostic contract `SdpExpectationEstimation` is false. -/
theorem not_sdpExpectationEstimation : ¬ SdpExpectationEstimation := by
  intro h
  obtain ⟨⟨copies, meas, _, hm, _, hbound⟩, _⟩ :=
    h 1 1 1 8 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbound
  exact (not_le_of_gt hm) hbound

end Qatlib.Concepts.SdpDuality.ConeSeparation
