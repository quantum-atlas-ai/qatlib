/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.NormNum

/-!
# Refutation of the Step 2 no-output separator contract

This module proves `not_sdpStep2NoOutputSeparator` by specializing the diagnostic contract to
one-dimensional zero matrices and a zero candidate vector. The resulting numerical inequality
yields a contradiction.

No-output separation is an ingredient in the SDP search framework associated with
[BrandaoSvore2017]. The theorem identifies a failure of the particular formal diagnostic
contract `SdpStep2NoOutputSeparator`.

## Main statements

* `not_sdpStep2NoOutputSeparator`: refutation of the diagnostic separator contract.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SdpMmwSolver.OracleError

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpDuality.ConeSeparation
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The diagnostic contract `SdpStep2NoOutputSeparator` is false. -/
theorem not_sdpStep2NoOutputSeparator : ¬ SdpStep2NoOutputSeparator := by
  intro h
  have hf := h 1 1 (fun _ => 0) 0 (fun _ => 1) (fun _ _ => 0)
    1 1 (1 / 10) 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; exact ⟨Matrix.isHermitian_zero, by simp⟩)
    ⟨Matrix.isHermitian_zero, by simp⟩ (by intro i; norm_num)
    (by intro i; rfl) (fun _ => 0) (by intro i; norm_num) (by simp)
  norm_num at hf

end Qatlib.Concepts.SdpDuality.ConeSeparation
