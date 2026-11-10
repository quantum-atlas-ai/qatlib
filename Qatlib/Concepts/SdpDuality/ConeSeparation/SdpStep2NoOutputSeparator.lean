/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.NormNum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SdpMmwSolver.OracleError

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpDuality.ConeSeparation
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

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
