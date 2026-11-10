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
namespace Qatlib.Concepts.SdpDuality.ConeSeparation

theorem not_sdpExpectationEstimation : ¬ SdpExpectationEstimation := by
  intro h
  obtain ⟨⟨copies, meas, _, hm, _, hbound⟩, _⟩ :=
    h 1 1 1 8 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbound
  exact (not_le_of_gt hm) hbound

end Qatlib.Concepts.SdpDuality.ConeSeparation
