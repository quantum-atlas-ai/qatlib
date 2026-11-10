/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.MmwCore.SdpLemma7SourceCoefficientsStat
import Qatlib.Concepts.MatrixWeights.LambdaMin
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.MatrixWeights.LambdaMin

namespace Qatlib.Concepts.SdpMmwSolver.MmwCore

theorem sdpLemma7SourceCoefficients : SdpLemma7SourceCoefficients := by
  exact matrix_mw_source_min_eigenvalue

end Qatlib.Concepts.SdpMmwSolver.MmwCore
