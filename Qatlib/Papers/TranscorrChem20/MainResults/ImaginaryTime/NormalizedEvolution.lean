/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.MatrixEvolution
import Qatlib.Concepts.ImaginaryFlow.Normalize
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.ImaginaryFlow.Normalize

namespace Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime

theorem actualState_ne_zero {d : ℕ} (H g : Op d) (φ : State d) (hφ : φ ≠ 0) (t : ℝ) :
    actualState H g φ t ≠ 0 := rawState_ne_zero (tc H g) φ hφ t

theorem actual_tc_normalized_norm {d : ℕ} (H g : Op d) (φ : State d) (hφ : φ ≠ 0) (t : ℝ) :
    ‖normalized (actualState H g φ t)‖ = 1 := actual_normalized_norm (tc H g) φ hφ t

theorem actual_tc_normalized_ode {d : ℕ} (H g : Op d) (φ : State d) (hφ : φ ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => normalized (actualState H g φ s))
      (- Matrix.toEuclideanLin (tc H g) (normalized (actualState H g φ t)) +
        (inner ℂ (normalized (actualState H g φ t))
          (Matrix.toEuclideanLin (tc H g) (normalized (actualState H g φ t)))).re •
            normalized (actualState H g φ t)) t := actual_normalized_ode (tc H g) φ hφ t

end Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime
