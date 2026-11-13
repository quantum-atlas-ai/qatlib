/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.MatrixEvolution
import Qatlib.Concepts.ImaginaryFlow.Normalize

/-!
# Normalized transcorrelated imaginary-time equation

This module verifies nonvanishing and unit normalization for exact finite transcorrelated
evolution. The derivative of the normalized state contains the real part of the transcorrelated
energy expectation, giving the normalized equation for a possibly non-Hermitian generator. See
[McArdleTew2020].

## Main statements

* `actualState_ne_zero`: A nonzero initial state stays nonzero.
* `actual_tc_normalized_ode`: Derivative formula for the normalized trajectory.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.ImaginaryFlow.Normalize

namespace Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime

/-- Exact transcorrelated imaginary-time evolution preserves nonvanishing of the initial state.
See [McArdleTew2020]. -/
theorem actualState_ne_zero {d : ℕ} (H g : Op d) (φ : State d) (hφ : φ ≠ 0) (t : ℝ) :
    actualState H g φ t ≠ 0 := rawState_ne_zero (tc H g) φ hφ t

/-- The normalization of an evolved nonzero state has norm one. See [McArdleTew2020]. -/
theorem actual_tc_normalized_norm {d : ℕ} (H g : Op d) (φ : State d) (hφ : φ ≠ 0) (t : ℝ) :
    ‖normalized (actualState H g φ t)‖ = 1 := actual_normalized_norm (tc H g) φ hφ t

/-- The normalized trajectory has derivative equal to minus the transcorrelated generator
applied to the state plus its real energy expectation times the state. See [McArdleTew2020]. -/
theorem actual_tc_normalized_ode {d : ℕ} (H g : Op d) (φ : State d) (hφ : φ ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => normalized (actualState H g φ s))
      (- Matrix.toEuclideanLin (tc H g) (normalized (actualState H g φ t)) +
        (inner ℂ (normalized (actualState H g φ t))
          (Matrix.toEuclideanLin (tc H g) (normalized (actualState H g φ t)))).re •
            normalized (actualState H g φ t)) t := actual_normalized_ode (tc H g) φ hφ t

end Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime
