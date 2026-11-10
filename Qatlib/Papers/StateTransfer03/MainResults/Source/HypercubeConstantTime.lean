/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Source.CartesianPropagator
import Qatlib.Papers.StateTransfer03.MainResults.Source.PairChainTransfer
set_option warningAsError false

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

theorem onelink_hypercube_transfer (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue (pathEigenvalue 2) d)
        (powerWeight (fun k => (pathWeight 2 k : ℂ)) d) t =
      (-Complex.I * (Real.sin t : ℂ)) ^ d := by
  rw [path_power_amplitude, pathSpectralAmplitude_two]

theorem twolink_hypercube_transfer (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue (pathEigenvalue 3) d)
        (powerWeight (fun k => (pathWeight 3 k : ℂ)) d) t =
      (-(((Real.sin (t / Real.sqrt 2)) ^ 2 : ℝ) : ℂ)) ^ d := by
  rw [path_power_amplitude, pathSpectralAmplitude_three]

theorem onelink_hypercube_constant_time (d : ℕ) :
    ‖spectralAmplitude (powerEigenvalue (pathEigenvalue 2) d)
        (powerWeight (fun k => (pathWeight 2 k : ℂ)) d) (Real.pi / 2)‖ = 1 := by
  rw [onelink_hypercube_transfer, Real.sin_pi_div_two]
  simp

theorem twolink_hypercube_constant_time (d : ℕ) :
    ‖spectralAmplitude (powerEigenvalue (pathEigenvalue 3) d)
        (powerWeight (fun k => (pathWeight 3 k : ℂ)) d)
        (Real.pi / Real.sqrt 2)‖ = 1 := by
  rw [twolink_hypercube_transfer]
  have ht : Real.pi / Real.sqrt 2 / Real.sqrt 2 = Real.pi / 2 := by
    rw [div_div, Real.mul_self_sqrt (by norm_num)]
  rw [ht, Real.sin_pi_div_two]
  simp

theorem onelink_hypercube_perfect (d : ℕ) :
    SpectralPerfectTransfer (powerEigenvalue (pathEigenvalue 2) d)
      (powerWeight (fun k => (pathWeight 2 k : ℂ)) d) := by
  exact ⟨Real.pi / 2, by positivity, onelink_hypercube_constant_time d⟩

theorem twolink_hypercube_perfect (d : ℕ) :
    SpectralPerfectTransfer (powerEigenvalue (pathEigenvalue 3) d)
      (powerWeight (fun k => (pathWeight 3 k : ℂ)) d) := by
  exact ⟨Real.pi / Real.sqrt 2, by positivity, twolink_hypercube_constant_time d⟩

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
