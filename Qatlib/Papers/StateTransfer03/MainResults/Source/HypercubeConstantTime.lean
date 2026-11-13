/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Source.CartesianPropagator
import Qatlib.Papers.StateTransfer03.MainResults.Source.PairChainTransfer

/-!
# Constant-time transfer in hypercube spectral models

The spectral amplitudes of Cartesian powers of the two- and three-vertex paths are powers of
their single-coordinate amplitudes. `onelink_hypercube_constant_time` and
`twolink_hypercube_constant_time` establish norm-one transfer at times independent of the
dimension. See [ChristandlEtAl2004].

## Main statements

* `onelink_hypercube_transfer`: the one-link amplitude is `(-i sin t) ^ d`.
* `twolink_hypercube_constant_time`: the two-link amplitude has norm one at `π / sqrt 2`.
* `onelink_hypercube_perfect`: every one-link Cartesian power has spectral perfect transfer.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

/-- The spectral amplitude of the `d`-fold Cartesian power of the two-vertex path is `(-i sin t)
^ d`. See [ChristandlEtAl2004]. -/
theorem onelink_hypercube_transfer (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue (pathEigenvalue 2) d)
        (powerWeight (fun k => (pathWeight 2 k : ℂ)) d) t =
      (-Complex.I * (Real.sin t : ℂ)) ^ d := by
  rw [path_power_amplitude, pathSpectralAmplitude_two]

/-- The spectral amplitude of the `d`-fold Cartesian power of the three-vertex path is `(-sin²
(t / sqrt 2)) ^ d`. See [ChristandlEtAl2004]. -/
theorem twolink_hypercube_transfer (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue (pathEigenvalue 3) d)
        (powerWeight (fun k => (pathWeight 3 k : ℂ)) d) t =
      (-(((Real.sin (t / Real.sqrt 2)) ^ 2 : ℝ) : ℂ)) ^ d := by
  rw [path_power_amplitude, pathSpectralAmplitude_three]

/-- In every dimension, the one-link hypercube spectral amplitude has norm one at time `π / 2`.
See [ChristandlEtAl2004]. -/
theorem onelink_hypercube_constant_time (d : ℕ) :
    ‖spectralAmplitude (powerEigenvalue (pathEigenvalue 2) d)
        (powerWeight (fun k => (pathWeight 2 k : ℂ)) d) (Real.pi / 2)‖ = 1 := by
  rw [onelink_hypercube_transfer, Real.sin_pi_div_two]
  simp

/-- In every dimension, the two-link hypercube spectral amplitude has norm one at time `π / sqrt
2`. See [ChristandlEtAl2004]. -/
theorem twolink_hypercube_constant_time (d : ℕ) :
    ‖spectralAmplitude (powerEigenvalue (pathEigenvalue 3) d)
        (powerWeight (fun k => (pathWeight 3 k : ℂ)) d)
        (Real.pi / Real.sqrt 2)‖ = 1 := by
  rw [twolink_hypercube_transfer]
  have ht : Real.pi / Real.sqrt 2 / Real.sqrt 2 = Real.pi / 2 := by
    rw [div_div, Real.mul_self_sqrt (by norm_num)]
  rw [ht, Real.sin_pi_div_two]
  simp

/-- Every Cartesian power of the two-vertex path possesses spectral perfect transfer. See
[ChristandlEtAl2004]. -/
theorem onelink_hypercube_perfect (d : ℕ) :
    SpectralPerfectTransfer (powerEigenvalue (pathEigenvalue 2) d)
      (powerWeight (fun k => (pathWeight 2 k : ℂ)) d) := by
  exact ⟨Real.pi / 2, by positivity, onelink_hypercube_constant_time d⟩

/-- Every Cartesian power of the three-vertex path possesses spectral perfect transfer. See
[ChristandlEtAl2004]. -/
theorem twolink_hypercube_perfect (d : ℕ) :
    SpectralPerfectTransfer (powerEigenvalue (pathEigenvalue 3) d)
      (powerWeight (fun k => (pathWeight 3 k : ℂ)) d) := by
  exact ⟨Real.pi / Real.sqrt 2, by positivity, twolink_hypercube_constant_time d⟩

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
