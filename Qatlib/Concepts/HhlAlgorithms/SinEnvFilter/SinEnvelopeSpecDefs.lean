/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# Sine-envelope kernel and three-state filter definitions

`sinEnvelopeState` defines the half-step sine amplitudes, and `sinEnvelopeKernel` applies
inverse QFT to their phase modulation. `sinEnvelopeDelta` and `sinEnvelopeGeoSum` supply the
scaled discrepancy and geometric quotient used in the phase-estimation analysis of
[HarrowHassidimLloyd2009].

`sinEnvelopeFilterF`, `sinEnvelopeFilterG`, and `sinEnvelopeHVector` define the reciprocal and
transition amplitudes and their three-state embedding.

## Main statements

* `sinEnvelopeKernel`: the sine-envelope phase-estimation amplitude.
* `sinEnvelopeFilterF`: the well-conditioned reciprocal filter with a sine transition.
* `sinEnvelopeHVector`: the residual, well-conditioned, and ill-conditioned amplitudes.

## References

* [Harrow et al., 2009, Appendix A][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

open Matrix
open scoped Real

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs

/-- The sine-envelope vector with amplitudes `sqrt (2 / M) * sin (π * (τ + 1 / 2) / M)`. -/
noncomputable def sinEnvelopeState (M : ℕ) : QState (Fin M) :=
  fun τ =>
    (Real.sqrt (2 / (M : ℝ)) : ℂ) *
      (Real.sin (Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ)) : ℂ)

/-- The phase-estimation kernel obtained by applying inverse QFT to the phase-modulated
sine-envelope vector. -/
noncomputable def sinEnvelopeKernel (M : ℕ) (φ : ℝ) (z : Fin M) : ℂ :=
  ApplyGate (QFTMatrix M)ᴴ
      (fun τ => Complex.exp (2 * Real.pi * Complex.I * ((τ.val : ℝ) * φ)) *
        sinEnvelopeState M τ) z

/-- The scaled phase discrepancy `2 * π * (M * φ - z)`. -/
noncomputable def sinEnvelopeDelta (M : ℕ) (φ : ℝ) (z : Fin M) : ℝ :=
  2 * Real.pi * ((M : ℝ) * φ - (z.val : ℝ))

/-- The geometric-sum quotient `(1 - exp (I * w)) / (1 - exp (I * w / M))`. -/
noncomputable def sinEnvelopeGeoSum (M : ℕ) (w : ℝ) : ℂ :=
  (1 - Complex.exp (Complex.I * w)) / (1 - Complex.exp (Complex.I * w / (M : ℝ)))
end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs

set_option autoImplicit false

open Matrix
open scoped Real
namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec

/-- The well-conditioned filter amplitude: reciprocal above `2 * d`, a sine transition between
`d` and `2 * d`, and zero below `d`. -/
noncomputable def sinEnvelopeFilterF (d θ : ℝ) : ℝ :=
  if 2 * d ≤ θ then d / θ
  else if d ≤ θ then (1 / 2) * Real.sin (Real.pi / 2 * (θ - d) / d) else 0

/-- The ill-conditioned filter amplitude: zero above `2 * d`, a cosine transition between `d`
and `2 * d`, and `1 / 2` below `d`. -/
noncomputable def sinEnvelopeFilterG (d θ : ℝ) : ℝ :=
  if 2 * d ≤ θ then 0
  else if d ≤ θ then (1 / 2) * Real.cos (Real.pi / 2 * (θ - d) / d) else 1 / 2

/-- The three-state filter vector with selected amplitudes `sinEnvelopeFilterF` and
`sinEnvelopeFilterG` and residual amplitude given by their complementary square root. -/
noncomputable def sinEnvelopeHVector (d θ : ℝ) : QState (Fin 3) :=
  fun s =>
    if s = 0 then
      (Real.sqrt (1 - sinEnvelopeFilterF d θ ^ 2 - sinEnvelopeFilterG d θ ^ 2) : ℂ)
    else if s = 1 then (sinEnvelopeFilterF d θ : ℂ) else (sinEnvelopeFilterG d θ : ℂ)
end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
