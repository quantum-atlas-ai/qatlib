/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

open Matrix
open scoped Real

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs

noncomputable def sinEnvelopeState (M : ℕ) : QState (Fin M) :=
  fun τ =>
    (Real.sqrt (2 / (M : ℝ)) : ℂ) *
      (Real.sin (Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ)) : ℂ)

noncomputable def sinEnvelopeKernel (M : ℕ) (φ : ℝ) (z : Fin M) : ℂ :=
  ApplyGate (QFTMatrix M)ᴴ
      (fun τ => Complex.exp (2 * Real.pi * Complex.I * ((τ.val : ℝ) * φ)) *
        sinEnvelopeState M τ) z

noncomputable def sinEnvelopeDelta (M : ℕ) (φ : ℝ) (z : Fin M) : ℝ :=
  2 * Real.pi * ((M : ℝ) * φ - (z.val : ℝ))

noncomputable def sinEnvelopeGeoSum (M : ℕ) (w : ℝ) : ℂ :=
  (1 - Complex.exp (Complex.I * w)) / (1 - Complex.exp (Complex.I * w / (M : ℝ)))
end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs

set_option autoImplicit false

open Matrix
open scoped Real
namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec

noncomputable def sinEnvelopeFilterF (d θ : ℝ) : ℝ :=
  if 2 * d ≤ θ then d / θ
  else if d ≤ θ then (1 / 2) * Real.sin (Real.pi / 2 * (θ - d) / d) else 0

noncomputable def sinEnvelopeFilterG (d θ : ℝ) : ℝ :=
  if 2 * d ≤ θ then 0
  else if d ≤ θ then (1 / 2) * Real.cos (Real.pi / 2 * (θ - d) / d) else 1 / 2

noncomputable def sinEnvelopeHVector (d θ : ℝ) : QState (Fin 3) :=
  fun s =>
    if s = 0 then
      (Real.sqrt (1 - sinEnvelopeFilterF d θ ^ 2 - sinEnvelopeFilterG d θ ^ 2) : ℂ)
    else if s = 1 then (sinEnvelopeFilterF d θ : ℂ) else (sinEnvelopeFilterG d θ : ℂ)
end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
