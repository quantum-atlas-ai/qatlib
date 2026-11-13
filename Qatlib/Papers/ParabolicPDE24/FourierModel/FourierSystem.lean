/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.TelegraphLimit.TelegraphMode

/-!
# Explicit Fourier signal and flux

`signal` and `flux` turn the scalar relaxation mode into complex Fourier amplitudes. Their
derivatives satisfy the coupled signal-flux system with initial data `(amp, 0)` under the stated
parameter assumptions, providing the explicit Fourier solution used for [JinLiu2024].

## Main statements

* `signal_hasDerivAt`: the specified signal derivative is the actual time derivative.
* `source_fourier_system`: the amplitudes satisfy the source Fourier equations and initial
  conditions.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Papers.ParabolicPDE24.FourierDefs
open Qatlib.Foundations.TimeEvolution.TelegraphLimit

/-- The Fourier signal amplitude obtained by multiplying `amp` by `mode (k * ε²) (k * ω²) t`. -/
def signal (k ε ω : ℝ) (amp : ℂ) (t : ℝ) : ℂ := (mode (k*ε^2) (k*ω^2) t:ℝ)*amp

/-- The Fourier flux amplitude `i * ε / ω` times `modeDeriv (k * ε²) (k * ω²) t` times `amp`. -/
def flux (k ε ω : ℝ) (amp : ℂ) (t : ℝ) : ℂ :=
  Complex.I*(ε:ℂ)/(ω:ℂ)*(modeDeriv (k*ε^2) (k*ω^2) t:ℝ)*amp

/-- The specified time derivative of the Fourier signal, given by the scalar mode derivative
times `amp`. -/
def signalDeriv (k ε ω : ℝ) (amp : ℂ) (t : ℝ) : ℂ :=
  (modeDeriv (k*ε^2) (k*ω^2) t:ℝ)*amp

/-- The specified time derivative of the Fourier flux, given by `i * ε / ω` times the second
scalar mode derivative times `amp`. -/
def fluxDeriv (k ε ω : ℝ) (amp : ℂ) (t : ℝ) : ℂ :=
  Complex.I*(ε:ℂ)/(ω:ℂ)*(modeDeriv2 (k*ε^2) (k*ω^2) t:ℝ)*amp

/-- The Fourier signal has derivative `signalDeriv` at every real time. See [JinLiu2024]. -/
theorem signal_hasDerivAt (k ε ω : ℝ) (amp : ℂ) (t : ℝ) :
    HasDerivAt (signal k ε ω amp) (signalDeriv k ε ω amp t) t :=
  (mode_hasDerivAt _ _ _).ofReal_comp.mul_const amp

/-- The Fourier flux has derivative `fluxDeriv` at every real time. See [JinLiu2024]. -/
theorem flux_hasDerivAt (k ε ω : ℝ) (amp : ℂ) (t : ℝ) :
    HasDerivAt (flux k ε ω amp) (fluxDeriv k ε ω amp t) t :=
  ((modeDeriv_hasDerivAt _ _ _).ofReal_comp.const_mul _).mul_const amp

/-- For positive `k` and `ε`, nonzero `ω`, and the stated mode bound, signal and flux satisfy
the coupled Fourier transport-relaxation equations and start at `amp` and zero,
respectively. See [JinLiu2024]. -/
theorem source_fourier_system {k ε ω : ℝ} (hk : 0<k) (hε : 0<ε) (hω : ω≠0)
    (hm : 4*(k*ε^2)*(k*ω^2)≤3/4) (amp : ℂ) (t : ℝ) :
    signalDeriv k ε ω amp t= -(ε:ℂ)⁻¹*(Complex.I*(ω:ℂ))*flux k ε ω amp t ∧
    fluxDeriv k ε ω amp t= -(ε:ℂ)⁻¹*(Complex.I*(ω:ℂ))*signal k ε ω amp t-
      ((k*ε^2:ℝ):ℂ)⁻¹*flux k ε ω amp t ∧
    signal k ε ω amp 0=amp ∧ flux k ε ω amp 0=0 := by
  obtain ⟨heq,hinit,hzero⟩ := mode_solves (by positivity : 0<k*ε^2) (by positivity : 0≤k*ω^2) hm t
  have hz0 := (mode_solves (by positivity : 0<k*ε^2) (by positivity : 0≤k*ω^2) hm 0).2
  have hεc : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hωc : (ω:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hω
  have hkc : (k:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have heqc : ((k*ε^2:ℝ):ℂ)*(modeDeriv2 (k*ε^2) (k*ω^2) t:ℝ)+
      (modeDeriv (k*ε^2) (k*ω^2) t:ℝ)+((k*ω^2:ℝ):ℂ)*(mode (k*ε^2) (k*ω^2) t:ℝ)=0 := by
    exact_mod_cast heq
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [signalDeriv,flux]
    field_simp
    simp [Complex.I_sq]
  · dsimp [fluxDeriv,signal,flux]
    push_cast at heqc ⊢
    field_simp
    linear_combination amp*heqc
  · simp [signal,hz0.1]
  · simp [flux,hz0.2]
end Qatlib.Papers.ParabolicPDE24.FourierDefs
