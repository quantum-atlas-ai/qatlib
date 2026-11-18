/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.VanishCharge.ClebschAlgebra
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The polar current in the Madelung representation

[Kedia2018SuperfluidHelicity], Section II,
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
A real amplitude and unit complex phase determine a wavefunction. The product
rule yields its directional derivative and the imaginary current is amplitude
squared times the phase rate. Division by density requires nonzero amplitude.
This is a local calculation away from vortex cores, not a derivation of the
Gross–Pitaevskii PDE or a global phase-lift existence theorem.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.Madelung

/-- The directional probability current before its mass and Planck normalizations. -/
def polarCurrent (amplitude amplitudeRate phaseRate : ℝ) (phase : ℂ) : ℝ :=
  (star ((amplitude : ℂ) * phase) *
    (((amplitudeRate : ℂ) + Complex.I * (amplitude * phaseRate : ℝ)) * phase)).im

/-- The polar current depends on the phase rate, while the amplitude derivative cancels. -/
theorem polar_current_formula (amplitude amplitudeRate phaseRate : ℝ) (phase : ℂ)
    (hphase : Complex.normSq phase = 1) :
    polarCurrent amplitude amplitudeRate phaseRate phase = amplitude ^ 2 * phaseRate := by
  have hp : phase.re * phase.re + phase.im * phase.im = 1 := by
    simpa only [Complex.normSq_apply] using hphase
  simp [polarCurrent, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  linear_combination (amplitude ^ 2 * phaseRate) * hp

/-- Away from a density zero, division by squared amplitude recovers the phase rate. -/
theorem normalized_polar_current (amplitude amplitudeRate phaseRate : ℝ) (phase : ℂ)
    (ha : amplitude ≠ 0) (hphase : Complex.normSq phase = 1) :
    polarCurrent amplitude amplitudeRate phaseRate phase / amplitude ^ 2 = phaseRate := by
  rw [polar_current_formula amplitude amplitudeRate phaseRate phase hphase]
  field_simp

/-- The ordinary product rule supplies the polar derivative along each differentiable coordinate curve. -/
theorem polar_wave_derivative (amplitude : ℝ → ℝ) (phase : ℝ → ℂ)
    (amplitudeRate phaseRate t : ℝ)
    (ha : HasDerivAt amplitude amplitudeRate t)
    (hp : HasDerivAt phase (Complex.I * (phaseRate : ℂ) * phase t) t) :
    HasDerivAt (fun s => (amplitude s : ℂ) * phase s)
      (((amplitudeRate : ℂ) + Complex.I * (amplitude t * phaseRate : ℝ)) * phase t) t := by
  exact (HasDerivAt.fun_mul ha.ofReal_comp hp).congr_deriv (by push_cast; ring)

end Qatlib.Papers.SuperfluidHel18.Madelung
