/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullUnitaryTransport

@[expose] public section


/-! Finite real-time phases and their exact Gram-adjoint identity.
The identity is algebraic and does not assert a continuous generator representation.
-/

namespace Qatlib.Concepts.GibbsSource.SourceForms

/-- Real-time phase of a Bohr component of frequency `ν`. -/
noncomputable def bohrPhase (ν t : ℝ) : ℂ :=
  Complex.exp ((ν * t : ℝ) * Complex.I)

/-- Taking the Gram adjoint changes the sign of the first frequency. -/
theorem bohrPhase_star_mul (ν μ t : ℝ) :
    star (bohrPhase ν t) * bohrPhase μ t = bohrPhase (μ - ν) t := by
  simp only [bohrPhase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Qatlib.Concepts.GibbsSource.SourceForms
