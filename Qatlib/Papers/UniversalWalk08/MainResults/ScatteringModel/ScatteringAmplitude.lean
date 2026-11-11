/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Scattering amplitudes of arXiv:0806.1972

Paper: A. M. Childs, *Universal computation by quantum walk*,
arXiv:0806.1972v1 (12 June 2008), Sec. II and Sec. VII.

For a graph obtained by attaching semi-infinite lines to a finite graph, the
propagator decomposes into a sum over scattering states and bound states
(Eq. (7)).  For large distances `x, y`, the stationary-phase evaluation of the
scattering-state integral gives Eq. (11); in the universal-computer
construction the input is the single vertex at distance `x` on the input wire
and the output is the vertex `0` on the output wire, which yields Eq. (40):

`⟨0, s_out| e^{-iHt} |x, 0_in⟩ ≈ ∫_{-π}^{0} e^{ikx - 2it cos k}
   T_{0_in, s_out}(k) dk/(2π)`.

This module records the right-hand side of Eq. (40) as
`scatteringAmplitude`, with `T` the transmission coefficients, so that the
paper's Sec. VII statement can refer to the same object as the paper.
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.ScatteringModel



set_option autoImplicit false

/-- The oscillatory phase `e^{ikx - 2it cos k}` of Eq. (40).

Paper: arXiv:0806.1972v1, Sec. VII, Eq. (40); compare Eq. (7). -/
noncomputable def scatteringPhase (k x t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((k : ℂ) * (x : ℂ)) -
    2 * Complex.I * (t : ℂ) * (Real.cos k : ℂ))

/-- The stationary-phase amplitude of Eq. (40):
`(1/(2π)) ∫_{-π}^{0} e^{ikx - 2it cos k} T_s(k) dk`.

`T s` is the transmission coefficient `T_{0_in, s_out}(·)` from the input
wire to output wire `s`.  Paper: arXiv:0806.1972v1, Sec. VII, Eq. (40) (which
uses Eq. (7) and Eq. (11)). -/
noncomputable def scatteringAmplitude {n : ℕ} (T : Fin (2 ^ n) → ℝ → ℂ)
    (x t : ℝ) (s : Fin (2 ^ n)) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ k in (-Real.pi)..0, scatteringPhase k x t * T s k

/-- The phase at the origin of the wire and at time zero is one. -/
@[simp]
theorem scatteringPhase_zero_zero (k : ℝ) : scatteringPhase k 0 0 = 1 := by
  simp [scatteringPhase]

/-- Zero transmission coefficients give the zero amplitude. -/
@[simp]
theorem scatteringAmplitude_zero {n : ℕ} (x t : ℝ) (s : Fin (2 ^ n)) :
    scatteringAmplitude (n := n) (fun _ _ => 0) x t s = 0 := by
  simp [scatteringAmplitude]

end Qatlib.Papers.UniversalWalk08.MainResults.ScatteringModel
