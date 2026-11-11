/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# OrszagMcLaughlin — a real quadratic Orszag--McLaughlin local model

Leyton--Osborne, *A quantum algorithm to solve nonlinear differential equations*,
fixed arXiv:0812.4423v1.

Source location: §5 (worked example, equation (25)).

The paper's worked example is the periodic lattice quadratic system

  `x′_j = x_{j+1} x_{j+2} + x_{j−1} x_{j−2} − 2 x_{j+1} x_{j−1}`,

whose energy `∑_j x_j²` is preserved by index cancellation.  This module
formalises a *local three-variable* instance of that real quadratic family,

  `ẋ = y z,   ẏ = x z,   ż = -2 x y`,

with the Euclidean energy `x² + y² + z²`.  It records the vector field, the
energy, the gradient, and the exact algebraic identity

  `2x (yz) + 2y (xz) + 2z (-2xy) = 0`

that is the pointwise content of conservation (`∇E · F = 0`).  The periodic
lattice form of (25) and its index cancellation are *not* formalised here; this
is the three-variable local model, marked `provenance_uncertain` in the claim
metadata.  Numerical Euler error and state normalisation are controlled
separately in the `QuantumEuler` block.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonlinODE08.RealQuadratic

/-- The Orszag--McLaughlin vector field `(x,y,z) ↦ (yz, xz, -2xy)`: a degree-two
polynomial map on real coordinates. -/
def omField (x y z : ℝ) : ℝ × ℝ × ℝ := (y * z, x * z, -2 * x * y)

/-- The Euclidean energy `x² + y² + z²`, the conserved squared norm. -/
def omEnergy (x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 + z ^ 2

/-- The energy gradient `(2x, 2y, 2z)`. -/
def omGradient (x y z : ℝ) : ℝ × ℝ × ℝ := (2 * x, 2 * y, 2 * z)

/-- Conservation at the level of the directional derivative: the gradient of the
energy is orthogonal to the vector field everywhere, so the energy is constant
along every trajectory. -/
theorem om_energy_directional_derivative_zero (x y z : ℝ) :
    (2 * x) * (y * z) + (2 * y) * (x * z) + (2 * z) * (-2 * x * y) = 0 := by
  ring

/-- The same conservation identity written with the vector-field and gradient
components: `∇E · F = 0`. -/
theorem om_gradient_dot_field_zero (x y z : ℝ) :
    (omGradient x y z).1 * (omField x y z).1
      + (omGradient x y z).2.1 * (omField x y z).2.1
      + (omGradient x y z).2.2 * (omField x y z).2.2 = 0 := by
  unfold omGradient omField
  ring

/-- The energy is a sum of squares, hence nonnegative. -/
theorem omEnergy_nonneg (x y z : ℝ) : 0 ≤ omEnergy x y z := by
  unfold omEnergy
  exact add_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y)) (sq_nonneg z)

end Qatlib.Papers.NonlinODE08.RealQuadratic
