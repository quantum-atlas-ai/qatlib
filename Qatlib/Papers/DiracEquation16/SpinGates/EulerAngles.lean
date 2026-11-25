/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Qatlib.Foundations.MatrixAlgebra.CliffordWalk.Euler

@[expose] public section

/-!
# Euler angles of the local rotation `QA`

Eqs. (60)-(64) of [FillionGourdeauMacLeanLaflamme2017] express the local operator
`QA = exp (-i dt (A · σ))` in the canonical `SU(2)` form and give the Euler data
`δ`, `ξ`, `θ` of the decomposition `QA = Rz(δ) Ry(θ) Rz(ξ)` of Eq. (61). This module records that
data for the finite register: the modulus `|A|` of Eq. (60), the azimuth
`arctan (Ax / Ay)` shared by Eqs. (62)-(63), and the half-sum `arctan ((Az/|A|) tan (|A| dt))`
determined by the same two equations.

## Main statements

* `xi_add_delta`: `ξ + δ = 2 arctan ((Az/|A|) tan (|A| dt))`.
* `xi_sub_delta`: `ξ - δ = 2 arctan (Ax / Ay)`.
* `half_xi_add_delta`: `(ξ + δ) / 2` is the half-sum.
* `tan_halfSum`: the half-sum has the tangent `(Az/|A|) tan (|A| dt)`.
* `cos_halfSum_pos`: the angle `(ξ + δ) / 2` has positive cosine, so the cosine guard of the
  decomposition is automatic.
* `cos_theta_div_two`: the half-angle `θ / 2` has cosine `cos(|A| dt) / cos((ξ + δ)/2)`.

The matrix identity `rotation (A · σ) dt = rotation σz (δ/2) * rotation σy (θ/2) * rotation σz
(ξ/2)` is **not** established here. Two branches are missing: the principal-value prescription of
Eqs. (62)-(64) is only correct for `Ay > 0` and `sin (|A| dt) > 0`, so the literal target needs
those extra branch hypotheses; and the four scalar relations that match the matrix entries are not
yet assembled into the `2 × 2` comparison.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DiracEquation16.SpinGates

open Qatlib.Foundations.MatrixAlgebra.CliffordWalk

/-- The modulus `|A(t)|` of the vector potential, Eq. (60) of
[FillionGourdeauMacLeanLaflamme2017]. -/
def Aabs (Ax Ay Az : ℝ) : ℝ := Real.sqrt (Ax ^ 2 + Ay ^ 2 + Az ^ 2)

/-- The modulus is nonnegative. -/
theorem Aabs_nonneg (Ax Ay Az : ℝ) : 0 ≤ Aabs Ax Ay Az := Real.sqrt_nonneg _

/-- A nonvanishing vector potential has positive modulus. -/
theorem Aabs_pos {Ax Ay Az : ℝ} (h : Ax ≠ 0 ∨ Ay ≠ 0 ∨ Az ≠ 0) : 0 < Aabs Ax Ay Az := by
  have hs : 0 < Ax ^ 2 + Ay ^ 2 + Az ^ 2 := by
    rcases h with h | h | h
    · nlinarith [mul_self_pos.mpr h, sq_nonneg Ay, sq_nonneg Az]
    · nlinarith [mul_self_pos.mpr h, sq_nonneg Ax, sq_nonneg Az]
    · nlinarith [mul_self_pos.mpr h, sq_nonneg Ax, sq_nonneg Ay]
  simpa [Aabs] using Real.sqrt_pos.2 hs

/-- The squared modulus is the squared norm of the vector potential. -/
theorem Aabs_sq (Ax Ay Az : ℝ) : Aabs Ax Ay Az ^ 2 = Ax ^ 2 + Ay ^ 2 + Az ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The azimuth `arctan (Ax / Ay)` appearing in Eqs. (62)-(63). -/
def azimuth (Ax Ay : ℝ) : ℝ := Real.arctan (Ax / Ay)

/-- The common half-sum `arctan ((Az/|A|) tan (|A| dt))` of Eqs. (62)-(63). -/
def halfSum (Ax Ay Az dt : ℝ) : ℝ :=
  Real.arctan (Az / Aabs Ax Ay Az * Real.tan (Aabs Ax Ay Az * dt))

/-- The Euler angle `δ` of Eq. (62). -/
def delta (Ax Ay Az dt : ℝ) : ℝ := halfSum Ax Ay Az dt - azimuth Ax Ay

/-- The Euler angle `ξ` of Eq. (63). -/
def xi (Ax Ay Az dt : ℝ) : ℝ := halfSum Ax Ay Az dt + azimuth Ax Ay

/-- The Euler angle `θ` of Eq. (64). -/
def theta (Ax Ay Az dt : ℝ) : ℝ :=
  2 * Real.arccos (Real.cos (Aabs Ax Ay Az * dt) /
    Real.cos ((xi Ax Ay Az dt + delta Ax Ay Az dt) / 2))

/-- The two azimuthal angles add up to twice the half-sum. -/
theorem xi_add_delta (Ax Ay Az dt : ℝ) :
    xi Ax Ay Az dt + delta Ax Ay Az dt = 2 * halfSum Ax Ay Az dt := by
  unfold xi delta
  ring

/-- The two azimuthal angles differ by twice the azimuth. -/
theorem xi_sub_delta (Ax Ay Az dt : ℝ) :
    xi Ax Ay Az dt - delta Ax Ay Az dt = 2 * azimuth Ax Ay := by
  unfold xi delta
  ring

/-- Half the sum of the azimuthal angles is the half-sum itself. -/
theorem half_xi_add_delta (Ax Ay Az dt : ℝ) :
    (xi Ax Ay Az dt + delta Ax Ay Az dt) / 2 = halfSum Ax Ay Az dt := by
  rw [xi_add_delta]
  ring

/-- The half-sum has the tangent prescribed by Eqs. (62)-(63). -/
theorem tan_halfSum (Ax Ay Az dt : ℝ) :
    Real.tan (halfSum Ax Ay Az dt) =
      Az / Aabs Ax Ay Az * Real.tan (Aabs Ax Ay Az * dt) := by
  unfold halfSum
  exact Real.tan_arctan _

/-- The cosine of the half-sum is positive, so the half-sum is never a pole of the tangent. -/
theorem cos_halfSum_pos (Ax Ay Az dt : ℝ) : 0 < Real.cos (halfSum Ax Ay Az dt) := by
  unfold halfSum
  exact Real.cos_arctan_pos _

/-- The cosine of the half-sum does not vanish, which discharges the cosine guard of the
decomposition. -/
theorem cos_halfSum_ne_zero (Ax Ay Az dt : ℝ) : Real.cos (halfSum Ax Ay Az dt) ≠ 0 :=
  (cos_halfSum_pos Ax Ay Az dt).ne'

/-- The half-angle `θ / 2` has the cosine prescribed by Eq. (64), whenever the principal argument
of the arccosine lies in its range. -/
theorem cos_theta_div_two (Ax Ay Az dt : ℝ)
    (h : -(1 : ℝ) ≤ Real.cos (Aabs Ax Ay Az * dt) / Real.cos (halfSum Ax Ay Az dt) ∧
      Real.cos (Aabs Ax Ay Az * dt) / Real.cos (halfSum Ax Ay Az dt) ≤ 1) :
    Real.cos (theta Ax Ay Az dt / 2) =
      Real.cos (Aabs Ax Ay Az * dt) / Real.cos (halfSum Ax Ay Az dt) := by
  unfold theta
  rw [half_xi_add_delta]
  rw [show (2 * Real.arccos (Real.cos (Aabs Ax Ay Az * dt) / Real.cos (halfSum Ax Ay Az dt))) / 2
      = Real.arccos (Real.cos (Aabs Ax Ay Az * dt) / Real.cos (halfSum Ax Ay Az dt)) by ring]
  exact Real.cos_arccos h.1 h.2

end Qatlib.Papers.DiracEquation16.SpinGates

end
