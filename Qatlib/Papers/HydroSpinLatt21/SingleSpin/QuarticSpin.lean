/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# A normalized single-spin symmetry-breaking potential

[Saenz2021HydroSpinLattices], Methods, describes Rayleigh self-propulsion with
oppositely rotating states. See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

We study the exact scalar normal form `x' = a x - x^3` and its even quartic
potential. The stationary points, their parameter dependence, and the global
minimizers are derived explicitly. This is a reduced mathematical model: it
does not derive the measured walking threshold, orbital-radius response,
three-lobed instability, or spin-flip time from the full droplet-wave dynamics.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.SingleSpin

/-- The even quartic potential for a normalized scalar active spin. -/
def spinPotential (a x : ℝ) : ℝ := x ^ 4 / 4 - a * x ^ 2 / 2

/-- The negative potential gradient, normalized to unit cubic coefficient. -/
def spinDrift (a x : ℝ) : ℝ := a * x - x ^ 3

/-- The uncoupled Rayleigh angular-velocity drift with relaxation time `tau`
and preferred speed `omega`. -/
def rayleighDrift (tau omega x : ℝ) : ℝ :=
  (1 / tau) * (1 - x ^ 2 / omega ^ 2) * x

/-- The paper's Rayleigh term is exactly a rescaling of the cubic
normal form when its relaxation time and preferred speed are nonzero. -/
theorem rayleigh_drift_normalization (tau omega x : ℝ)
    (htau : tau ≠ 0) (homega : omega ≠ 0) :
    rayleighDrift tau omega x = spinDrift (omega ^ 2) x / (tau * omega ^ 2) := by
  unfold rayleighDrift spinDrift
  field_simp [htau, homega]

/-- Reflecting the spin leaves the scalar potential invariant. -/
theorem spin_potential_even (a x : ℝ) : spinPotential a (-x) = spinPotential a x := by
  unfold spinPotential
  ring

/-- The scalar drift is odd, expressing the two orientations' symmetry. -/
theorem spin_drift_odd (a x : ℝ) : spinDrift a (-x) = -spinDrift a x := by
  unfold spinDrift
  ring

/-- The polynomial potential has derivative equal to minus the spin drift. -/
theorem spin_potential_has_deriv_at (a x : ℝ) :
    HasDerivAt (spinPotential a) (-spinDrift a x) x := by
  change HasDerivAt (fun y : ℝ => y ^ 4 / 4 - a * y ^ 2 / 2) (-spinDrift a x) x
  apply HasDerivAt.congr_deriv
    (HasDerivAt.sub (((hasDerivAt_id x).pow 4).div_const 4)
      ((((hasDerivAt_id x).pow 2).const_mul a).div_const 2))
  dsimp [spinDrift]
  ring

/-- Factoring the cubic gives the exact stationary-point condition. -/
theorem stationary_iff (a x : ℝ) : spinDrift a x = 0 ↔ x = 0 ∨ x ^ 2 = a := by
  have hfactor : spinDrift a x = x * (a - x ^ 2) := by
    unfold spinDrift
    ring
  rw [hfactor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

/-- At and below the bifurcation parameter, zero is the only stationary spin. -/
theorem stationary_nonpos_iff {a : ℝ} (ha : a ≤ 0) (x : ℝ) :
    spinDrift a x = 0 ↔ x = 0 := by
  rw [stationary_iff]
  constructor
  · rintro (h | h)
    · exact h
    · nlinarith [sq_nonneg x]
  · exact Or.inl

/-- Above the bifurcation parameter the stationary spins are exactly zero and
the two square-root branches. -/
theorem stationary_pos_iff {a : ℝ} (ha : 0 < a) (x : ℝ) :
    spinDrift a x = 0 ↔ x = 0 ∨ x = Real.sqrt a ∨ x = -Real.sqrt a := by
  rw [stationary_iff]
  have hsqrt := Real.sq_sqrt ha.le
  have heq : x ^ 2 = a ↔ x = Real.sqrt a ∨ x = -Real.sqrt a := by
    constructor
    · intro h
      exact sq_eq_sq_iff_eq_or_eq_neg.1 (h.trans hsqrt.symm)
    · rintro (rfl | rfl) <;> simpa using hsqrt
  rw [heq]

/-- The uncoupled physical Rayleigh drift has exactly the zero state and the
two preferred angular velocities as fixed points. -/
theorem rayleigh_stationary_iff (tau omega x : ℝ)
    (htau : tau ≠ 0) (homega : omega ≠ 0) :
    rayleighDrift tau omega x = 0 ↔ x = 0 ∨ x = omega ∨ x = -omega := by
  rw [rayleigh_drift_normalization tau omega x htau homega,
    div_eq_zero_iff, or_iff_left (mul_ne_zero htau (pow_ne_zero _ homega)), stationary_iff,
    sq_eq_sq_iff_eq_or_eq_neg]

/-- Completing the square isolates the global-minimum defect. -/
theorem potential_square_completion (a x : ℝ) :
    spinPotential a x = (x ^ 2 - a) ^ 2 / 4 - a ^ 2 / 4 := by
  unfold spinPotential
  ring

/-- The broken-symmetry energy bound holds for every real spin. -/
theorem potential_lower_bound (a x : ℝ) : -a ^ 2 / 4 ≤ spinPotential a x := by
  rw [potential_square_completion]
  nlinarith [sq_nonneg (x ^ 2 - a)]

/-- Saturating the energy bound is equivalent to lying on a square-root branch. -/
theorem potential_eq_lower_bound_iff (a x : ℝ) :
    spinPotential a x = -a ^ 2 / 4 ↔ x ^ 2 = a := by
  rw [potential_square_completion]
  constructor <;> intro h
  · nlinarith [sq_nonneg (x ^ 2 - a)]
  · rw [h]
    ring

/-- For positive parameter, the two square-root branches are precisely all
global minimizers; the central stationary point has strictly higher energy. -/
theorem global_minimizers_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∀ y : ℝ, spinPotential a x ≤ spinPotential a y) ↔
      x = Real.sqrt a ∨ x = -Real.sqrt a := by
  have hsqrt := Real.sq_sqrt ha.le
  have hmin : spinPotential a (Real.sqrt a) = -a ^ 2 / 4 :=
    (potential_eq_lower_bound_iff a _).2 hsqrt
  constructor
  · intro h
    have heq : spinPotential a x = -a ^ 2 / 4 :=
      le_antisymm (by simpa [hmin] using h (Real.sqrt a)) (potential_lower_bound a x)
    have hx := (potential_eq_lower_bound_iff a x).1 heq
    exact (sq_eq_sq_iff_eq_or_eq_neg).1 (hx.trans hsqrt.symm)
  · intro h y
    have hx : x ^ 2 = a := by
      rcases h with rfl | rfl <;> simpa using hsqrt
    rw [(potential_eq_lower_bound_iff a x).2 hx]
    exact potential_lower_bound a y

/-- At and below threshold, the unbroken zero orientation is the unique global
minimum of the quartic potential. -/
theorem global_minimizer_nonpos {a : ℝ} (ha : a ≤ 0) (x : ℝ) :
    (∀ y : ℝ, spinPotential a x ≤ spinPotential a y) ↔ x = 0 := by
  have hnonneg (y : ℝ) : 0 ≤ spinPotential a y := by
    unfold spinPotential
    nlinarith [sq_nonneg (y ^ 2), mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg y)]
  constructor
  · intro h
    have hzero := h 0
    simp only [spinPotential, zero_pow (by decide : 4 ≠ 0),
      zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero, sub_zero] at hzero
    have hx4 : x ^ 4 ≤ 0 := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg x)]
    have hx4zero : (x ^ 2) ^ 2 = 0 := by nlinarith [sq_nonneg (x ^ 2)]
    exact sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hx4zero)
  · rintro rfl y
    simpa [spinPotential] using hnonneg y

/-- Along the scalar drift, the potential derivative is minus the squared
drift and hence cannot be positive. -/
theorem spin_potential_dissipation {a t : ℝ} {x : ℝ → ℝ}
    (hx : HasDerivAt x (spinDrift a (x t)) t) :
    HasDerivAt (fun s => spinPotential a (x s)) (-(spinDrift a (x t)) ^ 2) t := by
  apply ((spin_potential_has_deriv_at a (x t)).comp t hx).congr_deriv
  ring

end Qatlib.Papers.HydroSpinLatt21.SingleSpin
