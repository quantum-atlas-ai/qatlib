/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.Rotation.ConstantSpeedDifferential

@[expose] public section

/-!
# Consumers of the instantaneous-radius constant-speed orbit analysis

Concrete checks for [Saenz2021HydroSpinLattices], Methods equations (31)-(32):
the exact unit-parameter co- and counter-rotating equilibria, rejected
zero-frequency and wrong-speed states, existence and uniqueness at the
article parameters, the circular-orbit Jacobian and characteristic cubic,
and spectral non-root witnesses on the nonnegative real and imaginary axes.
The axiom closures of the main theorems are printed at the end.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.HydroSpinLatt21.Rotation
open Polynomial

namespace QatlibTests.HydroSpinConstantSpeedRegression

/-! ## Exact positive and negative examples -/

/-- At `k=1/4`, `τ=u₀=1` and `Ω=0`, `(r,v,ω)=(1,0,1)` is an exact co-rotating
equilibrium of the literal field. -/
example : constantSpeedSpinField (1 / 4) 1 1 0 (1, 0, 1) = 0 := by
  norm_num [constantSpeedSpinField, zeroWavePhaseRHS, instantaneousRayleighRHS,
    coriolisRadialRHS]

/-- The reversed frequency `(r,v,ω)=(1,0,-1)` is an exact counter-rotating
equilibrium at the same parameters. -/
example : constantSpeedSpinField (1 / 4) 1 1 0 (1, 0, -1) = 0 := by
  norm_num [constantSpeedSpinField, zeroWavePhaseRHS, instantaneousRayleighRHS,
    coriolisRadialRHS]

/-- Zero frequency is not a positive-radius equilibrium: the radial balance
still contains the nonzero quartic-well acceleration. -/
example : constantSpeedSpinField (1 / 4) 1 1 0 (1, 0, 0) ≠ 0 := by
  norm_num [constantSpeedSpinField, zeroWavePhaseRHS, instantaneousRayleighRHS,
    coriolisRadialRHS]

/-- The fixed-reference value `ω=1` is not enough when the instantaneous
speed condition fails: `(r,v,ω)=(2,0,1)` is not an equilibrium. -/
example : constantSpeedSpinField (1 / 4) 1 1 0 (2, 0, 1) ≠ 0 := by
  norm_num [constantSpeedSpinField, zeroWavePhaseRHS, instantaneousRayleighRHS,
    coriolisRadialRHS]

/-! ## Existence and uniqueness at the article parameters -/

/-- A unique co-rotating circular orbit exists at `k=4.34`, `τ=0.1`,
`u₀=6`, and `Ω=0.75` in the article's unit convention. -/
example : ∃ p : ℝ × ℝ × ℝ, 0 < p.1 ∧
    constantSpeedSpinField (217 / 50) (1 / 10) 6 (3 / 4) p = 0 ∧ 0 < p.2.2 := by
  obtain ⟨p, hp, _⟩ := corotating_orbit_exists_unique
    (217 / 50) (1 / 10) 6 (3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p, hp⟩

/-- A unique counter-rotating circular orbit exists at the same parameters;
unlike the fixed-reference reduction, there is no finite `ω₀/2` existence
threshold. -/
example : ∃ p : ℝ × ℝ × ℝ, 0 < p.1 ∧
    constantSpeedSpinField (217 / 50) (1 / 10) 6 (3 / 4) p = 0 ∧ p.2.2 < 0 := by
  obtain ⟨p, hp, _⟩ := counterrotating_orbit_exists_unique
    (217 / 50) (1 / 10) 6 (3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p, hp⟩

/-- Every negative-frequency equilibrium at these parameters has frequency
strictly below `-2Ω`. -/
example (r ω : ℝ) (hr : 0 < r) (hω : ω < 0)
    (hz : constantSpeedSpinField (217 / 50) (1 / 10) 6 (3 / 4) (r, 0, ω) = 0) :
    ω < -2 * (3 / 4) :=
  counterrotating_frequency_lt (217 / 50) (1 / 10) 6 (3 / 4) r ω
    (by norm_num) hr hω hz

/-! ## Jacobian, characteristic cubic, and spectral witnesses -/

/-- At the unit co-rotating orbit, the Jacobian is explicit; its bottom-left
entry is the instantaneous-radius Rayleigh derivative `-2ω/(τr)=-2`. -/
example : constantSpeedJacobian (1 / 4) 1 1 0 1 1 =
    !![0, 1, 0; -2, 0, 2; -2, -2, -2] := by
  rw [constantSpeedJacobian_at_orbit (1 / 4) 1 1 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The unit-orbit characteristic polynomial is `λ³+2λ²+6λ+8`. -/
example : (constantSpeedJacobian (1 / 4) 1 1 0 1 1).charpoly =
    X ^ 3 + C 2 * X ^ 2 + C 6 * X + C 8 := by
  rw [charpoly_constantSpeedJacobian_at_orbit (1 / 4) 1 1 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The unit-orbit Routh--Hurwitz determinant is strictly positive. -/
example : (0 : ℝ) < 2 * 6 - 8 := by norm_num

/-- `1` is not a characteristic root of the unit co-rotating Jacobian. -/
example : ((constantSpeedJacobian (1 / 4) 1 1 0 1 1).charpoly.map
    Complex.ofRealHom).eval 1 ≠ 0 := by
  intro h
  have hre := corotating_charpoly_roots_re_neg (1 / 4) 1 1 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 h
  simp only [Complex.one_re] at hre
  norm_num at hre

/-- `I` is not a characteristic root of the unit co-rotating Jacobian. -/
example : ((constantSpeedJacobian (1 / 4) 1 1 0 1 1).charpoly.map
    Complex.ofRealHom).eval Complex.I ≠ 0 := by
  intro h
  have hre := corotating_charpoly_roots_re_neg (1 / 4) 1 1 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Complex.I h
  simp only [Complex.I_re] at hre
  norm_num at hre

/-- `1` is not a characteristic root of the unit counter-rotating Jacobian. -/
example : ((constantSpeedJacobian (1 / 4) 1 1 0 1 (-1)).charpoly.map
    Complex.ofRealHom).eval 1 ≠ 0 := by
  intro h
  have hre := counterrotating_charpoly_roots_re_neg (1 / 4) 1 1 0 1 (-1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 h
  simp only [Complex.one_re] at hre
  norm_num at hre

/-- `I` is not a characteristic root of the unit counter-rotating Jacobian. -/
example : ((constantSpeedJacobian (1 / 4) 1 1 0 1 (-1)).charpoly.map
    Complex.ofRealHom).eval Complex.I ≠ 0 := by
  intro h
  have hre := counterrotating_charpoly_roots_re_neg (1 / 4) 1 1 0 1 (-1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Complex.I h
  simp only [Complex.I_re] at hre
  norm_num at hre

/-! ## Axiom closures -/

#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.azimuthal_balance_eq32_zero_wave
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.constantSpeedSpinField_eq_zero_iff
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.circular_orbit_frequency_equation
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.counterrotating_frequency_lt
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.corotating_frequency_exists_unique
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.counterrotating_frequency_exists_unique
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.corotating_orbit_exists_unique
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.counterrotating_orbit_exists_unique
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.zeroWavePhaseRHS_hasDerivAt_r
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.zeroWavePhaseRHS_hasDerivAt_v
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.zeroWavePhaseRHS_hasDerivAt_ω
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.constantSpeedJacobian_at_orbit
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.constantSpeedJacobian_det_eq
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.charpoly_constantSpeedJacobian_at_orbit
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.constantSpeed_charpoly_roots_re_neg
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.corotating_charpoly_roots_re_neg
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.counterrotating_charpoly_roots_re_neg
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.cubic_re_neg_of_routh_hurwitz

end QatlibTests.HydroSpinConstantSpeedRegression

/-- The full Fréchet derivative of the actual field has the nonzero radial
Rayleigh entry at the exact unit orbit. -/
example :
    fderiv ℝ (constantSpeedSpinField (1 / 4) 1 1 0) (1, 0, 1) (1, 0, 0) =
      (0, -2, -2) := by
  have h := fderiv_constantSpeedSpinField_columns (1 / 4) 1 1 0 1 1 (by norm_num) 0
  norm_num [constantSpeedJacobian] at h
  exact h

#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.fderiv_constantSpeedSpinField_matrix
