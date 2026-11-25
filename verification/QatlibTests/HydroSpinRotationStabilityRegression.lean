/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.Rotation.CircularOrbitStability

@[expose] public section

/-!
# Consumers of the rotating-frame circular-orbit stability analysis

Concrete nondegenerate instances of the rotating-frame circular-orbit
analysis for [Saenz2021HydroSpinLattices] Methods equations (31)-(32), at
the article's parameter values `τ = 0.1 s`, `ω₀ = 10/3 s⁻¹` (speed
`u₀ = 6 mm s⁻¹` at the reference radius `r₀ = 1.8 mm`) and well stiffness
`k = 4.34 mm⁻² s⁻²`, with the strict polar rotation-coupling coefficient
`κ = 2`: the co- and counter-rotating orbits at bath rotation
`Ω = 0.75 s⁻¹` (below the reduced counter-rotating threshold `ω₀/2`) are
exact equilibria, no counter-rotating orbit survives at `Ω = 2 s⁻¹`, the
linearization is nondegenerate with all characteristic roots in the open
left half-plane (witnessed by `1` and `I` not being roots), the
Routh-Hurwitz data is strictly positive, and the Lyapunov form is
nonnegative and positive away from the origin. The axiom closures of the
main theorems are checked at the end.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.HydroSpinLatt21.Rotation

namespace QatlibTests.HydroSpinRotationStabilityRegression

/-! ## Circular-orbit existence at the article parameters -/

/-- The co-rotating circular orbit at `Ω = 0.75 s⁻¹` is an exact equilibrium
of the coupled system (31)+(32). -/
example : rotatingSpinField 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (radialEquilibrium (10 / 3) (3 / 4) (217 / 50), 0, 10 / 3) = 0 :=
  corotating_circular_orbit 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)

/-- The counter-rotating circular orbit exists at `Ω = 0.75 s⁻¹`, below the
reduced threshold `ω₀ / 2 = 5/3 s⁻¹`. -/
example : ∃ r : ℝ, 0 < r ∧
    rotatingSpinField 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4) (r, 0, -(10 / 3)) = 0 :=
  (counterrotating_orbit_iff 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Above the reduced threshold, `Ω = 2 s⁻¹ > ω₀ / 2`, no positive-radius
counter-rotating circular orbit exists. -/
example (r : ℝ) (hr : 0 < r) :
    rotatingSpinField 2 (217 / 50) (1 / 10) (10 / 3) 2 (r, 0, -(10 / 3)) ≠ 0 := by
  intro hz
  have hlt := (counterrotating_orbit_iff 2 (217 / 50) (1 / 10) (10 / 3) 2
    (by norm_num) (by norm_num)).mp ⟨r, hr, hz⟩
  norm_num at hlt

/-! ## Nondegeneracy and the Routh-Hurwitz data -/

/-- The linearization at the co-rotating orbit is nondegenerate. -/
example : (spinJacobian 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (radialEquilibrium (10 / 3) (3 / 4) (217 / 50)) (10 / 3)).det ≠ 0 :=
  spinJacobian_det_ne_zero 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4) (10 / 3)
    (by norm_num) (by norm_num) (Or.inl rfl) (by norm_num) (by norm_num)

/-- The Routh-Hurwitz data of the characteristic cubic at the article
parameters is strictly positive: `a₁ = 2/τ`,
`a₂ = 2κ(ω₀+Ω)² + 2ω₀(ω₀+2Ω)`, `a₃ = (4/τ)ω₀(ω₀+2Ω)` and the collapsed
determinant `a₁a₂ - a₃ = (4κ/τ)(ω₀+Ω)²`. -/
example : (0 : ℝ) < 2 / (1 / 10) := by norm_num

example : (0 : ℝ) < 2 * 2 * (10 / 3 + 3 / 4) ^ 2
    + 2 * (10 / 3) * (10 / 3 + 2 * (3 / 4)) := by norm_num

example : (0 : ℝ) < (4 / (1 / 10)) * (10 / 3 * (10 / 3 + 2 * (3 / 4))) := by
  norm_num

example : (0 : ℝ) < (4 * 2 / (1 / 10)) * (10 / 3 + 3 / 4) ^ 2 := by norm_num

/-! ## Spectral stability witnesses -/

/-- `1` is not a characteristic root of the co-rotating linearization: a
root on the positive real axis would contradict the Routh-Hurwitz
criterion. -/
example : ((spinJacobian 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (radialEquilibrium (10 / 3) (3 / 4) (217 / 50)) (10 / 3)).charpoly.map
    Complex.ofRealHom).eval 1 ≠ 0 := by
  intro h
  have hre := charpoly_roots_re_neg 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (10 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) (by norm_num) 1 h
  simp only [Complex.one_re] at hre
  norm_num at hre

/-- The imaginary unit is not a characteristic root either: a purely
imaginary root would contradict the Routh-Hurwitz criterion. -/
example : ((spinJacobian 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (radialEquilibrium (10 / 3) (3 / 4) (217 / 50)) (10 / 3)).charpoly.map
    Complex.ofRealHom).eval Complex.I ≠ 0 := by
  intro h
  have hre := charpoly_roots_re_neg 2 (217 / 50) (1 / 10) (10 / 3) (3 / 4)
    (10 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) (by norm_num) Complex.I h
  simp only [Complex.I_re] at hre
  norm_num at hre

/-! ## The Lyapunov form -/

/-- The Lyapunov form is nonnegative everywhere at the article parameters. -/
example (p : ℝ × ℝ × ℝ) : 0 ≤ orbitLyapunov 2 (217 / 50) (3 / 4) (10 / 3) p :=
  orbitLyapunov_nonneg 2 (217 / 50) (3 / 4) (10 / 3) (by norm_num)
    (by norm_num) p

/-- The Lyapunov form vanishes at the orbit and is positive away from it
(witnessed at a unit radial displacement). -/
example : orbitLyapunov 2 (217 / 50) (3 / 4) (10 / 3) (0, 0, 0) = 0 := by
  norm_num [orbitLyapunov]

example : 0 < orbitLyapunov 2 (217 / 50) (3 / 4) (10 / 3) (1, 0, 0) := by
  norm_num [orbitLyapunov]

/-! ## Axiom closures -/

#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.rotatingSpinField_eq_zero_iff
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.corotating_circular_orbit
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.counterrotating_orbit_iff
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.radialEquilibrium_strict_mono_in_Ω
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.counterrotating_radius_lt_corotating
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.counterrotating_radius_tendsto_zero
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.spinJacobian_at_orbit
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.spinJacobian_det_ne_zero
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.charpoly_spinJacobian_at_orbit
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.charpoly_roots_re_neg
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.cubic_re_neg_of_routh_hurwitz
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.orbitLyapunov_nonneg
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.hasDerivAt_orbitLyapunov
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.orbitLyapunov_nonincreasing

end QatlibTests.HydroSpinRotationStabilityRegression
