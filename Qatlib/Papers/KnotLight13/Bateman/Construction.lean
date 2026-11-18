/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic

/-!
# Bateman's compatibility condition and polynomial reparametrizations

[Kedia2013TyingKnots], equations (1)–(6),
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
The complex gradients a = ∇α and b = ∇β must satisfy the Bateman relation
a × b = i(αₜ b − βₜ a). A cross product of arbitrary gradients is not null.
We prove the algebraic implication, its stability under complex rescaling and
the Jacobian determinant rule for reparametrizing two potentials. Derivative
rules for powers justify the coefficients used in the polynomial family.
No Maxwell existence theorem, global smoothness, finite-energy integral,
classification of field-line knots or topology-preserving PDE evolution is proved.
The electromagnetic invariant equivalence is
`Qatlib.Papers.KnottedLight08.HopfField.null_iff`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.Bateman

open Qatlib.Papers.KnottedLight08.HopfField

/-- Bateman compatibility forces the bilinear square of the constructed field to vanish. -/
theorem bateman_null (a b : Fin 3 → ℂ) (alphaTime betaTime : ℂ)
    (compatibility : cross3 a b =
      fun j => Complex.I * (alphaTime * b j - betaTime * a j)) :
    dot3 (cross3 a b) (cross3 a b) = 0 := by
  calc
    dot3 (cross3 a b) (cross3 a b) =
        dot3 (cross3 a b)
          (fun j => Complex.I * (alphaTime * b j - betaTime * a j)) :=
      congrArg (dot3 (cross3 a b)) compatibility
    _ = Complex.I * (alphaTime * dot3 (cross3 a b) b -
        betaTime * dot3 (cross3 a b) a) := by simp [dot3]; ring
    _ = 0 := by rw [dot_cross_left, dot_cross_right]; ring

/-- Reconstruct a complex field from its electric and magnetic real components. -/
theorem field_from_parts (F : Fin 3 → ℂ) :
    riemannSilberstein (fun j => (F j).re) (fun j => (F j).im) = F := by
  funext j
  apply Complex.ext <;> simp [riemannSilberstein]

/-- A compatible Bateman pair yields perpendicular real fields of equal squared magnitude. -/
theorem bateman_real_invariants (a b : Fin 3 → ℂ) (alphaTime betaTime : ℂ)
    (compatibility : cross3 a b =
      fun j => Complex.I * (alphaTime * b j - betaTime * a j)) :
    dot3 (fun j => (cross3 a b j).re) (fun j => (cross3 a b j).im) = 0 ∧
      squaredLength (fun j => (cross3 a b j).re) =
      squaredLength (fun j => (cross3 a b j).im) := by
  apply (null_iff _ _).mp
  rw [field_from_parts]
  exact bateman_null a b alphaTime betaTime compatibility

/-- Complex multiplication preserves algebraic nullness. -/
theorem rescale_null (F : Fin 3 → ℂ) (h : ℂ) (hF : dot3 F F = 0) :
    dot3 (fun j => h * F j) (fun j => h * F j) = 0 := by
  calc
    _ = h ^ 2 * dot3 F F := by simp [dot3]; ring
    _ = 0 := by rw [hF, mul_zero]

/-- The two-potential chain rule changes the cross product by the Jacobian determinant. -/
theorem reparametrization_cross (a b : Fin 3 → ℂ) (fa fb ga gb : ℂ) :
    cross3 (fun j => fa * a j + fb * b j) (fun j => ga * a j + gb * b j) =
      fun j => (fa * gb - fb * ga) * cross3 a b j := by
  funext j
  fin_cases j <;> simp [cross3] <;> ring

/-- Every chain-rule reparametrization of a compatible pair remains algebraically null. -/
theorem reparametrized_null (a b : Fin 3 → ℂ) (alphaTime betaTime fa fb ga gb : ℂ)
    (compatibility : cross3 a b =
      fun j => Complex.I * (alphaTime * b j - betaTime * a j)) :
    let F := cross3 (fun j => fa * a j + fb * b j) (fun j => ga * a j + gb * b j)
    dot3 F F = 0 := by
  dsimp
  rw [reparametrization_cross]
  exact rescale_null _ _ (bateman_null a b alphaTime betaTime compatibility)

/-- The derivative of a complex potential power supplies its exact chain-rule coefficient. -/
theorem power_derivative (f : ℝ → ℂ) (df : ℂ) (t : ℝ) (n : ℕ)
    (hf : HasDerivAt f df t) :
    HasDerivAt (fun s => f s ^ n) ((n : ℂ) * f t ^ (n - 1) * df) t := by
  simpa only [mul_assoc] using hf.fun_pow n

/-- Coordinate gradients e₁ and e₂ have a nonnull cross product, so compatibility is essential. -/
theorem arbitrary_cross_not_null :
    dot3 (cross3 (![1, 0, 0] : Fin 3 → ℂ) ![0, 1, 0])
      (cross3 (![1, 0, 0] : Fin 3 → ℂ) ![0, 1, 0]) ≠ 0 := by
  norm_num [dot3, cross3]

/-- The real field obtained by multiplying E+iB by the complex scalar a+ib. -/
def rescaledElectric (a b : ℝ) (E B : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => a * E j - b * B j

/-- The imaginary field obtained by the same complex multiplication. -/
def rescaledMagnetic (a b : ℝ) (E B : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => b * E j + a * B j

/-- Complex scalar multiplication acts on the real electric and magnetic pair by these formulas. -/
theorem complex_rescaling_parts (a b : ℝ) (E B : Fin 3 → ℝ) :
    riemannSilberstein (rescaledElectric a b E B) (rescaledMagnetic a b E B) =
      fun j => ((a : ℂ) + Complex.I * (b : ℂ)) * riemannSilberstein E B j := by
  funext j
  apply Complex.ext
  · simp [riemannSilberstein, rescaledElectric, rescaledMagnetic,
      Complex.mul_re, Complex.mul_im]
  · simp [riemannSilberstein, rescaledElectric, rescaledMagnetic,
      Complex.mul_re, Complex.mul_im]
    ring

/-- The Poynting numerator scales by the squared modulus of the complex multiplier. -/
theorem poynting_rescaling (a b : ℝ) (E B : Fin 3 → ℝ) :
    cross3 (rescaledElectric a b E B) (rescaledMagnetic a b E B) =
      fun j => (a ^ 2 + b ^ 2) * cross3 E B j := by
  funext j
  fin_cases j <;> simp [cross3, rescaledElectric, rescaledMagnetic] <;> ring

/-- The electromagnetic squared-magnitude sum has the same rescaling factor. -/
theorem energy_rescaling (a b : ℝ) (E B : Fin 3 → ℝ) :
    squaredLength (rescaledElectric a b E B) + squaredLength (rescaledMagnetic a b E B) =
      (a ^ 2 + b ^ 2) * (squaredLength E + squaredLength B) := by
  simp [squaredLength, dot3, rescaledElectric, rescaledMagnetic]
  ring

/-- The energy-normalized Poynting velocity, in units where the light speed is one. -/
noncomputable def poyntingVelocity (E B : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => 2 * cross3 E B j / (squaredLength E + squaredLength B)

/-- Nonzero complex rescaling preserves energy-normalized Poynting velocity. -/
theorem poynting_velocity_invariant (a b : ℝ) (E B : Fin 3 → ℝ)
    (hscalar : a ^ 2 + b ^ 2 ≠ 0) (henergy : squaredLength E + squaredLength B ≠ 0) :
    poyntingVelocity (rescaledElectric a b E B) (rescaledMagnetic a b E B) =
      poyntingVelocity E B := by
  funext j
  unfold poyntingVelocity
  rw [poynting_rescaling, energy_rescaling]
  field_simp [hscalar, henergy]

end Qatlib.Papers.KnotLight13.Bateman
