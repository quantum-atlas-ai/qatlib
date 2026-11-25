/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalPower

/-!
# Maxwell equations for the rational Bateman power family

[Kedia2013TyingKnots], equations (2) and (6),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The derivative of the power factor is a linear combination of the two
Bateman derivatives. Orthogonality to the base field cancels the extra
divergence term, while the Bateman identity cancels the extra curl and time
terms in the Riemann–Silberstein Maxwell equation.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta)
open Qatlib.Papers.KnotLight13.Bateman (power_derivative)
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3 dot_cross_left dot_cross_right)

/-- Cartesian space-time ordered as the three spatial coordinates and time. -/
abbrev Spacetime := ℝ × ℝ × ℝ × ℝ

/-- The base value of a Cartesian space-time coordinate. -/
def coordinateValue (s : Spacetime) (i : Fin 4) : ℝ :=
  ![s.1, s.2.1, s.2.2.1, s.2.2.2] i

/-- Fix three Cartesian space-time coordinates and vary the indicated one. -/
def coordinateSection (s : Spacetime) (i : Fin 4) (u : ℝ) : Spacetime :=
  if i = 0 then (u, s.2.1, s.2.2.1, s.2.2.2)
  else if i = 1 then (s.1, u, s.2.2.1, s.2.2.2)
  else if i = 2 then (s.1, s.2.1, u, s.2.2.2)
  else (s.1, s.2.1, s.2.2.1, u)

/-- At its base parameter the coordinate section gives the original point. -/
@[simp] theorem coordinateSection_at (s : Spacetime) (i : Fin 4) :
    coordinateSection s i (coordinateValue s i) = s := by
  fin_cases i <;> simp [coordinateSection, coordinateValue]

/-- The actual partial derivative along the indicated Cartesian section. -/
noncomputable def spaceTimePartial (f : Spacetime → ℂ) (s : Spacetime) (i : Fin 4) : ℂ :=
  deriv (fun u => f (coordinateSection s i u)) (coordinateValue s i)

/-- Cartesian curl of a space-time vector field, using its spatial partial derivatives. -/
noncomputable def cartesianCurl (F : Spacetime → Fin 3 → ℂ) (s : Spacetime) : Fin 3 → ℂ :=
  ![spaceTimePartial (fun s' => F s' 2) s 1 - spaceTimePartial (fun s' => F s' 1) s 2,
    spaceTimePartial (fun s' => F s' 0) s 2 - spaceTimePartial (fun s' => F s' 2) s 0,
    spaceTimePartial (fun s' => F s' 1) s 0 - spaceTimePartial (fun s' => F s' 0) s 1]

/-- Cartesian divergence of a vector field, using its actual spatial partial derivatives. -/
noncomputable def cartesianDivergence (F : Spacetime → Fin 3 → ℂ) (s : Spacetime) : ℂ :=
  spaceTimePartial (fun s' => F s' 0) s 0 + spaceTimePartial (fun s' => F s' 1) s 1 +
    spaceTimePartial (fun s' => F s' 2) s 2

/-- Smooth functions have the indicated coordinate derivative. -/
private theorem hasDerivAt_coordinateSection {f : Spacetime → ℂ}
    (hf : ContDiff ℝ ⊤ f) (s : Spacetime) (i : Fin 4) :
    HasDerivAt (fun u => f (coordinateSection s i u)) (spaceTimePartial f s i) (coordinateValue s i) := by
  have hsec : Differentiable ℝ (coordinateSection s i) := by
    change Differentiable ℝ (fun u => coordinateSection s i u)
    unfold coordinateSection
    fin_cases i <;> simp <;> fun_prop
  exact ((hf.differentiable (by simp)).comp hsec).differentiableAt.hasDerivAt

/-- The product rule for the actual Cartesian partial. -/
private theorem partial_mul {a f : Spacetime → ℂ}
    (ha : ContDiff ℝ ⊤ a) (hf : ContDiff ℝ ⊤ f) (s : Spacetime) (i : Fin 4) :
    spaceTimePartial (fun s' => a s' * f s') s i =
      spaceTimePartial a s i * f s + a s * spaceTimePartial f s i := by
  change deriv (fun u => a (coordinateSection s i u) * f (coordinateSection s i u))
    (coordinateValue s i) = _
  simpa only [coordinateSection_at] using
    ((hasDerivAt_coordinateSection ha s i).fun_mul (hasDerivAt_coordinateSection hf s i)).deriv

/-- The alpha potential in tuple coordinates. -/
private noncomputable def alphaAt (s : Spacetime) : ℂ :=
  rationalAlpha s.1 s.2.1 s.2.2.1 s.2.2.2

/-- The beta potential in tuple coordinates. -/
private noncomputable def betaAt (s : Spacetime) : ℂ :=
  rationalBeta s.1 s.2.1 s.2.2.1 s.2.2.2

/-- The original rational vector field in tuple coordinates. -/
private noncomputable def fieldAt (s : Spacetime) : Fin 3 → ℂ :=
  rationalField s.1 s.2.1 s.2.2.1 s.2.2.2

local notation "α" => alphaAt
local notation "β" => betaAt
local notation "F₀" => fieldAt

/-- Evaluating the base field at a Cartesian tuple recovers the original field. -/
private theorem fieldAt_mk (x y z t : ℝ) : F₀ (x, y, z, t) = rationalField x y z t := rfl

/-- Linear coefficients in the partial derivative of the power factor. -/
private noncomputable def powerFactorCoefficients (p q : ℕ) (s : Spacetime) : ℂ × ℂ :=
  ((p : ℂ) * ((p - 1 : ℕ) : ℂ) * α s ^ ((p - 1) - 1) * ((q : ℂ) * β s ^ (q - 1)),
    ((p : ℂ) * α s ^ (p - 1)) * (q : ℂ) * ((q - 1 : ℕ) : ℂ) * β s ^ ((q - 1) - 1))

/-- The partial of the power factor lies in the span of the two potential partials. -/
private theorem partial_powerFactor (p q : ℕ) (s : Spacetime) (i : Fin 4) :
    spaceTimePartial (fun s' => rationalPowerFactor p q s'.1 s'.2.1 s'.2.2.1 s'.2.2.2) s i =
      (powerFactorCoefficients p q s).1 * spaceTimePartial α s i +
      (powerFactorCoefficients p q s).2 * spaceTimePartial β s i := by
  have ha := (power_derivative _ _ _ (p - 1) (hasDerivAt_coordinateSection
    contDiff_rationalAlpha s i)).const_mul (p : ℂ)
  have hb := (power_derivative _ _ _ (q - 1) (hasDerivAt_coordinateSection
    contDiff_rationalBeta s i)).const_mul (q : ℂ)
  have h := (ha.fun_mul hb).deriv
  change deriv (fun u =>
    ((p : ℂ) * rationalAlpha (coordinateSection s i u).1 (coordinateSection s i u).2.1
      (coordinateSection s i u).2.2.1 (coordinateSection s i u).2.2.2 ^ (p - 1)) *
    ((q : ℂ) * rationalBeta (coordinateSection s i u).1 (coordinateSection s i u).2.1
      (coordinateSection s i u).2.2.1 (coordinateSection s i u).2.2.2 ^ (q - 1)))
    (coordinateValue s i) = _
  rw [h]
  simp only [coordinateSection_at, powerFactorCoefficients, alphaAt, betaAt]
  delta alphaAt betaAt
  ring

/-- The rational alpha partials agree with the entries of its spatial gradient
and its time derivative. -/
private theorem alphaPartials (x y z t : ℝ) (i : Fin 4) :
    spaceTimePartial α (x, y, z, t) i =
      ![alphaGradient x y z t 0, alphaGradient x y z t 1,
        alphaGradient x y z t 2, alphaTimePartial x y z t] i := by
  fin_cases i
  · exact (hasDerivAt_rationalAlpha_x x y z t).deriv
  · exact (hasDerivAt_rationalAlpha_y x y z t).deriv
  · exact (hasDerivAt_rationalAlpha_z x y z t).deriv
  · exact (hasDerivAt_rationalAlpha_t x y z t).deriv

/-- The rational beta partials agree with the entries of its spatial gradient
and its time derivative. -/
private theorem betaPartials (x y z t : ℝ) (i : Fin 4) :
    spaceTimePartial β (x, y, z, t) i =
      ![betaGradient x y z t 0, betaGradient x y z t 1,
        betaGradient x y z t 2, betaTimePartial x y z t] i := by
  fin_cases i
  · exact (hasDerivAt_rationalBeta_x x y z t).deriv
  · exact (hasDerivAt_rationalBeta_y x y z t).deriv
  · exact (hasDerivAt_rationalBeta_z x y z t).deriv
  · exact (hasDerivAt_rationalBeta_t x y z t).deriv

/-- The algebraic Bateman identity turns the extra curl term into the
matching time-derivative term when the multiplier derivatives lie in the
span of the two potential derivatives. -/
private theorem cross_bateman_multiplier (a b : Fin 3 → ℂ) (atime btime A B : ℂ)
    (h : cross3 a b = fun j => Complex.I * (atime * b j - btime * a j)) :
    cross3 (fun j => A * a j + B * b j) (cross3 a b) =
      fun j => Complex.I * (A * atime + B * btime) * cross3 a b j := by
  conv_lhs => rw [h]
  funext j
  fin_cases j <;> simp [cross3] <;> ring

/-- A component derivative of the powered field splits into the derivative
of the original field and the contribution from the multiplier. -/
private theorem partial_powerField (p q : ℕ) (s : Spacetime) (j : Fin 3) (i : Fin 4) :
    spaceTimePartial (fun s' => rationalPowerField p q s'.1 s'.2.1 s'.2.2.1 s'.2.2.2 j) s i =
      ((powerFactorCoefficients p q s).1 * spaceTimePartial α s i +
        (powerFactorCoefficients p q s).2 * spaceTimePartial β s i) * F₀ s j +
      rationalPowerFactor p q s.1 s.2.1 s.2.2.1 s.2.2.2 *
        spaceTimePartial (fun s' => F₀ s' j) s i := by
  have hfun : (fun s' : Spacetime => rationalPowerField p q s'.1 s'.2.1 s'.2.2.1 s'.2.2.2 j) =
      fun s' => rationalPowerFactor p q s'.1 s'.2.1 s'.2.2.1 s'.2.2.2 * F₀ s' j := by
    funext s'
    exact congrFun (rationalPowerField_eq p q s'.1 s'.2.1 s'.2.2.1 s'.2.2.2) j
  rw [hfun]
  delta fieldAt
  rw [partial_mul (contDiff_rationalPowerFactor p q) (contDiff_rationalField j),
    partial_powerFactor]

/-- The powered rational field solves the curl–time Maxwell equation for
every pair of natural exponents. -/
theorem maxwell_rational_power_field (p q : ℕ) (x y z t : ℝ) (j : Fin 3) :
    cartesianCurl (fun s =>
      rationalPowerField p q s.1 s.2.1 s.2.2.1 s.2.2.2) (x, y, z, t) j =
      Complex.I * spaceTimePartial
        (fun s => rationalPowerField p q s.1 s.2.1 s.2.2.1 s.2.2.2 j) (x, y, z, t) 3 := by
  have hcurl : cartesianCurl F₀ (x, y, z, t) = fieldCurl x y z t := rfl
  have ht (j : Fin 3) : spaceTimePartial (fun s => F₀ s j) (x, y, z, t) 3 = fieldTimeDeriv x y z t j := rfl
  have hb := congrFun (cross_bateman_multiplier (alphaGradient x y z t) (betaGradient x y z t)
    (alphaTimePartial x y z t) (betaTimePartial x y z t)
    (powerFactorCoefficients p q (x, y, z, t)).1 (powerFactorCoefficients p q (x, y, z, t)).2
    (bateman_rational_pair x y z t)) j
  have hm := maxwell_rational_field x y z t j
  rw [← hcurl, ← ht] at hm
  fin_cases j <;>
    simp [cartesianCurl, cross3, partial_powerField, alphaPartials, betaPartials] at hb hm ⊢ <;>
    simp [fieldAt_mk, rationalField, cross3] <;>
    linear_combination hb + rationalPowerFactor p q x y z t * hm

/-- The powered rational field has zero divergence. The multiplier derivative
is orthogonal to the base cross product. -/
theorem rational_power_field_divergence_free (p q : ℕ) (x y z t : ℝ) :
    cartesianDivergence
      (fun s => rationalPowerField p q s.1 s.2.1 s.2.2.1 s.2.2.2) (x, y, z, t) = 0 := by
  have hd : cartesianDivergence F₀ (x, y, z, t) = 0 :=
    rational_field_divergence_free x y z t
  have ha := dot_cross_left (alphaGradient x y z t) (betaGradient x y z t)
  have hb := dot_cross_right (alphaGradient x y z t) (betaGradient x y z t)
  simp [cartesianDivergence, partial_powerField, alphaPartials, betaPartials]
  simp only [cartesianDivergence] at hd
  simp only [dot3] at ha hb
  simp only [fieldAt_mk, rationalField]
  linear_combination rationalPowerFactor p q x y z t * hd +
    (powerFactorCoefficients p q (x, y, z, t)).1 * ha +
    (powerFactorCoefficients p q (x, y, z, t)).2 * hb

end Qatlib.Papers.KnotLight13.TorusFamily
