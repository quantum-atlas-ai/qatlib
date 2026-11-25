/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalEnergy

/-!
# The power family of rational Bateman fields

[Kedia2013TyingKnots], equations (2) and (6),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The actual coordinate gradients of the rational potentials raised to powers
produce the complex field of equation (6). The power chain rule supplies its
scalar multiplier. The unit-sphere identity bounds this multiplier at each
point and yields finite energy at every time.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta complex_rational_pair_unit)
open Qatlib.Papers.KnotLight13.Bateman (power_derivative rescale_null)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open MeasureTheory

/-- Spatial gradient of the powered rational scalar `α^p`, using the
actual derivatives along the three Cartesian axes. -/
noncomputable def alphaPowerGradient (p : ℕ) (x y z t : ℝ) : Fin 3 → ℂ :=
  ![deriv (fun s => rationalAlpha s y z t ^ p) x,
    deriv (fun s => rationalAlpha x s z t ^ p) y,
    deriv (fun s => rationalAlpha x y s t ^ p) z]

/-- Spatial gradient of the powered rational scalar `β^q`, using the
actual derivatives along the three Cartesian axes. -/
noncomputable def betaPowerGradient (q : ℕ) (x y z t : ℝ) : Fin 3 → ℂ :=
  ![deriv (fun s => rationalBeta s y z t ^ q) x,
    deriv (fun s => rationalBeta x s z t ^ q) y,
    deriv (fun s => rationalBeta x y s t ^ q) z]

/-- The field of equation (6), the cross product `∇α^p × ∇β^q`. -/
noncomputable def rationalPowerField (p q : ℕ) (x y z t : ℝ) : Fin 3 → ℂ :=
  cross3 (alphaPowerGradient p x y z t) (betaPowerGradient q x y z t)

/-- The Jacobian scalar of the power reparametrization of the two potentials.
A zero power gives a zero scalar, including at zeros of a potential. -/
noncomputable def rationalPowerFactor (p q : ℕ) (x y z t : ℝ) : ℂ :=
  (p : ℂ) * rationalAlpha x y z t ^ (p - 1) *
    ((q : ℂ) * rationalBeta x y z t ^ (q - 1))

/-- The true gradient of `α^p` is its power chain-rule factor times
the true gradient of `α`. -/
theorem alphaPowerGradient_eq (p : ℕ) (x y z t : ℝ) :
    alphaPowerGradient p x y z t =
      fun j => (p : ℂ) * rationalAlpha x y z t ^ (p - 1) * alphaGradient x y z t j := by
  funext j
  fin_cases j
  · exact (power_derivative _ _ _ p (hasDerivAt_rationalAlpha_x x y z t)).deriv
  · exact (power_derivative _ _ _ p (hasDerivAt_rationalAlpha_y x y z t)).deriv
  · exact (power_derivative _ _ _ p (hasDerivAt_rationalAlpha_z x y z t)).deriv

/-- The true gradient of `β^q` is its power chain-rule factor times
the true gradient of `β`. -/
theorem betaPowerGradient_eq (q : ℕ) (x y z t : ℝ) :
    betaPowerGradient q x y z t =
      fun j => (q : ℂ) * rationalBeta x y z t ^ (q - 1) * betaGradient x y z t j := by
  funext j
  fin_cases j
  · exact (power_derivative _ _ _ q (hasDerivAt_rationalBeta_x x y z t)).deriv
  · exact (power_derivative _ _ _ q (hasDerivAt_rationalBeta_y x y z t)).deriv
  · exact (power_derivative _ _ _ q (hasDerivAt_rationalBeta_z x y z t)).deriv

/-- The powered field is the original rational field multiplied by the
Jacobian scalar of the power reparametrization. -/
theorem rationalPowerField_eq (p q : ℕ) (x y z t : ℝ) :
    rationalPowerField p q x y z t =
      fun j => rationalPowerFactor p q x y z t * rationalField x y z t j := by
  rw [rationalPowerField, alphaPowerGradient_eq, betaPowerGradient_eq]
  funext j
  fin_cases j <;> simp [cross3, rationalPowerFactor, rationalField] <;> ring

/-- The squared complex bilinear norm of the powered field vanishes at
each point. This holds for every pair of natural exponents. -/
theorem rational_power_field_null (p q : ℕ) (x y z t : ℝ) :
    dot3 (rationalPowerField p q x y z t) (rationalPowerField p q x y z t) = 0 := by
  rw [rationalPowerField_eq]
  exact rescale_null _ _ (rational_field_null x y z t)

/-- The reparametrization factor is smooth on all real space-time. -/
theorem contDiff_rationalPowerFactor (p q : ℕ) :
    ContDiff ℝ ⊤ (fun s : ℝ × ℝ × ℝ × ℝ =>
      rationalPowerFactor p q s.1 s.2.1 s.2.2.1 s.2.2.2) :=
  (contDiff_const.mul (contDiff_rationalAlpha.pow (p - 1))).mul
    (contDiff_const.mul (contDiff_rationalBeta.pow (q - 1)))

/-- Each field component in the power family is smooth on all real space-time. -/
theorem contDiff_rationalPowerField (p q : ℕ) (j : Fin 3) :
    ContDiff ℝ ⊤ (fun s : ℝ × ℝ × ℝ × ℝ =>
      rationalPowerField p q s.1 s.2.1 s.2.2.1 s.2.2.2 j) := by
  simp only [rationalPowerField_eq]
  exact (contDiff_rationalPowerFactor p q).mul (contDiff_rationalField j)

/-- The squared modulus of the power Jacobian is at most `(p q)²`.
The bound follows from the two potentials lying on the unit sphere. -/
theorem normSq_rationalPowerFactor_le (p q : ℕ) (x y z t : ℝ) :
    Complex.normSq (rationalPowerFactor p q x y z t) ≤ ((p : ℝ) * (q : ℝ)) ^ 2 := by
  have hunit := complex_rational_pair_unit x y z t
  have hα : Complex.normSq (rationalAlpha x y z t) ≤ 1 := by
    linarith [Complex.normSq_nonneg (rationalBeta x y z t)]
  have hβ : Complex.normSq (rationalBeta x y z t) ≤ 1 := by
    linarith [Complex.normSq_nonneg (rationalAlpha x y z t)]
  have ha := pow_le_one₀ (n := p - 1) (Complex.normSq_nonneg (rationalAlpha x y z t)) hα
  have hb := pow_le_one₀ (n := q - 1) (Complex.normSq_nonneg (rationalBeta x y z t)) hβ
  simp only [rationalPowerFactor, Complex.normSq_mul, map_pow, mul_pow]
  rw [show Complex.normSq (p : ℂ) = (p : ℝ) ^ 2 by simp [Complex.normSq_apply, pow_two],
    show Complex.normSq (q : ℂ) = (q : ℝ) ^ 2 by simp [Complex.normSq_apply, pow_two]]
  exact mul_le_mul (by simpa using mul_le_mul_of_nonneg_left ha (sq_nonneg (p : ℝ)))
    (by simpa using mul_le_mul_of_nonneg_left hb (sq_nonneg (q : ℝ)))
    (mul_nonneg (sq_nonneg (q : ℝ)) (pow_nonneg (Complex.normSq_nonneg _) _))
    (sq_nonneg (p : ℝ))

/-- At every time, the actual field `∇α^p × ∇β^q` has finite spatial
energy with respect to Lebesgue measure on Euclidean three-space. -/
theorem rationalPowerField_energy_integrable (p q : ℕ) (t : ℝ) :
    Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
      ∑ j : Fin 3, Complex.normSq (rationalPowerField p q (s 0) (s 1) (s 2) t j)) := by
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  have hcoords : Continuous (fun s : EuclideanSpace ℝ (Fin 3) => (s 0, s 1, s 2, t)) :=
    (PiLp.continuous_apply 2 _ 0).prodMk
      ((PiLp.continuous_apply 2 _ 1).prodMk
        ((PiLp.continuous_apply 2 _ 2).prodMk continuous_const))
  have hcont := Complex.continuous_normSq.comp
    ((contDiff_rationalPowerField p q j).continuous.comp hcoords)
  refine ((integrable_normSq_rationalField t j).const_mul (((p : ℝ) * (q : ℝ)) ^ 2)).mono_nonneg
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun _ => Complex.normSq_nonneg _) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  simp only [rationalPowerField_eq, Complex.normSq_mul]
  exact mul_le_mul_of_nonneg_right (normSq_rationalPowerFactor_le p q (s 0) (s 1) (s 2) t)
    (Complex.normSq_nonneg _)

end Qatlib.Papers.KnotLight13.TorusFamily
