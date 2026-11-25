/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPotential

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Initial energy and helicity densities of the Bateman power family

[Kedia2013TyingKnots], equation (6) and the conserved quantities on page 150404-3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
In the initial stereographic chart the unnormalized helicity density and
the usual electromagnetic energy density reduce to powers of the two
squared sphere coordinates with explicit radial factors.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta)
open scoped ComplexConjugate

/-- The common complex denominator is real on the initial slice. -/
private theorem complexDenominator_zero_time (x y z : ℝ) :
    complexDenominator x y z 0 = ((x ^ 2 + y ^ 2 + z ^ 2 + 1 : ℝ) : ℂ) := by
  simp [complexDenominator, radialAux]

/-- The α numerator is its stereographic real coordinate plus its
imaginary coordinate on the initial slice. -/
private theorem alphaNumerator_zero_time (x y z : ℝ) :
    alphaNumerator x y z 0 = ((x ^ 2 + y ^ 2 + z ^ 2 - 1 : ℝ) : ℂ) + Complex.I * (2 * z : ℝ) := by
  unfold alphaNumerator radialAux
  congr 1
  push_cast
  ring

/-- In the stereographic chart the norm squared of the unpowered
Riemann–Silberstein field is `32 / (1 + |x|²)^4`. -/
theorem normSq_rationalField_zero_time (x y z : ℝ) :
    ∑ j : Fin 3, Complex.normSq (rationalField x y z 0 j) =
      32 / (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 4 := by
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let n := cross3 (alphaGradientNumerators x y z 0) (betaGradientNumerators x y z 0)
  have hd : 0 < d := by dsimp [d]; positivity
  let v : Fin 3 → ℂ :=
    ![((-1 - x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) + Complex.I * (2 * (z + x * y) : ℝ),
      ((2 * (z - x * y) : ℝ) : ℂ) + Complex.I * (1 - x ^ 2 + y ^ 2 - z ^ 2 : ℝ),
      ((-2 * (y + x * z) : ℝ) : ℂ) + Complex.I * (2 * (y * z - x) : ℝ)]
  have hv (j : Fin 3) : n j = (4 * (d : ℂ)) * v j := by
    fin_cases j <;> apply Complex.ext <;>
      simp [n, v, cross3, alphaGradientNumerators, betaGradientNumerators, alphaXNumerator,
        alphaYNumerator, alphaZNumerator, betaXNumerator, betaYNumerator, betaZNumerator,
        betaReducedNumerator, alphaCommonFactor, complexDenominator_zero_time, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im, pow_two, d] <;> ring
  have hvNorm : ∑ j : Fin 3, Complex.normSq (v j) = 2 * d ^ 2 := by
    simp [v, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, pow_two, d]
    ring
  have hn : ∑ j : Fin 3, Complex.normSq (n j) = 32 * d ^ 4 := by
    simp only [hv, Complex.normSq_mul, ← Finset.mul_sum, hvNorm]
    rw [show Complex.normSq (d : ℂ) = d ^ 2 by simp [Complex.normSq_apply, pow_two]]
    norm_num [Complex.normSq_apply]
    ring
  have h (j : Fin 3) : Complex.normSq (rationalField x y z 0 j) = Complex.normSq (n j) / d ^ 8 := by
    rw [rationalField_eq_cross_div, complexDenominator_zero_time, Complex.normSq_div, map_pow]
    change Complex.normSq (n j) / Complex.normSq (d : ℂ) ^ 4 = _
    rw [show Complex.normSq (d : ℂ) = d ^ 2 by simp [Complex.normSq_apply, pow_two],
      ← pow_mul]
  simp_rw [h, ← Finset.sum_div, hn]
  change 32 * d ^ 4 / d ^ 8 = 32 / d ^ 4
  field_simp [hd.ne']

/-- The initial pairing of the conjugate β gradient with the unpowered
field reduces to the first Bateman coordinate. -/
theorem conj_betaGradient_dot_rationalField_zero_time (x y z : ℝ) :
    dot3 (fun j => conj (betaGradient x y z 0 j)) (rationalField x y z 0) =
      16 * rationalAlpha x y z 0 / ((x ^ 2 + y ^ 2 + z ^ 2 + 1 : ℝ) : ℂ) ^ 3 := by
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let u := betaGradientNumerators x y z 0
  let n := cross3 (alphaGradientNumerators x y z 0) u
  have hd : 0 < d := by dsimp [d]; positivity
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hn : dot3 (fun j => conj (u j)) n = 16 * alphaNumerator x y z 0 * (d : ℂ) ^ 2 := by
    apply Complex.ext <;>
      simp [u, n, dot3, cross3, alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, betaReducedNumerator, alphaCommonFactor,
        alphaNumerator_zero_time, complexDenominator_zero_time, pow_two, Complex.conj_re,
        Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, pow_two, d] <;> ring
  have hα : rationalAlpha x y z 0 = alphaNumerator x y z 0 / (d : ℂ) := by
    rw [rational_alpha_stereographic_zero_time, alphaNumerator_zero_time]
  calc
    dot3 (fun j => conj (betaGradient x y z 0 j)) (rationalField x y z 0) =
        dot3 (fun j => conj (u j)) n / (d : ℂ) ^ 6 := by
      have hF (j : Fin 3) : rationalField x y z 0 j = n j / (d : ℂ) ^ 4 := by
        rw [rationalField_eq_cross_div, complexDenominator_zero_time]
      have hB (j : Fin 3) : betaGradient x y z 0 j = u j / (d : ℂ) ^ 2 := by
        unfold betaGradient
        rw [complexDenominator_zero_time]
      simp only [dot3, hB, hF, map_div₀, map_pow, Complex.conj_ofReal]
      field_simp [hdC]
    _ = _ := by
      rw [hn, hα]
      change 16 * alphaNumerator x y z 0 * (d : ℂ) ^ 2 / (d : ℂ) ^ 6 =
        16 * (alphaNumerator x y z 0 / (d : ℂ)) / (d : ℂ) ^ 3
      field_simp [hdC]

/-- The physical energy density is half the sum of the squared electric
and magnetic lengths. Its initial expression separates the two sphere
coordinates from the stereographic radial weight. -/
theorem rationalPowerField_energy_density_zero_time (p q : ℕ) (x y z : ℝ) :
    (∑ j : Fin 3, Complex.normSq (rationalPowerField p q x y z 0 j)) / 2 =
      16 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
        Complex.normSq (rationalAlpha x y z 0) ^ (p - 1) *
        Complex.normSq (rationalBeta x y z 0) ^ (q - 1) /
        (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 4 := by
  simp only [rationalPowerField_eq, Complex.normSq_mul, ← Finset.mul_sum,
    normSq_rationalField_zero_time, rationalPowerFactor, map_pow]
  rw [show Complex.normSq (p : ℂ) = (p : ℝ) ^ 2 by simp [Complex.normSq_apply, pow_two],
    show Complex.normSq (q : ℂ) = (q : ℝ) ^ 2 by simp [Complex.normSq_apply, pow_two]]
  ring

/-- The actual initial electric helicity density is a nonnegative
stereographic weight times the two powered sphere coordinates. -/
theorem batemanElectricHelicityDensity_zero_time (p q : ℕ) (x y z : ℝ) :
    batemanElectricHelicityDensity p q 0 (x, y, z) =
      8 * (p : ℝ) * (q : ℝ) ^ 2 *
        Complex.normSq (rationalAlpha x y z 0) ^ p *
        Complex.normSq (rationalBeta x y z 0) ^ (q - 1) /
        (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 3 := by
  rw [bateman_helicity_eq_hermitian]
  let a := rationalAlpha x y z 0
  let b := rationalBeta x y z 0
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let S := conj (a ^ p) * ((p : ℂ) * a ^ (p - 1)) *
    ((Complex.normSq (((q : ℂ) * b ^ (q - 1))) : ℝ) : ℂ)
  have hg : ∀ j : Fin 3, batemanPotential p q 0 (x, y, z) (batemanAxis j) =
      a ^ p * (((q : ℂ) * b ^ (q - 1)) * betaGradient x y z 0 j) := by
    intro j
    simp [batemanPotential, batemanAlphaPower, batemanPairAt,
      smul_eq_mul, fderiv_batemanBetaPower_axis, betaPowerGradient_eq, a, b]
  have hPair :
      dot3 (fun j => conj (batemanPotential p q 0 (x, y, z) (batemanAxis j)))
        (rationalPowerField p q x y z 0) =
      S * dot3 (fun j => conj (betaGradient x y z 0 j)) (rationalField x y z 0) := by
    unfold S
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [dot3, hg, rationalPowerField_eq, rationalPowerFactor, map_mul, a, b]
    ring
  rw [hPair, conj_betaGradient_dot_rationalField_zero_time]
  have ha : conj (a ^ p) * ((p : ℂ) * a ^ (p - 1)) * a =
      (p : ℂ) * ((Complex.normSq a : ℂ) ^ p) := by
    cases p with
    | zero => simp
    | succ p =>
      rw [Complex.normSq_eq_conj_mul_self, mul_pow, map_pow]
      simp only [Nat.add_one_sub_one]
      rw [pow_succ a]
      ring
  have hq : (Complex.normSq ((q : ℂ) * b ^ (q - 1)) : ℂ) =
      ((q : ℝ) ^ 2 * Complex.normSq b ^ (q - 1) : ℝ) := by
    rw [Complex.normSq_mul, map_pow]
    congr 1
    simp [Complex.normSq_apply, pow_two]
  change (S * (16 * a / (d : ℂ) ^ 3)).re / 2 = _
  have hS : S * (16 * a / (d : ℂ) ^ 3) =
      ((16 * (p : ℝ) * (q : ℝ) ^ 2 * Complex.normSq a ^ p *
        Complex.normSq b ^ (q - 1) / d ^ 3 : ℝ) : ℂ) := by
    calc
      _ = (conj (a ^ p) * ((p : ℂ) * a ^ (p - 1)) * a) *
          (Complex.normSq ((q : ℂ) * b ^ (q - 1)) : ℂ) * 16 / (d : ℂ) ^ 3 := by
            unfold S
            ring
      _ = _ := by
        rw [ha, hq]
        push_cast
        ring
  rw [hS, Complex.ofReal_re]
  change _ = 8 * (p : ℝ) * (q : ℝ) ^ 2 * Complex.normSq a ^ p * Complex.normSq b ^ (q - 1) / d ^ 3
  ring

/-- The magnetic initial helicity density has the same stereographic expression. -/
theorem batemanMagneticHelicityDensity_zero_time (p q : ℕ) (x y z : ℝ) :
    batemanMagneticHelicityDensity p q 0 (x, y, z) =
      8 * (p : ℝ) * (q : ℝ) ^ 2 *
        Complex.normSq (rationalAlpha x y z 0) ^ p *
        Complex.normSq (rationalBeta x y z 0) ^ (q - 1) /
        (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 3 := by
  rw [← bateman_electric_helicity_eq_magnetic, batemanElectricHelicityDensity_zero_time]

end Qatlib.Papers.KnotLight13.TorusFamily
