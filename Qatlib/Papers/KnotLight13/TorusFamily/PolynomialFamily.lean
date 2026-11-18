/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.Bateman.Construction
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic.Positivity

/-!
# Sphere coordinates and weighted homogeneous torus polynomials

[Kedia2013TyingKnots], equations (5)–(6),
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
The time-dependent rational coordinates are represented by their common real
norm-square denominator. Their two squared moduli sum to one for every real
space-time point. Weighted homogeneous scaling of α^p − β^q and its explicit
algebraic parametrization are proved without identifying a knot type. This does
not prove the Brauner–Milnor classification, Maxwell evolution, or the spatial
integrals giving the energy-normalized helicities 1/(p+q).
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

/-- Twice the real auxiliary coordinate A of the Bateman rational pair. -/
def radialAux (x y z t : ℝ) : ℝ := x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 + 1

/-- Squared modulus of the common complex denominator 2(A + it). -/
def pairDenominator (x y z t : ℝ) : ℝ := radialAux x y z t ^ 2 + 4 * t ^ 2

/-- The explicit complex scalar α in the rational Bateman pair. -/
noncomputable def rationalAlpha (x y z t : ℝ) : ℂ :=
  ((radialAux x y z t - 2 : ℝ) + Complex.I * (2 * z : ℝ)) /
    ((radialAux x y z t : ℝ) + Complex.I * (2 * t : ℝ))

/-- The explicit complex scalar β in the rational Bateman pair. -/
noncomputable def rationalBeta (x y z t : ℝ) : ℂ :=
  (2 * (x : ℂ) - Complex.I * (2 * y : ℝ)) /
    ((radialAux x y z t : ℝ) + Complex.I * (2 * t : ℝ))

/-- The common denominator is strictly positive everywhere in real space-time. -/
theorem pair_denominator_pos (x y z t : ℝ) : 0 < pairDenominator x y z t := by
  unfold pairDenominator radialAux
  by_cases ht : t = 0
  · subst t
    have h : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by positivity
    nlinarith [sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2 + 1)]
  · have h : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 + 1)]

/-- Squared modulus of α = (A − 1 + iz)/(A + it). -/
noncomputable def alphaSquared (x y z t : ℝ) : ℝ :=
  ((radialAux x y z t - 2) ^ 2 + 4 * z ^ 2) / pairDenominator x y z t

/-- Squared modulus of β = (x − iy)/(A + it). -/
noncomputable def betaSquared (x y z t : ℝ) : ℝ :=
  (4 * (x ^ 2 + y ^ 2)) / pairDenominator x y z t

/-- The real α expression is the actual complex squared modulus of the rational scalar. -/
theorem rational_alpha_norm (x y z t : ℝ) :
    Complex.normSq (rationalAlpha x y z t) = alphaSquared x y z t := by
  simp [rationalAlpha, Complex.normSq_apply,
    alphaSquared, pairDenominator]
  congr 1 <;> ring

/-- The real β expression is the actual complex squared modulus of the rational scalar. -/
theorem rational_beta_norm (x y z t : ℝ) :
    Complex.normSq (rationalBeta x y z t) = betaSquared x y z t := by
  simp [rationalBeta, Complex.normSq_apply,
    betaSquared, pairDenominator]
  congr 1 <;> ring

/-- The rational pair satisfies |α|² + |β|² = 1 at every real time. -/
theorem rational_pair_unit (x y z t : ℝ) :
    alphaSquared x y z t + betaSquared x y z t = 1 := by
  have hd := ne_of_gt (pair_denominator_pos x y z t)
  unfold alphaSquared betaSquared
  rw [← add_div, div_eq_one_iff_eq hd]
  unfold pairDenominator radialAux
  ring

/-- The explicit complex pair lies on the unit three-sphere for all real space-time points. -/
theorem complex_rational_pair_unit (x y z t : ℝ) :
    Complex.normSq (rationalAlpha x y z t) + Complex.normSq (rationalBeta x y z t) = 1 := by
  rw [rational_alpha_norm, rational_beta_norm, rational_pair_unit]

/-- The two squared moduli are nonnegative, so the sphere identity is nonvacuous. -/
theorem rational_pair_nonnegative (x y z t : ℝ) :
    0 ≤ alphaSquared x y z t ∧ 0 ≤ betaSquared x y z t := by
  have hd := le_of_lt (pair_denominator_pos x y z t)
  constructor
  · unfold alphaSquared
    positivity
  · unfold betaSquared
    positivity

/-- The polynomial whose link on the three-sphere encodes the torus family. -/
def torusPolynomial (p q : ℕ) (alpha beta : ℂ) : ℂ := alpha ^ p - beta ^ q

/-- Weighted scaling has weight pq, including zero exponents. -/
theorem weighted_homogeneity (p q : ℕ) (lambda alpha beta : ℂ) :
    torusPolynomial p q (lambda ^ q * alpha) (lambda ^ p * beta) =
      lambda ^ (p * q) * torusPolynomial p q alpha beta := by
  simp only [torusPolynomial, mul_pow, ← pow_mul, Nat.mul_comm q p]
  ring

/-- The monomial parametrization lies in the polynomial zero set. -/
theorem parametrized_zero (p q : ℕ) (s : ℂ) :
    torusPolynomial p q (s ^ q) (s ^ p) = 0 := by
  simp [torusPolynomial, ← pow_mul, Nat.mul_comm]

/-- Weighted scaling preserves membership in the torus-polynomial zero set. -/
theorem scaled_zero (p q : ℕ) (lambda alpha beta : ℂ)
    (h : torusPolynomial p q alpha beta = 0) :
    torusPolynomial p q (lambda ^ q * alpha) (lambda ^ p * beta) = 0 := by
  rw [weighted_homogeneity, h, mul_zero]

end Qatlib.Papers.KnotLight13.TorusFamily
