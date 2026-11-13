/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyNonlin25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Skew-Adjointness of Second-Quantized Drift and Cubic Kolmogorov Operators

This module formalizes Lemma 1: for the second-quantized Kolmogorov generator on
`N` bosonic modes, the quadratic drift operator `driftOp` is skew-adjoint whenever
its scaled drift coefficients are antisymmetric, and the reduced cubic operator
`cubicOp` is skew-adjoint termwise.

## Main statements

* `driftCoeff`, `driftOp`: scaled quadratic drift coefficients and operator `B`.
* `cubicCoeff`, `cubicOp`: scaled cubic coefficients and reduced cubic operator `C`.
* `lemma1_skewAdjoint`: `(driftOp a adag lam b)† = -driftOp a adag lam b` and
  `(cubicOp a adag lam q c)† = -cubicOp a adag lam q c`.

## References

* [Bravyi et al., 2025][BravyiEtAl2025NoisyNonlin], Lemma 1, Eqs. (20)--(22), pp. 11--12.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ComplexOrder InnerProduct
open Finset

namespace Qatlib.Papers.NoisyNonlin25.MainResults

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scaled drift coefficient `(λᵢ / λⱼ)^{1/2} bᵢⱼ`. -/
def driftCoeff {N : ℕ} (lam : Fin N → ℝ) (b : Fin N → Fin N → ℝ) (i j : Fin N) : ℂ :=
  ((b i j * Real.sqrt (lam i / lam j) : ℝ) : ℂ)

/-- The quadratic drift operator `B = ∑ᵢⱼ bᵢⱼ (λᵢ / λⱼ)^{1/2} aⱼ† aᵢ`. -/
def driftOp {N : ℕ} (a adag : Fin N → H →L[ℂ] H) (lam : Fin N → ℝ)
    (b : Fin N → Fin N → ℝ) : H →L[ℂ] H :=
  ∑ i, ∑ j, driftCoeff lam b i j • (adag j * a i)

/-- Cubic coefficient `(q / 2)^{1/2} (λᵢ λⱼ λₖ)^{-1/2} λᵢ cᵢⱼₖ`. -/
def cubicCoeff {N : ℕ} (lam : Fin N → ℝ) (q : ℝ) (c : Fin N → Fin N → Fin N → ℝ)
    (i j k : Fin N) : ℂ :=
  ((Real.sqrt (q / 2) * (Real.sqrt (lam i * lam j * lam k))⁻¹ * lam i * c i j k : ℝ) : ℂ)

/-- The reduced cubic operator
`C = (q / 2)^{1/2} ∑ᵢⱼₖ (λᵢ λⱼ λₖ)^{-1/2} λᵢ cᵢⱼₖ (aⱼ† aₖ† aᵢ - aᵢ† aₖ aⱼ)`. -/
def cubicOp {N : ℕ} (a adag : Fin N → H →L[ℂ] H) (lam : Fin N → ℝ) (q : ℝ)
    (c : Fin N → Fin N → Fin N → ℝ) : H →L[ℂ] H :=
  ∑ i, ∑ j, ∑ k, cubicCoeff lam q c i j k •
    ((adag j * adag k * a i) - (adag i * a k * a j))

/-- **Lemma 1**: under scaled drift antisymmetry `driftCoeff lam b i j + driftCoeff lam b j i = 0`
and adjoint pairing `(a i)† = adag i`, both `driftOp` and `cubicOp` are skew-adjoint. -/
theorem lemma1_skewAdjoint {N : ℕ} (a adag : Fin N → H →L[ℂ] H)
    (hadj : ∀ i, (a i)† = adag i) (lam : Fin N → ℝ) (hlam : ∀ i, 0 < lam i)
    (b : Fin N → Fin N → ℝ)
    (hskew : ∀ i j, driftCoeff lam b i j + driftCoeff lam b j i = 0)
    (q : ℝ) (hq : 0 < q) (c : Fin N → Fin N → Fin N → ℝ) :
    (driftOp (H := H) a adag lam b)† = -driftOp (H := H) a adag lam b ∧
    (cubicOp (H := H) a adag lam q c)† = -cubicOp (H := H) a adag lam q c := by
  have hstar_a : ∀ i, star (a i) = adag i := by
    intro i; rw [ContinuousLinearMap.star_eq_adjoint]; exact hadj i
  have hstar_adag : ∀ i, star (adag i) = a i := by
    intro i; rw [← hstar_a, star_star]
  constructor
  · change star (driftOp (H := H) a adag lam b) = -driftOp (H := H) a adag lam b
    unfold driftOp
    have hstar_coeff : ∀ (i j : Fin N),
        star (driftCoeff lam b i j) = driftCoeff lam b i j := by
      intro i j
      unfold driftCoeff
      rw [Real.sqrt_div (le_of_lt (hlam i)), Complex.star_def, Complex.conj_ofReal]
    simp only [star_sum, star_smul, star_mul, hstar_a, hstar_adag, hstar_coeff]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [eq_neg_of_add_eq_zero_left (hskew i j), neg_smul]
  · change star (cubicOp (H := H) a adag lam q c) = -cubicOp (H := H) a adag lam q c
    unfold cubicOp
    have hstar_coeff : ∀ (i j k : Fin N),
        star (cubicCoeff lam q c i j k) = cubicCoeff lam q c i j k := by
      intro i j k
      unfold cubicCoeff
      rw [Real.sqrt_div (le_of_lt hq), Complex.star_def, Complex.conj_ofReal]
    simp only [star_sum, star_smul, star_sub, star_mul, hstar_a, hstar_adag, hstar_coeff]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
      Finset.sum_congr rfl (fun z _ => ?_)))
    rw [← smul_neg, neg_sub]
    simp only [mul_assoc]

end Qatlib.Papers.NoisyNonlin25.MainResults
