/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.Fourier

/-!
# Second moments of biased Fourier overlaps

Computes the second moment of the finite biased weights and relates it to the Gram overlaps of
`fourierUnitVec`. Column normalization separates the diagonal term, giving an off-diagonal
squared-overlap sum bounded by `2 * eps^2` for `q > 1` and `eps ∈ [0, 1]`. See [TangWright2025].

## Main statements

* `actual_weight_second_moment`: the exact second-moment formula for the biased weights.
* `actual_gram_second_moment`: the Gram-column squared norm equals the weight second moment.
* `actual_offdiag_budget`: the off-diagonal squared-overlap bound.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- For positive `q`, `q` times the sum of the squared biased weights equals `1 + eps^2 * (q /
halfCount q - 1)`. -/
theorem actual_weight_second_moment (q : ℕ) (hq : 0 < q) (eps : ℝ) :
    (q:ℝ) * ∑ g : Fin q, (muEpsWeight eps q g)^2 =
      1 + eps^2 * ((q:ℝ)/(halfCount q:ℝ)-1) := by
  have hN : (halfCount q : ℝ) ≠ 0 := by
    have : 0 < halfCount q := by unfold halfCount; omega
    exact_mod_cast this.ne'
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hterm : ∀ g : Fin q, (muEpsWeight eps q g)^2 =
      ((1-eps)*(q:ℝ)⁻¹)^2 +
        (2*((1-eps)*(q:ℝ)⁻¹)*(eps*(halfCount q:ℝ)⁻¹) +
          (eps*(halfCount q:ℝ)⁻¹)^2) * (if isRightHalf q g then 1 else 0) := by
    intro g
    unfold muEpsWeight
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_add_distrib,
    ← Finset.mul_sum, card_rightHalf q hq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- For `q > 1` and `eps ∈ [0, 1]`, the sum of squared overlaps with a fixed weighted Fourier
column equals `q` times the sum of squared biased weights. -/
theorem actual_gram_second_moment (q : ℕ) (hq : 1 < q) (eps : ℝ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1) (k : Fin q) :
    ∑ j : Fin q, ‖∑ g : Fin q,
      star (fourierUnitVec eps q j g) * fourierUnitVec eps q k g‖^2 =
      (q:ℝ) * ∑ g : Fin q, (muEpsWeight eps q g)^2 := by
  have hmu := muEpsWeight_nonneg q hq eps he0 he1
  have hsqrt : ∀ g : Fin q,
      (Real.sqrt (muEpsWeight eps q g):ℂ) *
        (Real.sqrt (muEpsWeight eps q g):ℂ) = (muEpsWeight eps q g:ℂ) := by
    intro g
    norm_cast
    nlinarith [Real.sq_sqrt (hmu g)]
  have hterm : ∀ j : Fin q,
      star (∑ g : Fin q, star (fourierUnitVec eps q j g) * fourierUnitVec eps q k g) =
        ∑ g : Fin q, omega q ^ ((j:ℕ)*(g:ℕ)) *
          ((muEpsWeight eps q g:ℂ) * star (phase q g ^ (k:ℕ))) := by
    intro j
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro g _
    simp only [fourierUnitVec, star_mul, Complex.star_def, map_pow,
      Complex.conj_ofReal, Complex.conj_conj]
    have hp : phase q g ^ (j:ℕ) = omega q ^ ((j:ℕ)*(g:ℕ)) := by
      simp only [phase, ← pow_mul, Nat.mul_comm]
    rw [hp]
    calc
      _ = ((Real.sqrt (muEpsWeight eps q g):ℂ) *
        (Real.sqrt (muEpsWeight eps q g):ℂ)) *
          (omega q ^ ((j:ℕ)*(g:ℕ)) * star (phase q g ^ (k:ℕ))) := by
            simp only [Complex.star_def, map_pow]; ring
      _ = _ := by rw [hsqrt]; simp only [Complex.star_def, map_pow]; ring
  have hdft := actual_dft_tight q (by omega)
    (fun g => (muEpsWeight eps q g:ℂ) * star (phase q g ^ (k:ℕ)))
  have hnorm : ∀ g : Fin q,
      ‖(muEpsWeight eps q g:ℂ) * star (phase q g ^ (k:ℕ))‖^2 =
        (muEpsWeight eps q g)^2 := by
    intro g
    rw [norm_mul, norm_star, norm_pow, norm_phase, one_pow, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun g _ => hnorm g)] at hdft
  rw [← hdft]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hterm j, norm_star]

/-- For `q > 1` and `eps ∈ [0, 1]`, each weighted Fourier column has total squared mass one. -/
theorem actual_column_norm (q : ℕ) (hq : 1 < q) (eps : ℝ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1) (k : Fin q) :
    ∑ g : Fin q, ‖fourierUnitVec eps q k g‖^2 = 1 := by
  have hmu := muEpsWeight_nonneg q hq eps he0 he1
  have hterm : ∀ g : Fin q, ‖fourierUnitVec eps q k g‖^2 = muEpsWeight eps q g := by
    intro g
    simp only [fourierUnitVec, norm_mul, norm_pow, norm_phase,
      one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt (hmu g)
  rw [Finset.sum_congr rfl (fun g _ => hterm g), sum_muEpsWeight q (by omega) eps he0 he1]

/-- For `q > 1` and `eps ∈ [0, 1]`, the inner product of a weighted Fourier column with itself
is one. -/
theorem actual_column_self (q : ℕ) (hq : 1 < q) (eps : ℝ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1) (k : Fin q) :
    (∑ g : Fin q, star (fourierUnitVec eps q k g) * fourierUnitVec eps q k g) = 1 := by
  have h : ∀ z : ℂ, star z*z=((‖z‖^2:ℝ):ℂ) := by
    intro z
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [h, ← Complex.ofReal_sum, actual_column_norm q hq eps he0 he1 k,
    Complex.ofReal_one]

/-- For `q > 1` and `eps ∈ [0, 1]`, the sum of squared overlaps of a fixed weighted Fourier
column with all other columns is at most `2 * eps^2`. -/
theorem actual_offdiag_budget (q : ℕ) (hq : 1 < q) (eps : ℝ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1) (k : Fin q) :
    ∑ j : Fin q, (if j ≠ k then ‖∑ g : Fin q,
      star (fourierUnitVec eps q j g) * fourierUnitVec eps q k g‖^2 else 0) ≤ 2*eps^2 := by
  let B := fun j : Fin q => ‖∑ g : Fin q,
      star (fourierUnitVec eps q j g) * fourierUnitVec eps q k g‖^2
  have hself : B k = 1 := by
    have h := actual_column_self q hq eps he0 he1 k
    calc
      B k = ‖(1:ℂ)‖^2 := congrArg (fun z : ℂ => ‖z‖^2) h
      _ = 1 := by norm_num
  have hsplit : (∑ j, B j) = 1 + ∑ j, (if j ≠ k then B j else 0) := by
    have heq : ∀ j : Fin q, B j = (if j=k then B j else 0) + (if j≠k then B j else 0) := by
      intro j
      by_cases h : j=k <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => heq j), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hself]
  have hm := actual_gram_second_moment q hq eps he0 he1 k
  change (∑ j, B j) = _ at hm
  rw [actual_weight_second_moment q (by omega) eps, hsplit] at hm
  have hN : 0 < (halfCount q:ℝ) := by
    have : 0 < halfCount q := by unfold halfCount; omega
    exact_mod_cast this
  have hqN : (q:ℝ) ≤ 3*(halfCount q:ℝ) := by
    have : q ≤ 3*halfCount q := by unfold halfCount; omega
    exact_mod_cast this
  have hratio : (q:ℝ)/(halfCount q:ℝ) ≤ 3 := (div_le_iff₀ hN).mpr hqN
  change (∑ j, if j≠k then B j else 0) ≤ _
  nlinarith [sq_nonneg eps]

end Qatlib.Papers.AmpInvReqTang26.BiasedFourier
