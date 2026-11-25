/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Forrelation14.MainResults.ForrelationModel

@[expose] public section

/-!
# Walsh moments for Section 8

The uniform average makes the Boolean monomials orthonormal. Variance
therefore omits the constant coefficient, and the squared change under
a sign flip contributes a factor of four to the influence.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Qatlib.Papers.Forrelation14.MainResults.Model

namespace Qatlib.Papers.Forrelation14.MainResults

variable {n : ℕ}

/-- The Boolean monomial indexed by a set of coordinates. -/
private def monomial (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, sign (x i)

/-- Flipping one coordinate negates a monomial precisely when it contains that coordinate. -/
private theorem monomial_flip (S : Finset (Fin n)) (x : Cube n) (i : Fin n) :
    monomial S (flipCoord x i) = if i ∈ S then -monomial S x else monomial S x := by
  unfold monomial
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, ← Finset.prod_erase_mul S _ hi, ← Finset.prod_erase_mul S _ hi]
    have hprod : (∏ j ∈ S.erase i, sign (flipCoord x i j)) = ∏ j ∈ S.erase i, sign (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [flipCoord, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hi' : sign (flipCoord x i i) = -sign (x i) := by
      cases h : x i <;> simp [flipCoord, h]
    rw [hprod, hi', mul_neg]
  · rw [ite_eq_right hi]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : j ≠ i := fun h => hi (h ▸ hj)
    simp [flipCoord, Function.update_of_ne hj']

/-- Flipping a coordinate twice gives the original input, so the flip permutes the cube. -/
private theorem flip_involutive (i : Fin n) : Function.Involutive (fun x : Cube n => flipCoord x i) := by
  intro x
  ext j
  by_cases h : j = i
  · subst j
    simp [flipCoord]
  · simp [flipCoord, Function.update_of_ne h]

/-- Two Boolean monomials have uniform inner product one exactly on the diagonal. -/
private theorem cubeAverage_monomial_mul (S T : Finset (Fin n)) :
    cubeAverage n (fun x => monomial S x * monomial T x) = if S = T then 1 else 0 := by
  classical
  unfold cubeAverage
  by_cases h : S = T
  · subst T
    rw [ite_eq_left rfl]
    have hone (x : Cube n) : monomial S x * monomial S x = 1 := by
      unfold monomial
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      cases x i <;> simp
    simp_rw [hone]
    simp [Cube, nsmul_eq_mul, div_self]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_contra! hn
      apply h
      ext i
      specialize hn i
      tauto
    let f : Cube n → ℝ := fun x => monomial S x * monomial T x
    let e : Cube n ≃ Cube n := (flip_involutive i).toPerm _
    have hflip (x : Cube n) : f (e x) = -f x := by
      change monomial S (flipCoord x i) * monomial T (flipCoord x i) = _
      rw [monomial_flip, monomial_flip]
      rcases hi with ⟨hS, hT⟩ | ⟨hT, hS⟩ <;> simp [f, hS, hT]
    have hsum := Equiv.sum_comp e f
    simp_rw [hflip, Finset.sum_neg_distrib] at hsum
    have hzero : ∑ x, f x = 0 := by linarith only [hsum]
    change (∑ x, f x) / (2 : ℝ) ^ n = 0
    rw [hzero, zero_div]

/-- Parseval on a finite set of Boolean monomials with arbitrary real coefficients. -/
private theorem cubeAverage_square (support : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℝ) :
    cubeAverage n (fun x => (∑ S ∈ support, c S * monomial S x) ^ 2) =
      ∑ S ∈ support, c S ^ 2 := by
  classical
  unfold cubeAverage
  calc
    _ = (∑ x : Cube n, ∑ S ∈ support, ∑ T ∈ support,
        (c S * c T) * (monomial S x * monomial T x)) / (2 : ℝ) ^ n := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      dsimp only
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ = ∑ S ∈ support, ∑ T ∈ support,
        (c S * c T) * cubeAverage n (fun x => monomial S x * monomial T x) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro T _
      rw [← Finset.mul_sum, mul_div_assoc, cubeAverage]
    _ = _ := by
      simp_rw [cubeAverage_monomial_mul, mul_ite, mul_zero, mul_one]
      apply Finset.sum_congr rfl
      intro S hS
      simp [hS, sq]

/-- The uniform mean of a cube polynomial is its constant coefficient. -/
theorem cubePolynomial_average (p : CubePolynomial n) : cubeAverage n p.eval = p.coeff ∅ := by
  classical
  unfold cubeAverage CubePolynomial.eval
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [← Finset.mul_sum, mul_div_assoc]
  have hmean (S : Finset (Fin n)) : (∑ x : Cube n, monomial S x) / (2 : ℝ) ^ n =
      if S = ∅ then 1 else 0 := by
    simpa [cubeAverage, monomial] using cubeAverage_monomial_mul S ∅
  change (∑ S ∈ p.support, p.coeff S * ((∑ x : Cube n, monomial S x) / (2 : ℝ) ^ n)) = _
  simp_rw [hmean, mul_ite, mul_zero, mul_one]
  rw [Finset.sum_ite_eq']
  by_cases h : ∅ ∈ p.support
  · simp [h]
  · have hz : p.coeff ∅ = 0 := by by_contra hn; exact h (p.support_spec ∅ hn)
    simp [h, hz]

/-- Centering the polynomial removes the monomial with empty support. -/
private theorem variance_eq_sum_erase (p : CubePolynomial n) :
    p.variance = ∑ S ∈ p.support.erase ∅, p.coeff S ^ 2 := by
  classical
  have hcenter (x : Cube n) : p.eval x - p.coeff ∅ =
      ∑ S ∈ p.support.erase ∅, p.coeff S * monomial S x := by
    by_cases h : ∅ ∈ p.support
    · have hs := Finset.sum_erase_add p.support (fun S => p.coeff S * monomial S x) h
      simp only [monomial, Finset.prod_empty, mul_one] at hs
      change (∑ S ∈ p.support, p.coeff S * monomial S x) - p.coeff ∅ = _
      simp only [monomial]
      linarith only [hs]
    · have hz : p.coeff ∅ = 0 := by by_contra hn; exact h (p.support_spec ∅ hn)
      simp [hz, Finset.erase_eq_of_notMem h, CubePolynomial.eval, monomial]
  rw [CubePolynomial.variance, cubePolynomial_average]
  simp_rw [hcenter]
  exact cubeAverage_square _ _

/-- Subtracting the constant part removes precisely its square from the Fourier variance. -/
theorem cubePolynomial_variance (p : CubePolynomial n) :
    p.variance = p.fourierVariance - p.coeff ∅ ^ 2 := by
  classical
  rw [variance_eq_sum_erase, CubePolynomial.fourierVariance]
  by_cases h : ∅ ∈ p.support
  · linarith only [Finset.sum_erase_add p.support (fun S => p.coeff S ^ 2) h]
  · have hz : p.coeff ∅ = 0 := by by_contra hn; exact h (p.support_spec ∅ hn)
    simp [hz, Finset.erase_eq_of_notMem h]

/-- A coordinate flip changes the sign of each containing term, so the
mean squared change is four times the sum of their squared coefficients. -/
theorem cubePolynomial_influence (p : CubePolynomial n) (i : Fin n) :
    p.influence i = 4 * p.fourierInfluence i := by
  classical
  have hflip (x : Cube n) : p.eval (flipCoord x i) - p.eval x =
      ∑ S ∈ p.support.filter (fun S => i ∈ S), (-2 * p.coeff S) * monomial S x := by
    change (∑ S ∈ p.support, p.coeff S * monomial S (flipCoord x i)) -
      (∑ S ∈ p.support, p.coeff S * monomial S x) = _
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    rw [monomial_flip]
    split <;> simp_all; ring
  unfold CubePolynomial.influence CubePolynomial.fourierInfluence
  simp_rw [hflip]
  rw [cubeAverage_square, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- The degree bound of Lemma 28 with influence normalized to the squared
half-difference, which is the convention of its Fourier formula. -/
theorem lemma28_normalized_influence (p : CubePolynomial n) :
    (∑ i, p.influence i / 4) ≤ (p.degree : ℝ) * p.variance := by
  classical
  have hnorm (i : Fin n) : p.influence i / 4 = p.fourierInfluence i := by
    rw [cubePolynomial_influence]
    ring
  simp_rw [hnorm]
  let q : CubePolynomial n := {
    coeff := fun S => if S = ∅ then 0 else p.coeff S
    support := p.support.erase ∅
    support_spec := by
      intro S hS
      by_cases h : S = ∅
      · simp [h] at hS
      · exact Finset.mem_erase.mpr ⟨h, p.support_spec S (by simpa [h] using hS)⟩
  }
  have hqv : q.fourierVariance = p.variance := by
    rw [variance_eq_sum_erase]
    apply Finset.sum_congr rfl
    intro S hS
    simp [q, (Finset.mem_erase.mp hS).1]
  have hqi (i : Fin n) : p.fourierInfluence i = q.fourierInfluence i := by
    have hset : p.support.filter (fun S => i ∈ S) = q.support.filter (fun S => i ∈ S) := by
      ext S
      by_cases h : S = ∅ <;> simp [q, h]
    unfold CubePolynomial.fourierInfluence
    rw [hset]
    apply Finset.sum_congr rfl
    intro S hS
    have h := (Finset.mem_filter.mp hS).2
    have hne : S ≠ ∅ := by intro heq; simp [heq] at h
    simp [q, hne]
  simp_rw [hqi]
  have hd : q.degree ≤ p.degree := Finset.sup_mono (Finset.erase_subset _ _)
  have hv : 0 ≤ p.variance := by
    rw [variance_eq_sum_erase]
    exact Finset.sum_nonneg fun S _ => sq_nonneg _
  exact (Qatlib.Papers.Forrelation14.MainResults.sum_influence_le_degree_mul_variance n q).trans
    (by rw [hqv]; gcongr)

end Qatlib.Papers.Forrelation14.MainResults
