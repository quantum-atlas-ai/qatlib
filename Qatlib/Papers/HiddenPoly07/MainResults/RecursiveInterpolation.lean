/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-!
# Recursive interpolation and polynomial slices

This module defines the geometric-sum interpolation cost `kappa` and proves that it equals the
recursive cost `schemeCost`. It also constructs polynomial slices and coefficient polynomials,
establishing the degree estimates and slice-agreement criterion `eq_of_slice_agreement` used in
recursive interpolation.

The development follows [DeckerDraismaWocjan2009].

## Main statements

* `schemeCost_eq_kappa`: The recursively defined interpolation cost equals the geometric sum
  `kappa` in every dimension.
* `natDegree_coeffPoly_le`: If `Q` has total degree at most n, the coefficient polynomial for
  `α` has natural degree at most n minus the total exponent of `α`.
* `eq_of_slice_agreement`: Two polynomials of total degree at most n ≥ 1 are equal if their
  zero-monomial coefficient polynomials agree and all nonzero-monomial slice coefficients agree
  at n distinct parameters.

## References

* [Decker et al., 2009][DeckerDraismaWocjan2009]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HiddenPoly07.MainResults

/-- The geometric sum of n^j for 0 ≤ j < m, representing the recursive interpolation cost. -/
def kappa (n m : ℕ) : ℕ := ∑ j ∈ Finset.range m, n ^ j

/-- The interpolation cost with zero variables is zero. -/
theorem kappa_zero (n : ℕ) : kappa n 0 = 0 := by
  simp [kappa]

/-- The interpolation cost with one variable is one. -/
theorem kappa_one (n : ℕ) : kappa n 1 = 1 := by
  simp [kappa]

/-- The geometric-sum cost satisfies `kappa n (m + 1) = 1 + n * kappa n m`. -/
theorem kappa_succ (n m : ℕ) : kappa n (m + 1) = 1 + n * kappa n m := by
  have h1 : kappa n (m + 1) = (∑ j ∈ Finset.range m, n ^ (j + 1)) + 1 := by
    rw [kappa, Finset.sum_range_succ']
    simp
  have h2 : (∑ j ∈ Finset.range m, n ^ (j + 1)) = ∑ j ∈ Finset.range m, n * n ^ j :=
    Finset.sum_congr rfl fun j _ => by rw [pow_succ', mul_comm]
  rw [h1, h2, kappa, Finset.mul_sum, Nat.add_comm]

/-- Over the integers, multiplying `kappa n m` by n − 1 and adding one gives n^m. -/
theorem kappa_mul_pred_add_one (n m : ℕ) :
    (kappa n m : ℤ) * ((n : ℤ) - 1) + 1 = (n : ℤ) ^ m := by
  induction m with
  | zero => simp [kappa_zero]
  | succ m ih =>
    have hk : (kappa n (m + 1) : ℤ) = 1 + (n : ℤ) * (kappa n m : ℤ) := by
      rw [kappa_succ]
      push_cast
      ring
    rw [hk, pow_succ]
    linear_combination (n : ℤ) * ih

/-- The recursive cost with values zero and one in dimensions zero and one, and recurrence
c(m+2) = 1 + n c(m+1). -/
def schemeCost (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | m + 2 => 1 + n * schemeCost n (m + 1)

/-- The recursively defined interpolation cost equals the geometric sum `kappa` in every
dimension ([Lemma 2.4][DeckerDraismaWocjan2009]). -/
theorem schemeCost_eq_kappa (n m : ℕ) : schemeCost n m = kappa n m := by
  induction m with
  | zero => simp [schemeCost, kappa_zero]
  | succ m ih =>
    rcases m with _ | m
    · simp [schemeCost, kappa_one]
    · simp only [schemeCost, ih, ← kappa_succ]

/-- The univariate polynomial obtained by extracting the coefficient of the multivariate
monomial `α` from every coefficient of `p`. -/
def coeffPoly {R : Type*} [CommSemiring R] {k : ℕ} (α : Fin k →₀ ℕ)
    (p : Polynomial (MvPolynomial (Fin k) R)) : Polynomial R :=
  ∑ i ∈ p.support, Polynomial.monomial i ((p.coeff i).coeff α)

/-- The i-th coefficient of `coeffPoly α p` is the coefficient of `α` in the i-th coefficient of
`p`. -/
theorem coeff_coeffPoly {R : Type*} [CommSemiring R] {k : ℕ} (α : Fin k →₀ ℕ)
    (p : Polynomial (MvPolynomial (Fin k) R)) (i : ℕ) :
    Polynomial.coeff (coeffPoly α p) i = (Polynomial.coeff p i).coeff α := by
  classical
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  by_cases hi : i ∈ p.support
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [Polynomial.coeff_monomial, if_neg hb]
    · intro h
      exact absurd hi h
  · have hzero : p.coeff i = 0 := by
      simp only [Polynomial.mem_support_iff, ne_eq, not_not] at hi
      exact hi
    have hz : (∑ b ∈ p.support, (Polynomial.monomial b ((p.coeff b).coeff α)).coeff i) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hbne : ¬ (b = i) := by
        rintro rfl
        exact hi hb
      rw [Polynomial.coeff_monomial, if_neg hbne]
    rw [hz, hzero]
    simp

/-- The polynomial in k variables obtained by specializing the distinguished variable of `Q`, as
selected by `MvPolynomial.finSuccEquiv`, to `t`. -/
def slicePoly {F : Type*} [CommSemiring F] {k : ℕ} (Q : MvPolynomial (Fin (k + 1)) F)
    (t : F) : MvPolynomial (Fin k) F :=
  Polynomial.eval₂ (RingHom.id (MvPolynomial (Fin k) F)) (MvPolynomial.C t)
    (MvPolynomial.finSuccEquiv F k Q)

/-- Expresses `slicePoly Q t` as the sum of the coefficient polynomials of
`MvPolynomial.finSuccEquiv F k Q` weighted by powers of `t`. -/
theorem slicePoly_eq_sum {F : Type*} [CommSemiring F] {k : ℕ}
    (Q : MvPolynomial (Fin (k + 1)) F) (t : F) :
    slicePoly Q t
      = ∑ i ∈ (MvPolynomial.finSuccEquiv F k Q).support,
          MvPolynomial.C (t ^ i) * Polynomial.coeff (MvPolynomial.finSuccEquiv F k Q) i := by
  rw [slicePoly, Polynomial.eval₂_eq_eval_map, Polynomial.map_id, Polynomial.eval_eq_sum,
    Polynomial.sum_def]
  exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.C_pow, mul_comm]

/-- Evaluating `coeffPoly α p` at `t` gives the sum of the extracted coefficients multiplied by
the corresponding powers of `t`. -/
theorem eval_coeffPoly {F : Type*} [CommSemiring F] {k : ℕ} (α : Fin k →₀ ℕ)
    (p : Polynomial (MvPolynomial (Fin k) F)) (t : F) :
    Polynomial.eval t (coeffPoly α p)
      = ∑ i ∈ p.support, (p.coeff i).coeff α * t ^ i := by
  rw [coeffPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_monomial]

/-- The coefficient of `α` in a slice is the evaluation at the slice parameter of the associated
coefficient polynomial. -/
theorem coeff_slicePoly {F : Type*} [CommSemiring F] {k : ℕ}
    (Q : MvPolynomial (Fin (k + 1)) F) (t : F) (α : Fin k →₀ ℕ) :
    (slicePoly Q t).coeff α
      = Polynomial.eval t (coeffPoly α (MvPolynomial.finSuccEquiv F k Q)) := by
  rw [slicePoly_eq_sum, MvPolynomial.coeff_sum, eval_coeffPoly]
  exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.coeff_C_mul, mul_comm]

/-- Every coefficient in the univariate presentation of `Q` has total degree at most the total
degree of `Q`. -/
theorem totalDegree_coeff_finSuccEquiv_le {F : Type*} [CommSemiring F] {k : ℕ}
    (Q : MvPolynomial (Fin (k + 1)) F) (i : ℕ) :
    (Polynomial.coeff (MvPolynomial.finSuccEquiv F k Q) i).totalDegree ≤ Q.totalDegree := by
  classical
  by_cases hQ : Q = 0
  · simp [hQ]
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro β hβ
  have hcoeff : Q.coeff (β.cons i) ≠ 0 := by
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff]
    exact Finsupp.mem_support_iff.mp hβ
  have hmem : β.cons i ∈ Q.support := Finsupp.mem_support_iff.mpr hcoeff
  have := MvPolynomial.le_totalDegree hmem
  rw [Finsupp.sum_cons] at this
  exact le_trans (Nat.le_add_left _ _) this

/-- Specializing the distinguished variable does not increase total degree. -/
theorem totalDegree_slicePoly_le {F : Type*} [CommSemiring F] {k : ℕ}
    (Q : MvPolynomial (Fin (k + 1)) F) (t : F) :
    (slicePoly Q t).totalDegree ≤ Q.totalDegree := by
  rw [slicePoly_eq_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  exact totalDegree_coeff_finSuccEquiv_le Q i

/-- The constant coefficient of the slice at zero equals the constant coefficient of the
original polynomial. -/
theorem coeff_slicePoly_zero {F : Type*} [CommSemiring F] {k : ℕ}
    (Q : MvPolynomial (Fin (k + 1)) F) :
    (slicePoly Q 0).coeff 0 = Q.coeff 0 := by
  classical
  rw [coeff_slicePoly, eval_coeffPoly]
  by_cases h0 : 0 ∈ (MvPolynomial.finSuccEquiv F k Q).support
  · rw [Finset.sum_eq_single 0]
    · rw [pow_zero, mul_one, MvPolynomial.finSuccEquiv_coeff_coeff]
      simp
    · intro b _ hb
      rw [zero_pow hb, mul_zero]
    · intro h
      exact absurd h0 h
  · have hz : (∑ i ∈ (MvPolynomial.finSuccEquiv F k Q).support,
        ((MvPolynomial.finSuccEquiv F k Q).coeff i).coeff 0 * 0 ^ i) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hbne : b ≠ 0 := by
        rintro rfl
        exact h0 hb
      rw [zero_pow hbne, mul_zero]
    have hp0 : (MvPolynomial.finSuccEquiv F k Q).coeff 0 = 0 := by
      simp only [Polynomial.mem_support_iff, ne_eq, not_not] at h0
      exact h0
    have hQ0 : Q.coeff 0 = 0 := by
      have h := MvPolynomial.finSuccEquiv_coeff_coeff (m := (0 : Fin k →₀ ℕ)) (f := Q) (i := 0)
      rw [hp0, Finsupp.cons_zero_zero] at h
      simpa using h.symm
    rw [hz, hQ0]

/-- Subtracting the constant coefficient from a slice gives a polynomial with zero constant
coefficient. -/
theorem coeff_sub_C_coeff_slicePoly {F : Type*} [Field F] {k : ℕ}
    (Q : MvPolynomial (Fin (k + 1)) F) (t : F) :
    (slicePoly Q t - MvPolynomial.C ((slicePoly Q t).coeff 0)).coeff 0 = 0 := by
  simp [MvPolynomial.coeff_C]

/-- A nonzero finitely supported exponent vector has total exponent at least one. -/
theorem one_le_sum_of_ne_zero {k : ℕ} {α : Fin k →₀ ℕ} (hα : α ≠ 0) :
    1 ≤ α.sum fun _ e => e := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hα
  have hpos : 0 < α i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hle : α i ≤ α.sum fun _ e => e := by
    rw [Finsupp.sum]
    exact Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) hi
  omega

/-- If `Q` has total degree at most n, the coefficient polynomial for `α` has natural degree at
most n minus the total exponent of `α`. -/
theorem natDegree_coeffPoly_le {F : Type*} [CommSemiring F] {k n : ℕ}
    (Q : MvPolynomial (Fin (k + 1)) F) (hQ : Q.totalDegree ≤ n) (α : Fin k →₀ ℕ) :
    (coeffPoly α (MvPolynomial.finSuccEquiv F k Q)).natDegree ≤ n - α.sum fun _ e => e := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_coeffPoly, MvPolynomial.finSuccEquiv_coeff_coeff]
  by_contra hne
  have hmem : Finsupp.cons N α ∈ Q.support := Finsupp.mem_support_iff.mpr hne
  have hle := MvPolynomial.le_totalDegree hmem
  rw [Finsupp.sum_cons] at hle
  omega

/-- Two polynomials of total degree at most n ≥ 1 are equal if their zero-monomial coefficient
polynomials agree and all nonzero-monomial slice coefficients agree at n distinct parameters
([Lemma 2.4][DeckerDraismaWocjan2009]). -/
theorem eq_of_slice_agreement {F : Type*} [Field F] {k n : ℕ} (hn : 1 ≤ n)
    (Q Q' : MvPolynomial (Fin (k + 1)) F) (hQ : Q.totalDegree ≤ n)
    (hQ' : Q'.totalDegree ≤ n) {s : Finset F} (hs : s.card = n)
    (haxis : coeffPoly (0 : Fin k →₀ ℕ) (MvPolynomial.finSuccEquiv F k Q)
      = coeffPoly (0 : Fin k →₀ ℕ) (MvPolynomial.finSuccEquiv F k Q'))
    (hslice : ∀ α : Fin k →₀ ℕ, α ≠ 0 → ∀ t ∈ s,
      (slicePoly Q t).coeff α = (slicePoly Q' t).coeff α) :
    Q = Q' := by
  classical
  apply (MvPolynomial.finSuccEquiv F k).injective
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro α
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    rw [← coeff_coeffPoly (α := (0 : Fin k →₀ ℕ)) (p := MvPolynomial.finSuccEquiv F k Q) (i := i),
      ← coeff_coeffPoly (α := (0 : Fin k →₀ ℕ)) (p := MvPolynomial.finSuccEquiv F k Q') (i := i)]
    exact congrArg (fun p => Polynomial.coeff p i) haxis
  · have hdeg1 : (coeffPoly α (MvPolynomial.finSuccEquiv F k Q)).natDegree ≤ n - 1 := by
      refine (natDegree_coeffPoly_le Q hQ α).trans ?_
      have := one_le_sum_of_ne_zero hα
      omega
    have hdeg2 : (coeffPoly α (MvPolynomial.finSuccEquiv F k Q')).natDegree ≤ n - 1 := by
      refine (natDegree_coeffPoly_le Q' hQ' α).trans ?_
      have := one_le_sum_of_ne_zero hα
      omega
    have hdeg : max (coeffPoly α (MvPolynomial.finSuccEquiv F k Q)).natDegree
        (coeffPoly α (MvPolynomial.finSuccEquiv F k Q')).natDegree < s.card := by
      rw [hs]
      omega
    have hval : ∀ t ∈ s,
        Polynomial.eval t (coeffPoly α (MvPolynomial.finSuccEquiv F k Q))
          = Polynomial.eval t (coeffPoly α (MvPolynomial.finSuccEquiv F k Q')) := by
      intro t ht
      rw [← coeff_slicePoly, ← coeff_slicePoly]
      exact hslice α hα t ht
    have heq := Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
      (coeffPoly α (MvPolynomial.finSuccEquiv F k Q))
      (coeffPoly α (MvPolynomial.finSuccEquiv F k Q')) s hval hdeg
    rw [← coeff_coeffPoly (α := α) (p := MvPolynomial.finSuccEquiv F k Q) (i := i),
      ← coeff_coeffPoly (α := α) (p := MvPolynomial.finSuccEquiv F k Q') (i := i),
      heq]

end Qatlib.Papers.HiddenPoly07.MainResults
