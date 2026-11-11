/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.PolynomialDomainRescalingStat
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Rescaling the domain of Chebyshev expansions

This module converts the half-weighted Chebyshev convention to ordinary polynomial evaluation
and constructs coefficients for composition with twice the variable. The construction preserves
the coefficient-vector length, relates interval suprema, and gives the corresponding
matrix-evaluation identity. Related mathematical background is given in [LowSu2026].

## Main statements

* `exists_cheb_coeff`: Chebyshev representation after composition with twice the variable.
* `Clause27PolynomialDomainRescaling_answer`: Scalar, supremum, and matrix rescaling identities.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

open Polynomial Polynomial.Chebyshev Matrix Module Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Twice the variable times a first-kind Chebyshev polynomial equals the sum of its two
adjacent-index Chebyshev polynomials. -/
private theorem two_mul_X_mul_T (j : ℤ) :
    2 * X * T ℂ j = T ℂ (j + 1) + T ℂ (j - 1) := by
  have h := T_mul_T ℂ 1 j
  simp only [T_one] at h
  have hneg : T ℂ (1 - j) = T ℂ (j - 1) := by
    have hj : (1 - j : ℤ) = -(j - 1) := by ring
    rw [hj, T_neg]
  rw [add_comm 1 j, hneg] at h
  exact h

/-- The recursive real Chebyshev value agrees with complex evaluation of the corresponding
first-kind polynomial. -/
private theorem chebT_eq_eval (x : ℝ) (k : ℕ) :
    ((chebT x k : ℝ) : ℂ) = (T ℂ (k : ℤ)).eval (x : ℂ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [chebT]
  | one => simp [chebT]
  | more k ih1 ih2 =>
    have hk2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by omega
    have hk1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
    rw [hk1] at ih2
    have hcheb : chebT x (k + 2) = 2 * x * chebT x (k + 1) - chebT x k := rfl
    rw [hcheb, hk2, T_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    rw [← ih2, ← ih1]
    push_cast
    ring

/-- Algebra evaluation of the polynomial twice the variable at a matrix gives twice that matrix. -/
private theorem aeval_two_mul_X {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) : aeval B (2 * X : ℂ[X]) = (2 : ℂ) • B := by
  have h2 : (2 : ℂ[X]) = C 2 := (Polynomial.C_ofNat 2).symm
  rw [h2, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- The matrix Chebyshev recurrence agrees with algebra evaluation of the first-kind Chebyshev
polynomial. -/
private theorem chebMatrix_eq_aeval {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (k : ℕ) :
    chebMatrix A k = aeval A (T ℂ (k : ℤ)) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [chebMatrix]
  | one => simp [chebMatrix]
  | more k ih1 ih2 =>
    have hk2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by omega
    have hk1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
    rw [hk1] at ih2
    have hcheb : chebMatrix A (k + 2) = (2 : ℂ) • (A * chebMatrix A (k + 1))
        - chebMatrix A k := rfl
    rw [hcheb, hk2, T_add_two]
    simp only [map_sub, map_mul, aeval_X]
    rw [← ih2, ← ih1]
    have h2 : aeval A ((2 : ℂ[X])) = (2 : ℂ) • (1 : Matrix I I ℂ) := by
      rw [(Polynomial.C_ofNat 2).symm, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one]
    rw [h2]
    simp only [smul_mul_assoc, one_mul]

/-- The standard Chebyshev coefficient vector obtained by halving the coefficient at index zero. -/
private def toStd {n : ℕ} (c : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if k.val = 0 then c k / 2 else c k

/-- The conversion to standard coefficients halves index zero and leaves every other coefficient
unchanged. -/
private theorem toStd_apply {n : ℕ} (c : Fin n → ℂ) (k : Fin n) :
    toStd c k = if k.val = 0 then c k / 2 else c k := rfl

/-- The half-weighted-convention coefficient vector obtained by doubling the standard
coefficient at index zero. -/
private def fromStd {n : ℕ} (d : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if k.val = 0 then 2 * d k else d k

/-- The conversion from standard coefficients doubles index zero and leaves every other
coefficient unchanged. -/
private theorem fromStd_apply {n : ℕ} (d : Fin n → ℂ) (k : Fin n) :
    fromStd d k = if k.val = 0 then 2 * d k else d k := rfl

/-- Converting from standard coefficients and then back to standard coefficients recovers the
original vector. -/
private theorem toStd_fromStd {n : ℕ} (d : Fin n → ℂ) : toStd (fromStd d) = d := by
  funext k
  by_cases hk : k.val = 0
  · simp only [toStd_apply, fromStd_apply, if_pos hk]
    field_simp
  · simp only [toStd_apply, fromStd_apply, if_neg hk]

/-- The polynomial given by the finite sum of standard coefficients times first-kind Chebyshev
polynomials. -/
private def chebPolyOf {n : ℕ} (d : Fin n → ℂ) : ℂ[X] :=
  ∑ k : Fin n, d k • T ℂ (k.val : ℤ)

/-- The half-weighted Chebyshev value equals polynomial evaluation after converting its
coefficients to the standard convention. -/
private theorem chebValue_eq {n : ℕ} (c : Fin n → ℂ) (x : ℝ) :
    chebValue c x = (chebPolyOf (toStd c)).eval (x : ℂ) := by
  rw [chebValue, chebPolyOf, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_smul, ← chebT_eq_eval]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk0 : k.val = 0
  · rw [if_pos hk0]
    have h0 : ((chebT x 0 : ℝ) : ℂ) = 1 := by simp [chebT]
    rw [hk0, h0, toStd_apply, hk0]
    simp only [if_true, smul_eq_mul, mul_one]
    field_simp
  · rw [if_neg hk0, toStd_apply, if_neg hk0]
    rfl

/-- The half-weighted matrix Chebyshev operator equals algebra evaluation of its
standard-coefficient polynomial. -/
private theorem chebOperator_eq {n : ℕ} (c : Fin n → ℂ)
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    chebOperator c A = aeval A (chebPolyOf (toStd c)) := by
  rw [chebOperator, chebPolyOf]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk0 : k.val = 0
  · rw [if_pos hk0]
    have h0 : T ℂ ((0 : ℕ) : ℤ) = 1 := by simp
    rw [hk0, h0, Polynomial.aeval_one]
    rw [toStd_apply, hk0]
    simp only [if_true]
    rw [smul_smul]
    rw [show (c k * (1 / 2 : ℂ)) = c k / 2 by field_simp]
  · rw [if_neg hk0, toStd_apply, if_neg hk0, chebMatrix_eq_aeval]

/-- The polynomial represented by a coefficient vector of length `n` has degree strictly less
than `n`. -/
private theorem chebPolyOf_degree_lt {n : ℕ} (d : Fin n → ℂ) :
    (chebPolyOf d).degree < n := by
  rw [chebPolyOf]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  by_cases hn : n = 0
  · subst hn
    simp
  · have hsup : (Finset.univ : Finset (Fin n)).sup
        (fun k => (d k • T ℂ (k.val : ℤ)).degree) ≤ ((n - 1 : ℕ) : WithBot ℕ) := by
      apply Finset.sup_le
      intro k _
      calc (d k • T ℂ (k.val : ℤ)).degree ≤ (T ℂ (k.val : ℤ)).degree :=
          Polynomial.degree_smul_le _ _
        _ = ((k.val : ℤ).natAbs : WithBot ℕ) := degree_T _ _
        _ = (k.val : WithBot ℕ) := by norm_cast
        _ ≤ ((n - 1 : ℕ) : WithBot ℕ) := by
          norm_cast
          omega
    refine lt_of_le_of_lt hsup ?_
    norm_cast
    omega

/-- Composing the represented Chebyshev polynomial with twice the variable leaves its degree
strictly less than the coefficient-vector length. -/
private theorem comp_degree_lt {n : ℕ} (d : Fin n → ℂ) :
    ((chebPolyOf d).comp (2 * X)).degree < n := by
  by_cases h : (chebPolyOf d) = 0
  · rw [h, zero_comp]
    simp
  · have hnd : (chebPolyOf d).natDegree < n := by
      rw [Polynomial.natDegree_lt_iff_degree_lt h]
      exact chebPolyOf_degree_lt d
    have h2 : (2 * X : ℂ[X]).natDegree = 1 := by simp
    have hcomp : ((chebPolyOf d).comp (2 * X)).natDegree
        ≤ (chebPolyOf d).natDegree * (2 * X : ℂ[X]).natDegree :=
      Polynomial.natDegree_comp_le
    rw [h2, mul_one] at hcomp
    have h4 : ((chebPolyOf d).comp (2 * X)).degree
        ≤ (((chebPolyOf d).comp (2 * X)).natDegree : WithBot ℕ) :=
      Polynomial.degree_le_natDegree
    refine lt_of_le_of_lt h4 ?_
    exact_mod_cast lt_of_le_of_lt hcomp hnd

/-- The polynomial obtained by composing the input Chebyshev expansion with twice the variable
has a standard Chebyshev coefficient vector of the same length. -/
private theorem exists_cheb_coeff {n : ℕ} (c : Fin n → ℂ) :
    ∃ e : Fin n → ℂ, chebPolyOf e = (chebPolyOf (toStd c)).comp (2 * X) := by
  set S : Polynomial.Sequence ℂ := chebyshevTsequence ℂ with hS
  have hCoeff : ∀ i, IsUnit (S i).leadingCoeff := by
    intro i
    have h : (S i).leadingCoeff = 2 ^ (i - 1) := by
      rw [hS]
      simp [chebyshevTsequence, chebyshevTSequence, leadingCoeff_T]
    rw [h]
    exact (isUnit_iff_ne_zero.mpr two_ne_zero).pow _
  set B : Basis ℕ ℂ ℂ[X] := S.basis hCoeff with hB
  set p : ℂ[X] := (chebPolyOf (toStd c)).comp (2 * X) with hp
  have deg_p : p.degree < n := by rw [hp]; exact comp_degree_lt _
  have hvanish : ∀ i, n ≤ i → B.repr p i = 0 := by
    intro i hi
    have hp' : p ∈ degreeLT ℂ i :=
      mem_degreeLT.mpr (lt_of_lt_of_le deg_p (by exact_mod_cast hi))
    have hspan : p ∈ Submodule.span ℂ (S '' Set.Iio i) := by
      rw [S.span_degreeLT (fun j _ => hCoeff j)]
      exact hp'
    have hcoord : ∀ x ∈ Submodule.span ℂ (S '' Set.Iio i), B.coord i x = 0 := by
      apply Submodule.span_induction
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := hx
        have hjne : j ≠ i := ne_of_lt (Set.mem_Iio.mp hj)
        rw [hB]
        rw [← S.basis_eq_self hCoeff j]
        rw [Basis.coord_apply, Basis.repr_self_apply, if_neg hjne]
      · simp
      · intro x y _ _ hx hy
        rw [map_add, hx, hy, add_zero]
      · intro a x _ hx
        rw [map_smul, hx, smul_zero]
    exact hcoord p hspan
  refine ⟨fun k => B.repr p k.val, ?_⟩
  rw [chebPolyOf]
  have hrepr : p = (B.repr p).sum (fun i a => a • B i) := by
    conv_rhs => rw [← Finsupp.linearCombination_apply, ← B.repr_symm_apply]
    rw [B.repr.symm_apply_apply]
  have hsupp : (B.repr p).support ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_range]
    by_contra! h
    exact absurd (hvanish i h) (Finsupp.mem_support_iff.mp hi)
  have hsum : p = ∑ i ∈ Finset.range n, B.repr p i • B i := by
    conv_lhs => rw [hrepr]
    rw [Finsupp.sum]
    refine Finset.sum_subset hsupp ?_
    intro i _ hi
    have hi0 : B.repr p i = 0 := by
      simpa [Finsupp.mem_support_iff] using! hi
    simp [hi0]
  conv_rhs => rw [hsum]
  conv_rhs =>
    rw [← Fin.sum_univ_eq_sum_range (fun i => B.repr p i • B i)]
  apply Finset.sum_congr rfl
  intro k _
  rw [show B k.val = T ℂ (k.val : ℤ) by
      rw [hB, S.basis_eq_self hCoeff, hS]
      simp [chebyshevTsequence, chebyshevTSequence]]

/-- Every finite Chebyshev expansion can be rescaled by twice its argument with the same
coefficient-vector length, preserving the stated interval supremum and matrix-evaluation
identities. -/
theorem Clause27PolynomialDomainRescaling_answer : Clause27PolynomialDomainRescaling := by
  intro n c
  obtain ⟨e, he⟩ := exists_cheb_coeff c
  have hval : ∀ x : ℝ, chebValue (fromStd e) x = chebValue c (2 * x) := by
    intro x
    rw [chebValue_eq, toStd_fromStd, he, Polynomial.eval_comp]
    have heval : (Polynomial.eval (x : ℂ) (2 * X : ℂ[X])) = (2 : ℂ) * (x : ℂ) := by
      simp [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    rw [heval]
    have hcast : ((2 * x : ℝ) : ℂ) = (2 : ℂ) * (x : ℂ) := by push_cast; rfl
    rw [← hcast, ← chebValue_eq]
  refine ⟨fromStd e, hval, ?_, ?_⟩
  · show polynomialSup (fromStd e) (1 / 2) = polynomialSup c 1
    rw [polynomialSup, polynomialSup]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hy
      obtain ⟨x, hx1, hx2, hxy⟩ := hy
      refine ⟨2 * x, by linarith, by linarith, ?_⟩
      rw [hxy, hval]
    · intro hy
      obtain ⟨z, hz1, hz2, hzy⟩ := hy
      refine ⟨z / 2, by linarith, by linarith, ?_⟩
      rw [hzy, hval]
      congr 1
      field_simp
  · intro I _ _ A αA hαA
    rw [chebOperator_eq, toStd_fromStd, he, chebOperator_eq]
    rw [Polynomial.aeval_comp, aeval_two_mul_X, smul_smul]
    congr 1
    congr 1
    field_simp

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
