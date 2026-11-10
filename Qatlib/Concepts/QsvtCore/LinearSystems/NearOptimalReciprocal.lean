/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalPolynomial
import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalApproximation
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.LinearSystems
open Polynomial
open scoped Classical BigOperators

def nearOptimalReciprocalB (κ ε : ℝ) : ℕ := Nat.ceil (κ*κ*Real.log (κ/ε))

def nearOptimalReciprocalJ (κ ε : ℝ) : ℕ :=
  Nat.ceil (Real.sqrt ((nearOptimalReciprocalB κ ε : ℝ)*
    Real.log (4*(nearOptimalReciprocalB κ ε : ℝ)/ε)))

def nearOptimalReciprocalPolynomial (κ ε : ℝ) : Polynomial ℝ :=
  let b := nearOptimalReciprocalB κ ε
  let J := nearOptimalReciprocalJ κ ε
  ∑ j ∈ Finset.range (J+1), Polynomial.C
    (4*(-1 : ℝ)^j *
      (∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ)) /
        (2 : ℝ)^(2*b))*Polynomial.Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)

def nearOptimalReciprocalTruncation (b J : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (J+1), Polynomial.C
    (4*(-1 : ℝ)^j *
      (∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ)) /
        (2 : ℝ)^(2*b))*Polynomial.Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)

theorem nearOptimalReciprocalPolynomial_eq_truncation (κ ε : ℝ) :
    nearOptimalReciprocalPolynomial κ ε =
      nearOptimalReciprocalTruncation (nearOptimalReciprocalB κ ε) (nearOptimalReciprocalJ κ ε) := rfl

theorem nearOptimalReciprocalTruncation_degree_parity (b J : ℕ) :
    (nearOptimalReciprocalTruncation b J).degree ≤ ((2*J+1 : ℕ) : WithBot ℕ) ∧
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2*J+1)
      (nearOptimalReciprocalTruncation b J) ∧
    (nearOptimalReciprocalTruncation b J).eval 0 = 0 := by
  have ho (j : ℕ) : Odd ((2*j+1 : ℕ) : ℤ) := by
    refine ⟨j, ?_⟩
    push_cast
    ring
  have hzero : (nearOptimalReciprocalTruncation b J).eval 0 = 0 := by
    simp only [nearOptimalReciprocalTruncation, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_eval_zero_of_odd ℝ (ho _),
      mul_zero, Finset.sum_const_zero]
  refine ⟨?_, ?_, hzero⟩
  · apply Polynomial.degree_le_of_natDegree_le
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, Polynomial.Chebyshev.natDegree_T,
      Int.natAbs_natCast, zero_add]
    simp only [Finset.mem_range] at hj
    omega
  · unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C, (odd_two_mul_add_one J).neg_one_pow,
      neg_one_mul]
    have hn (j : ℕ) : (Polynomial.Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)).eval (-x) =
        -(Polynomial.Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)).eval x := by
      rw [Polynomial.Chebyshev.T_eval_neg, Int.negOnePow_odd _ (ho j)]
      norm_num
    simp only [nearOptimalReciprocalTruncation, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    simp_rw [hn]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem nearOptimalReciprocal_cutoff_bounds (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    let b : ℕ := Nat.ceil (κ*κ*Real.log (κ/ε))
    let J : ℕ := Nat.ceil (Real.sqrt ((b : ℝ)*Real.log (4*(b : ℝ)/ε)))
    1 ≤ b ∧ 2 ≤ J ∧ (2*J+1 : ℝ) ≤ 32*κ*Real.log (κ/ε) := by
  let L := Real.log (κ/ε)
  let b : ℕ := Nat.ceil (κ*κ*L)
  let J : ℕ := Nat.ceil (Real.sqrt ((b : ℝ)*Real.log (4*(b : ℝ)/ε)))
  have hκ0 : 0 < κ := by linarith
  have hratio : (2 : ℝ) ≤ κ/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hratio
  have hL : 1/2 < L := lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) hL2
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < κ*κ*L := by positivity
  have hκsq : 1 ≤ κ*κ := by nlinarith
  have huL : L ≤ κ*κ*L := by nlinarith [mul_le_mul_of_nonneg_right hκsq hL0.le]
  have hb : 1 ≤ b := by
    have hb0 : 0 < b := Nat.ceil_pos.mpr hu0
    omega
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbLower : κ*κ*L ≤ (b : ℝ) := Nat.le_ceil _
  have hbUpper : (b : ℝ) ≤ 3*κ*κ*L := by
    have hu := (Nat.ceil_lt_add_one hu0.le).le
    change (b : ℝ) ≤ κ*κ*L+1 at hu
    nlinarith
  have hratio8 : (8 : ℝ) ≤ 4*(b : ℝ)/ε :=
    (le_div_iff₀ hε).mpr (by nlinarith)
  have hlog8 : 2 < Real.log (8 : ℝ) := by
    have he : Real.log (8 : ℝ) = 3*Real.log 2 := by
      simpa only [Nat.cast_ofNat, show (2 : ℝ)^3 = 8 by norm_num] using! Real.log_pow 2 3
    rw [he]
    linarith [Real.log_two_gt_d9]
  have hlogLower : 2 < Real.log (4*(b : ℝ)/ε) :=
    hlog8.trans_le (Real.log_le_log (by norm_num) hratio8)
  have hA0 : 0 ≤ (b : ℝ)*Real.log (4*(b : ℝ)/ε) := by positivity
  have hA : 1 < (b : ℝ)*Real.log (4*(b : ℝ)/ε) := by
    nlinarith [mul_le_mul_of_nonneg_right hb1 (by linarith : 0 ≤ Real.log (4*(b : ℝ)/ε))]
  have hS : 1 < Real.sqrt ((b : ℝ)*Real.log (4*(b : ℝ)/ε)) := by
    nlinarith [Real.sq_sqrt hA0, Real.sqrt_nonneg ((b : ℝ)*Real.log (4*(b : ℝ)/ε))]
  have hJ : 2 ≤ J := by
    have hJcast : (1 : ℝ) < J := hS.trans_le (Nat.le_ceil _)
    have : 1 < J := by exact_mod_cast hJcast
    omega
  have hLid : L = Real.log κ-Real.log ε := by
    dsimp [L]
    rw [Real.log_div hκ0.ne' hε.ne']
  have hlogκ : Real.log κ ≤ L := by
    have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le (by linarith)
    linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_self hL0.le)
  have hlog12 : Real.log (12 : ℝ) ≤ 4*L := by
    have h12 := Real.log_le_log (by norm_num : (0 : ℝ) < 12) (by norm_num : (12 : ℝ) ≤ 2^4)
    rw [Real.log_pow] at h12
    norm_num only [Nat.cast_ofNat] at h12
    linarith
  have hlogUpper : Real.log (4*(b : ℝ)/ε) ≤ 7*L := by
    have hnum : 4*(b : ℝ)/ε ≤ 12*κ*κ*L/ε :=
      (div_le_div_iff_of_pos_right hε).mpr (by nlinarith)
    have hl := Real.log_le_log (by positivity : 0 < 4*(b : ℝ)/ε) hnum
    rw [Real.log_div (by positivity : 12*κ*κ*L ≠ 0) hε.ne',
      Real.log_mul (by positivity : 12*κ*κ ≠ 0) hL0.ne',
      Real.log_mul (by positivity : 12*κ ≠ 0) hκ0.ne',
      Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) hκ0.ne'] at hl
    linarith
  have hSUpper : Real.sqrt ((b : ℝ)*Real.log (4*(b : ℝ)/ε)) ≤ 5*κ*L := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hprod := mul_le_mul hbUpper hlogUpper
      (by linarith : 0 ≤ Real.log (4*(b : ℝ)/ε)) (by positivity : 0 ≤ 3*κ*κ*L)
    nlinarith
  have hJU := (Nat.ceil_lt_add_one (Real.sqrt_nonneg ((b : ℝ)*Real.log (4*(b : ℝ)/ε)))).le
  change (J : ℝ) ≤ Real.sqrt ((b : ℝ)*Real.log (4*(b : ℝ)/ε))+1 at hJU
  have hκL : 1/2 ≤ κ*L := by
    nlinarith [mul_le_mul_of_nonneg_right hκ.le hL0.le]
  refine ⟨hb, hJ, ?_⟩
  change 2*(J : ℝ)+1 ≤ 32*κ*L
  nlinarith

theorem nearOptimalReciprocal_family_degree_parity (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε < 1/2) :
    1 ≤ nearOptimalReciprocalB κ ε ∧ 2 ≤ nearOptimalReciprocalJ κ ε ∧
    (nearOptimalReciprocalPolynomial κ ε).degree ≤
      ((2*nearOptimalReciprocalJ κ ε+1 : ℕ) : WithBot ℕ) ∧
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
      (2*nearOptimalReciprocalJ κ ε+1) (nearOptimalReciprocalPolynomial κ ε) ∧
    (nearOptimalReciprocalPolynomial κ ε).eval 0 = 0 ∧
    ((2*nearOptimalReciprocalJ κ ε+1 : ℕ) : ℝ) ≤ 32*κ*Real.log (κ/ε) := by
  obtain ⟨hb, hJ, hd⟩ := nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1.le
  obtain ⟨hdegree, hparity, hzero⟩ := nearOptimalReciprocalTruncation_degree_parity
    (nearOptimalReciprocalB κ ε) (nearOptimalReciprocalJ κ ε)
  refine ⟨hb, hJ, ?_, ?_, ?_, ?_⟩
  · rw [nearOptimalReciprocalPolynomial_eq_truncation]
    exact hdegree
  · rw [nearOptimalReciprocalPolynomial_eq_truncation]
    exact hparity
  · rw [nearOptimalReciprocalPolynomial_eq_truncation]
    exact hzero
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      nearOptimalReciprocalJ, nearOptimalReciprocalB] using! hd

theorem nearOptimalReciprocal_geometric_error (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε) (x : ℝ)
    (hx : x ∈ Set.Icc κ⁻¹ 1) :
    let b : ℕ := Nat.ceil (κ*κ*Real.log (κ/ε))
    |(Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial b).eval x-x⁻¹| ≤ ε := by
  let b : ℕ := Nat.ceil (κ*κ*Real.log (κ/ε))
  have hκ0 : 0 < κ := by linarith
  have hi : 0 < κ⁻¹ := inv_pos.mpr hκ0
  have hi1 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ.le
  have hq : 0 ≤ 1-κ⁻¹^2 := by nlinarith
  have hb : κ*κ*Real.log (κ/ε) ≤ (b : ℝ) := Nat.le_ceil _
  have harg : (b : ℝ)*(-κ⁻¹^2) ≤ -Real.log (κ/ε) := by
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg κ⁻¹)
    have he : κ⁻¹^2*(κ*κ*Real.log (κ/ε)) = Real.log (κ/ε) := by field_simp
    rw [he] at hm
    nlinarith
  have hpow : (1-κ⁻¹^2)^b ≤ ε/κ := by
    calc
      _ ≤ (Real.exp (-κ⁻¹^2))^b := pow_le_pow_left₀ hq
        (by linarith [Real.add_one_le_exp (-κ⁻¹^2)]) _
      _ = Real.exp ((b : ℝ)*(-κ⁻¹^2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-Real.log (κ/ε)) := Real.exp_le_exp.mpr harg
      _ = ε/κ := by
        rw [Real.exp_neg, Real.exp_log (div_pos hκ0 hε)]
        field_simp
  apply (Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial_error_le b hi hx).trans
  change (1-κ⁻¹^2)^b/κ⁻¹ ≤ ε
  rw [div_eq_mul_inv, inv_inv]
  have hm := mul_le_mul_of_nonneg_right hpow hκ0.le
  simpa only [div_mul_cancel₀ _ hκ0.ne'] using! hm

theorem nearOptimalReciprocal_geometric_error_of_abs (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (x : ℝ) (hx : |x| ∈ Set.Icc κ⁻¹ 1) :
    |(Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial (nearOptimalReciprocalB κ ε)).eval x-x⁻¹| ≤ ε := by
  rcases le_total 0 x with hx0 | hx0
  · exact nearOptimalReciprocal_geometric_error κ ε hκ hε x
      (by simpa only [abs_of_nonneg hx0] using! hx)
  · have hneg := nearOptimalReciprocal_geometric_error κ ε hκ hε (-x)
      (by simpa only [abs_of_nonpos hx0] using! hx)
    calc
      _ = |(Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial (nearOptimalReciprocalB κ ε)).eval (-x)-
          (-x)⁻¹| := by
        rw [Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial_eval_neg, inv_neg,
            neg_sub_neg, abs_sub_comm]
      _ ≤ ε := hneg

private theorem nearOptimalReciprocal_binomial_partition (b : ℕ) :
    2*(∑ i ∈ Finset.Ico 1 (b+1), (2*b).choose (b+i))+(2*b).choose b = 2^(2*b) := by
  have hl : (∑ m ∈ Finset.range b, (2*b).choose m) =
      ∑ i ∈ Finset.Ico 1 (b+1), (2*b).choose (b+i) := by
    apply Finset.sum_bij (fun m _ => b-m)
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [Finset.mem_Ico]
      omega
    · intro m hm m' hm' he
      simp only [Finset.mem_range] at hm hm'
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      refine ⟨b-i, Finset.mem_range.mpr (by omega), ?_⟩
      omega
    · intro m hm
      have hm' : m < b := Finset.mem_range.mp hm
      have he : 2*b-m = b+(b-m) := by omega
      rw [← he, Nat.choose_symm (by omega : m ≤ 2*b)]
  have hr : (∑ i ∈ Finset.Ico 1 (b+1), (2*b).choose (b+i)) =
      ∑ m ∈ Finset.Ico (b+1) (2*b+1), (2*b).choose m := by
    simpa only [show 1+b=b+1 by omega, show b+1+b=2*b+1 by omega] using!
      Finset.sum_Ico_add (fun m => (2*b).choose m) 1 (b+1) b
  have he := Finset.sum_range_add_sum_Ico (fun m => (2*b).choose m) (by omega : b+1 ≤ 2*b+1)
  rw [Finset.sum_range_succ, Nat.sum_range_choose, ← hr, hl] at he
  omega

private theorem nearOptimalReciprocal_binomial_half_tail (b : ℕ) :
    2*(∑ i ∈ Finset.Ico 1 (b+1), (2*b).choose (b+i)) ≤ 2^(2*b) := by
  have h := nearOptimalReciprocal_binomial_partition b
  omega

private theorem nearOptimalReciprocal_coefficient_size (b j : ℕ) :
    |4*(-1 : ℝ)^j*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b)| ≤ 2 := by
  have hN := nearOptimalReciprocal_binomial_half_tail b
  have hR : 2*(∑ i ∈ Finset.Ico 1 (b+1), ((2*b).choose (b+i) : ℝ)) ≤ (2 : ℝ)^(2*b) := by
    exact_mod_cast hN
  have hsub : Finset.Ico (j+1) (b+1) ⊆ Finset.Ico 1 (b+1) :=
    Finset.Ico_subset_Ico (by omega) le_rfl
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => Nat.cast_nonneg ((2*b).choose (b+i)) :
      ∀ i ∈ Finset.Ico 1 (b+1), i ∉ Finset.Ico (j+1) (b+1) → (0 : ℝ) ≤ ((2*b).choose (b+i)))
  have hp : 0 ≤ (∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ)) := by positivity
  have hden : (0 : ℝ) < 2^(2*b) := by positivity
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg hp,
    abs_of_pos hden]
  norm_num only [mul_one]
  rw [div_le_iff₀ hden]
  nlinarith

private theorem nearOptimalReciprocal_chebyshev_size (n : ℤ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem nearOptimalReciprocalTruncation_abs_le (b J : ℕ) (hJ : 1 ≤ J) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(nearOptimalReciprocalTruncation b J).eval x| ≤ 4*(J : ℝ) := by
  unfold nearOptimalReciprocalTruncation
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range (J+1), (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      simpa only [mul_one] using! mul_le_mul (nearOptimalReciprocal_coefficient_size b j)
        (nearOptimalReciprocal_chebyshev_size ((2*j+1 : ℕ) : ℤ) x hx) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ 4*(J : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      nlinarith

theorem nearOptimalReciprocal_size_bound (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(nearOptimalReciprocalPolynomial κ ε).eval x| ≤ 4*(nearOptimalReciprocalJ κ ε : ℝ) := by
  rw [nearOptimalReciprocalPolynomial_eq_truncation]
  apply nearOptimalReciprocalTruncation_abs_le _ _ _ x hx
  have hJ := (nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1).2.1
  change 2 ≤ nearOptimalReciprocalJ κ ε at hJ
  omega

theorem nearOptimalReciprocal_scale_bounded (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(4*(nearOptimalReciprocalJ κ ε : ℝ))⁻¹*
      (nearOptimalReciprocalPolynomial κ ε).eval x| ≤ 1 := by
  have hJ := (nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1).2.1
  change 2 ≤ nearOptimalReciprocalJ κ ε at hJ
  have hJr : (0 : ℝ) < nearOptimalReciprocalJ κ ε := by
    exact_mod_cast (by omega : 0 < nearOptimalReciprocalJ κ ε)
  have hp : (0 : ℝ) < 4*(nearOptimalReciprocalJ κ ε : ℝ) := by positivity
  rw [abs_mul, abs_inv, abs_of_pos hp]
  exact (inv_mul_le_one₀ hp).mpr (nearOptimalReciprocal_size_bound κ ε hκ hε hε1 x hx)

private theorem nearOptimalReciprocal_binomial_mgf (b : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.range (2*b+1),
      (((2*b).choose m : ℝ)/(2 : ℝ)^(2*b))*
        Real.exp (2*t*((m : ℝ)-(b : ℝ)))) = (Real.cosh t)^(2*b) := by
  have hterm (m : ℕ) (hm : m ∈ Finset.range (2*b+1)) :
      Real.exp (2*t*((m : ℝ)-(b : ℝ))) = (Real.exp t)^m*(Real.exp (-t))^(2*b-m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub (by simp only [Finset.mem_range] at hm; omega : m ≤ 2*b)]
    push_cast
    ring
  rw [Real.cosh_eq, div_pow, add_pow]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hterm m hm]
  ring

theorem nearOptimalReciprocal_binomial_tail (b k : ℕ) (hb : 0 < b) :
    (∑ i ∈ Finset.Ico k (b+1), ((2*b).choose (b+i) : ℝ)/(2 : ℝ)^(2*b)) ≤
      Real.exp (-((k : ℝ)^2)/(b : ℝ)) := by
  let t : ℝ := (k : ℝ)/(b : ℝ)
  let a : ℕ → ℝ := fun m => ((2*b).choose m : ℝ)/(2 : ℝ)^(2*b)
  have hb0 : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : (∑ i ∈ Finset.Ico k (b+1), a (b+i)) =
      ∑ m ∈ Finset.Ico (b+k) (2*b+1), a m := by
    simpa only [Nat.add_comm k b, show b+1+b=2*b+1 by omega] using! Finset.sum_Ico_add a k (b+1) b
  have hf : (∑ m ∈ Finset.Ico (b+k) (2*b+1), a m) =
      ∑ m ∈ Finset.range (2*b+1), if b+k ≤ m then a m else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, and_comm]
  have hmark : (∑ m ∈ Finset.range (2*b+1), if b+k ≤ m then a m else 0) ≤
      Real.exp (-2*t*(k : ℝ))*(∑ m ∈ Finset.range (2*b+1),
        a m*Real.exp (2*t*((m : ℝ)-(b : ℝ)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    have ha : 0 ≤ a m := by dsimp [a]; positivity
    by_cases hm : b+k ≤ m
    · rw [if_pos hm]
      have hm' : (b : ℝ)+(k : ℝ) ≤ m := by exact_mod_cast hm
      have he : 1 ≤ Real.exp (-2*t*(k : ℝ))*Real.exp (2*t*((m : ℝ)-(b : ℝ))) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        have hh := mul_nonneg ht (show 0 ≤ (m : ℝ)-(b : ℝ)-(k : ℝ) by linarith)
        nlinarith
      have hh := mul_le_mul_of_nonneg_left he ha
      simpa only [mul_one, one_mul, mul_assoc, mul_comm (a m)] using! hh
    · rw [if_neg hm]
      positivity
  have hcosh : (Real.cosh t)^(2*b) ≤ Real.exp ((b : ℝ)*t^2) := by
    have hh := pow_le_pow_left₀ (Real.cosh_pos t).le (Real.cosh_le_exp_half_sq t) (2*b)
    rw [← Real.exp_nat_mul] at hh
    convert! hh using 1
    congr 1
    push_cast
    ring
  change (∑ i ∈ Finset.Ico k (b+1), a (b+i)) ≤ _
  rw [hs, hf]
  apply hmark.trans
  rw [show (∑ m ∈ Finset.range (2*b+1), a m*Real.exp (2*t*((m : ℝ)-(b : ℝ)))) =
      (Real.cosh t)^(2*b) from nearOptimalReciprocal_binomial_mgf b t]
  calc
    _ ≤ Real.exp (-2*t*(k : ℝ))*Real.exp ((b : ℝ)*t^2) :=
      mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

private theorem nearOptimalReciprocal_binomial_two_step {R : Type*} [CommSemiring R] (n : ℕ) (f : ℕ → R) :
    (∑ i ∈ Finset.range (n+3), ((n+2).choose i : R)*f i) =
      ∑ i ∈ Finset.range (n+1), (n.choose i : R)*(f i+2*f (i+1)+f (i+2)) := by
  rw [Finset.sum_choose_succ_mul (fun i _ => f i) (n+1),
    Finset.sum_choose_succ_mul (fun i _ => f i) n,
    Finset.sum_choose_succ_mul (fun i _ => f (i+1)) n]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private def nearOptimalReciprocal_evenBinomial (b : ℕ) : Polynomial ℝ :=
  C ((-1 : ℝ)^b/(2 : ℝ)^(2*b)) *
    ∑ m ∈ Finset.range (2*b+1), ((2*b).choose m : Polynomial ℝ)*
      (C ((-1 : ℝ)^m)*Chebyshev.T ℝ (2*(m : ℤ)-2*(b : ℤ)))

private theorem nearOptimalReciprocal_evenBinomial_zero :
    nearOptimalReciprocal_evenBinomial 0 = 1 := by simp [nearOptimalReciprocal_evenBinomial]

private theorem nearOptimalReciprocal_evenBinomial_succ (b : ℕ) : nearOptimalReciprocal_evenBinomial (b+1) = (1-X^2)*nearOptimalReciprocal_evenBinomial b := by
  unfold nearOptimalReciprocal_evenBinomial
  have hN : 2*(b+1)=2*b+2 := by omega
  rw [hN]
  rw [nearOptimalReciprocal_binomial_two_step]
  have hterm (m : ℕ) :
      C ((-1 : ℝ)^m)*Chebyshev.T ℝ (2*(m : ℤ)-2*((b+1 : ℕ) : ℤ)) +
        2*(C ((-1 : ℝ)^(m+1))*Chebyshev.T ℝ (2*((m+1 : ℕ) : ℤ)-2*((b+1 : ℕ) : ℤ))) +
        C ((-1 : ℝ)^(m+2))*Chebyshev.T ℝ (2*((m+2 : ℕ) : ℤ)-2*((b+1 : ℕ) : ℤ)) =
      2*(Chebyshev.T ℝ 2-1)*(C ((-1 : ℝ)^m)*Chebyshev.T ℝ (2*(m : ℤ)-2*(b : ℤ))) := by
    have h1 : 2*(m : ℤ)-2*((b+1 : ℕ) : ℤ) = (2*(m : ℤ)-2*(b : ℤ))-2 := by omega
    have h2 : 2*((m+1 : ℕ) : ℤ)-2*((b+1 : ℕ) : ℤ) = 2*(m : ℤ)-2*(b : ℤ) := by omega
    have h3 : 2*((m+2 : ℕ) : ℤ)-2*((b+1 : ℕ) : ℤ) = (2*(m : ℤ)-2*(b : ℤ))+2 := by omega
    rw [h1,h2,h3]
    simp only [pow_succ, C_mul, C_neg, C_1]
    have ht := Chebyshev.T_mul_T ℝ 2 (2*(m : ℤ)-2*(b : ℤ))
    have htn : Chebyshev.T ℝ (2-(2*(m : ℤ)-2*(b : ℤ))) =
        Chebyshev.T ℝ ((2*(m : ℤ)-2*(b : ℤ))-2) := by
      rw [show 2-(2*(m : ℤ)-2*(b : ℤ)) = -((2*(m : ℤ)-2*(b : ℤ))-2) by ring, Chebyshev.T_neg]
    rw [htn, add_comm (2 : ℤ)] at ht
    linear_combination -(C ((-1 : ℝ)^m))*ht
  simp_rw [hterm]
  have hs : (∑ m ∈ Finset.range (2*b+1), ((2*b).choose m : Polynomial ℝ)*
      (2*(Chebyshev.T ℝ 2-1)*(C ((-1 : ℝ)^m)*Chebyshev.T ℝ (2*(m : ℤ)-2*(b : ℤ))))) =
      2*(Chebyshev.T ℝ 2-1) * (∑ m ∈ Finset.range (2*b+1),
        ((2*b).choose m : Polynomial ℝ)*(C ((-1 : ℝ)^m)*Chebyshev.T ℝ (2*(m : ℤ)-2*(b : ℤ)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hs]
  have hc : C ((-1 : ℝ)^(b+1)/(2 : ℝ)^(2*b+2)) =
      C (-1/4)*C ((-1 : ℝ)^b/(2 : ℝ)^(2*b)) := by
    rw [← C_mul]
    congr 1
    rw [pow_succ, pow_add]
    norm_num
    ring
  have ht : C (-1/4)*2*(Chebyshev.T ℝ 2-1) = (1-X^2 : Polynomial ℝ) := by
    rw [Chebyshev.T_two]
    have hq : C (-1/4 : ℝ)*(4 : Polynomial ℝ) = -1 := by
      rw [← C_ofNat, ← C_mul]
      norm_num
    linear_combination (X^2-1)*hq
  have hscale : C ((-1 : ℝ)^(b+1)/(2 : ℝ)^(2*b+2))*(2*(Chebyshev.T ℝ 2-1)) =
      (1-X^2)*C ((-1 : ℝ)^b/(2 : ℝ)^(2*b)) := by
    rw [hc]
    calc
      _ = (C (-1/4)*2*(Chebyshev.T ℝ 2-1))*C ((-1 : ℝ)^b/(2 : ℝ)^(2*b)) := by ring
      _ = _ := by rw [ht]
  rw [← mul_assoc, hscale, mul_assoc]

private theorem nearOptimalReciprocal_evenBinomial_eq (b : ℕ) : nearOptimalReciprocal_evenBinomial b = (1-X^2)^b := by
  induction b with
  | zero => simp [nearOptimalReciprocal_evenBinomial_zero]
  | succ b ih => rw [nearOptimalReciprocal_evenBinomial_succ, ih, pow_succ' (1-X^2 : Polynomial ℝ) b]

private theorem nearOptimalReciprocal_evenBinomial_as_sum (b : ℕ) : nearOptimalReciprocal_evenBinomial b =
    ∑ m ∈ Finset.range (2*b+1),
      C (((-1 : ℝ)^(b+m)*((2*b).choose m : ℝ))/(2 : ℝ)^(2*b))*
        Chebyshev.T ℝ (2*(m : ℤ)-2*(b : ℤ)) := by
  unfold nearOptimalReciprocal_evenBinomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hc : ((2*b).choose m : Polynomial ℝ) = C ((2*b).choose m : ℝ) := by norm_cast
  rw [hc]
  simp only [← mul_assoc, ← C_mul]
  congr 1
  congr 1
  rw [pow_add]
  ring

private theorem nearOptimalReciprocal_even_sign_sub (b m : ℕ) (hm : m ≤ 2*b) : (-1 : ℝ)^(2*b-m) = (-1 : ℝ)^m := by
  apply mul_right_cancel₀ (pow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0))
  calc
    _ = (-1 : ℝ)^(2*b-m+m) := (pow_add _ _ _).symm
    _ = 1 := by rw [Nat.sub_add_cancel hm]; exact (even_two_mul b).neg_one_pow
    _ = (-1 : ℝ)^m*(-1 : ℝ)^m := by
      rw [← pow_add, ← two_mul]
      exact (even_two_mul m).neg_one_pow.symm

private theorem nearOptimalReciprocal_even_paired (b : ℕ) : (1-X^2 : Polynomial ℝ)^b =
    C (((2*b).choose b : ℝ)/(2 : ℝ)^(2*b)) +
      ∑ i ∈ Finset.Ico 1 (b+1),
        C (2*(-1 : ℝ)^i*((2*b).choose (b+i) : ℝ)/(2 : ℝ)^(2*b))*
          Chebyshev.T ℝ ((2*i : ℕ) : ℤ) := by
  let f : ℕ → Polynomial ℝ := fun m =>
    C (((-1 : ℝ)^(b+m)*((2*b).choose m : ℝ))/(2 : ℝ)^(2*b))*
      Chebyshev.T ℝ (2*(m : ℤ)-2*(b : ℤ))
  let w : ℕ → Polynomial ℝ := fun i =>
    C (((-1 : ℝ)^i*((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b))*
      Chebyshev.T ℝ ((2*i : ℕ) : ℤ)
  have hu (i : ℕ) : f (b+i) = w i := by
    have he : b+(b+i)=2*b+i := by omega
    dsimp [f,w]
    rw [he, pow_add, (even_two_mul b).neg_one_pow, one_mul]
    congr 2
    omega
  have hl (i : ℕ) (hi : i ≤ b) : f (b-i) = w i := by
    have hidx : 2*((b-i : ℕ) : ℤ)-2*(b : ℤ) = -((2*i : ℕ) : ℤ) := by omega
    have he : b+(b-i)=2*b-i := by omega
    have hc : (2*b).choose (b-i) = (2*b).choose (b+i) := by
      have hh := Nat.choose_symm (by omega : b-i ≤ 2*b)
      rw [show 2*b-(b-i)=b+i by omega] at hh
      exact hh.symm
    dsimp [f,w]
    rw [he, nearOptimalReciprocal_even_sign_sub b i (by omega), hc, hidx, Chebyshev.T_neg]
    congr 2
  have hleft : (∑ m ∈ Finset.range b, f m) = ∑ i ∈ Finset.Ico 1 (b+1), w i := by
    apply Finset.sum_bij (fun m _ => b-m)
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [Finset.mem_Ico]
      omega
    · intro m hm m' hm' he
      simp only [Finset.mem_range] at hm hm'
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      exact ⟨b-i, Finset.mem_range.mpr (by omega), by omega⟩
    · intro m hm
      have hm' : m < b := Finset.mem_range.mp hm
      have hh := hl (b-m) (by omega)
      simpa only [show b-(b-m)=m by omega] using! hh
  have hright : (∑ m ∈ Finset.Ico (b+1) (2*b+1), f m) =
      ∑ i ∈ Finset.Ico 1 (b+1), w i := by
    have hh := Finset.sum_Ico_add f 1 (b+1) b
    simp only [show 1+b=b+1 by omega, show b+1+b=2*b+1 by omega] at hh
    rw [← hh]
    exact Finset.sum_congr rfl (fun i _ => hu i)
  have hcenter : f b = C (((2*b).choose b : ℝ)/(2 : ℝ)^(2*b)) := by
    dsimp [f]
    rw [show b+b=2*b by omega, (even_two_mul b).neg_one_pow]
    simp
  have hpart := Finset.sum_range_add_sum_Ico f (by omega : b+1 ≤ 2*b+1)
  rw [Finset.sum_range_succ, hleft, hright, hcenter] at hpart
  rw [← nearOptimalReciprocal_evenBinomial_eq b, nearOptimalReciprocal_evenBinomial_as_sum]
  change (∑ m ∈ Finset.range (2*b+1), f m) = _
  rw [← hpart]
  calc
    _ = C (((2*b).choose b : ℝ)/(2 : ℝ)^(2*b)) +
        ∑ i ∈ Finset.Ico 1 (b+1), (w i+w i) := by
      rw [Finset.sum_add_distrib]
      abel
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [w]
      rw [← add_mul, ← C_add]
      congr 1
      congr 1
      ring

private theorem nearOptimalReciprocal_adjacent_telescope {R : Type*} [CommRing R] (H V : ℕ → R) (b : ℕ) :
    (∑ j ∈ Finset.range b, (H j*V j+H j*V (j+1))) =
      H 0*V 0-H b*V b +
        ∑ i ∈ Finset.Ico 1 (b+1), (H (i-1)+H i)*V i := by
  rw [Finset.sum_Ico_eq_add_neg _ (by omega : 1 ≤ b+1)]
  simp only [Finset.sum_range_one, Nat.zero_sub]
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ (fun j => H j*V j+H j*V (j+1)) b,
      Finset.sum_range_succ (fun i => (H (i-1)+H i)*V i) (b+1), ih]
    rw [show b+1-1=b by omega]
    ring

private theorem nearOptimalReciprocal_tail_step (b i : ℕ) (hi : i ≤ b) :
    (∑ k ∈ Finset.Ico i (b+1), ((2*b).choose (b+k) : ℝ)) =
      ((2*b).choose (b+i) : ℝ) +
        ∑ k ∈ Finset.Ico (i+1) (b+1), ((2*b).choose (b+k) : ℝ) := by
  rw [Finset.sum_Ico_eq_add_neg _ (by omega : i ≤ b+1),
    Finset.sum_Ico_eq_add_neg _ (by omega : i+1 ≤ b+1),
    Finset.sum_range_succ (fun k => ((2*b).choose (b+k) : ℝ)) i]
  ring

private theorem nearOptimalReciprocal_adjacent_coefficient (b i : ℕ) (hi : 1 ≤ i) (hib : i ≤ b) :
    C (2*(-1 : ℝ)^(i-1)*(∑ k ∈ Finset.Ico i (b+1), ((2*b).choose (b+k) : ℝ))/(2 : ℝ)^(2*b)) +
      C (2*(-1 : ℝ)^i*(∑ k ∈ Finset.Ico (i+1) (b+1), ((2*b).choose (b+k) : ℝ))/(2 : ℝ)^(2*b)) =
        -C (2*(-1 : ℝ)^i*((2*b).choose (b+i) : ℝ)/(2 : ℝ)^(2*b)) := by
  have he : (-1 : ℝ)^i = -((-1 : ℝ)^(i-1)) := by
    conv_lhs => rw [show i=i-1+1 by omega]
    rw [pow_succ, mul_neg_one]
  rw [nearOptimalReciprocal_tail_step b i hib, ← C_add, ← C_neg, he]
  congr 1
  ring

private def nearOptimalReciprocal_halfCoefficient (b j : ℕ) : Polynomial ℝ :=
  C (2*(-1 : ℝ)^j*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b))
private def nearOptimalReciprocal_evenBasis (j : ℕ) : Polynomial ℝ := Chebyshev.T ℝ ((2*j : ℕ) : ℤ)

private theorem nearOptimalReciprocal_X_odd_term (b j : ℕ) :
    X*(C (4*(-1 : ℝ)^j*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b))*
      Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)) =
      nearOptimalReciprocal_halfCoefficient b j*nearOptimalReciprocal_evenBasis j+nearOptimalReciprocal_halfCoefficient b j*nearOptimalReciprocal_evenBasis (j+1) := by
  have hc : C (4*(-1 : ℝ)^j*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b)) =
      2*nearOptimalReciprocal_halfCoefficient b j := by
    unfold nearOptimalReciprocal_halfCoefficient
    rw [← C_ofNat, ← C_mul]
    congr 1
    ring
  have ht := Chebyshev.T_mul_T ℝ 1 ((2*j+1 : ℕ) : ℤ)
  have ha : 1+((2*j+1 : ℕ) : ℤ) = ((2*(j+1) : ℕ) : ℤ) := by omega
  have hs : 1-((2*j+1 : ℕ) : ℤ) = -((2*j : ℕ) : ℤ) := by omega
  rw [Chebyshev.T_one, ha, hs, Chebyshev.T_neg] at ht
  change 2*X*Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ) = nearOptimalReciprocal_evenBasis
      (j+1)+nearOptimalReciprocal_evenBasis j at ht
  rw [hc]
  calc
    _ = nearOptimalReciprocal_halfCoefficient b j*(2*X*Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)) := by ring
    _ = _ := by rw [ht]; ring

private theorem nearOptimalReciprocal_halfCoefficient_zero (b : ℕ) : nearOptimalReciprocal_halfCoefficient b 0 =
    1-C (((2*b).choose b : ℝ)/(2 : ℝ)^(2*b)) := by
  have hp := nearOptimalReciprocal_binomial_partition b
  have hr : 2*(∑ i ∈ Finset.Ico 1 (b+1), ((2*b).choose (b+i) : ℝ))+((2*b).choose b : ℝ) =
      (2 : ℝ)^(2*b) := by exact_mod_cast hp
  unfold nearOptimalReciprocal_halfCoefficient
  simp only [pow_zero, mul_one, zero_add]
  rw [← C_1, ← C_sub]
  congr 1
  have hd : (2 : ℝ)^(2*b) ≠ 0 := by positivity
  field_simp
  linarith

private theorem nearOptimalReciprocal_X_full_odd (b : ℕ) :
    X*(∑ j ∈ Finset.range b,
      C (4*(-1 : ℝ)^j*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b))*
        Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)) = 1-(1-X^2)^b := by
  rw [Finset.mul_sum]
  simp_rw [nearOptimalReciprocal_X_odd_term]
  rw [nearOptimalReciprocal_adjacent_telescope]
  have hb : nearOptimalReciprocal_halfCoefficient b b = 0 := by
    simp [nearOptimalReciprocal_halfCoefficient]
  have hv0 : nearOptimalReciprocal_evenBasis 0 = 1 := by simp [nearOptimalReciprocal_evenBasis]
  have hsum : (∑ i ∈ Finset.Ico 1 (b+1),
      (nearOptimalReciprocal_halfCoefficient b (i-1)+nearOptimalReciprocal_halfCoefficient b i)*nearOptimalReciprocal_evenBasis i) =
      -(∑ i ∈ Finset.Ico 1 (b+1),
        C (2*(-1 : ℝ)^i*((2*b).choose (b+i) : ℝ)/(2 : ℝ)^(2*b))*
          Chebyshev.T ℝ ((2*i : ℕ) : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hp : nearOptimalReciprocal_halfCoefficient b (i-1)+nearOptimalReciprocal_halfCoefficient b i =
        -C (2*(-1 : ℝ)^i*((2*b).choose (b+i) : ℝ)/(2 : ℝ)^(2*b)) := by
      unfold nearOptimalReciprocal_halfCoefficient
      rw [show i-1+1=i by omega]
      exact nearOptimalReciprocal_adjacent_coefficient b i hi'.1 (by omega)
    rw [hp]
    dsimp [nearOptimalReciprocal_evenBasis]
    ring
  rw [hb, zero_mul, sub_zero, hv0, mul_one, nearOptimalReciprocal_halfCoefficient_zero, hsum,
      nearOptimalReciprocal_even_paired]
  ring

theorem nearOptimalReciprocal_full_expansion (b : ℕ) : (∑ j ∈ Finset.range b,
    C (4*(-1 : ℝ)^j*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b))*
      Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)) = Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial b := by
  apply mul_left_cancel₀ (X_ne_zero : (X : Polynomial ℝ) ≠ 0)
  rw [nearOptimalReciprocal_X_full_odd,
      Qatlib.Concepts.QsvtCore.LinearSystems.X_mul_reciprocalPolynomial]

private def nearOptimalReciprocal_coef (b j : ℕ) : ℝ :=
  4*(-1 : ℝ)^j*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ))/(2 : ℝ)^(2*b)

private theorem nearOptimalReciprocal_coef_abs (b j : ℕ) : |nearOptimalReciprocal_coef b j| =
    4*(∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ)/(2 : ℝ)^(2*b)) := by
  have hs : 0 ≤ (∑ i ∈ Finset.Ico (j+1) (b+1), ((2*b).choose (b+i) : ℝ)) := by positivity
  have hd : (0 : ℝ) < 2^(2*b) := by positivity
  unfold nearOptimalReciprocal_coef
  rw [← Finset.sum_div]
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg hs, abs_of_pos hd]
  norm_num
  ring

private theorem nearOptimalReciprocal_coef_zero (b j : ℕ) (hj : b ≤ j) : nearOptimalReciprocal_coef b j = 0 := by
  have he : Finset.Ico (j+1) (b+1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
  simp [nearOptimalReciprocal_coef, he]

private theorem nearOptimalReciprocal_omitted_coef (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (j : ℕ) (hj : nearOptimalReciprocalJ κ ε+1 ≤ j) :
    |nearOptimalReciprocal_coef (nearOptimalReciprocalB κ ε) j| ≤ ε/(nearOptimalReciprocalB κ ε : ℝ) := by
  let b := nearOptimalReciprocalB κ ε
  let J := nearOptimalReciprocalJ κ ε
  have hb := (nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1).1
  change 1 ≤ b at hb
  have hb0 : 0 < b := by omega
  have hbr : (0 : ℝ) < b := Nat.cast_pos.mpr hb0
  have hratio : 1 ≤ 4*(b : ℝ)/ε := (le_div_iff₀ hε).mpr (by
    have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith)
  have hlog : 0 ≤ Real.log (4*(b : ℝ)/ε) := Real.log_nonneg hratio
  have hA0 : 0 ≤ (b : ℝ)*Real.log (4*(b : ℝ)/ε) := by positivity
  have hJr : Real.sqrt ((b : ℝ)*Real.log (4*(b : ℝ)/ε)) ≤ (J : ℝ) := Nat.le_ceil _
  have hJq := mul_self_le_mul_self (Real.sqrt_nonneg ((b : ℝ)*Real.log (4*(b : ℝ)/ε))) hJr
  rw [Real.mul_self_sqrt hA0] at hJq
  have hji : (J : ℝ) ≤ ((j+1 : ℕ) : ℝ) := by
    exact_mod_cast (by change J+1 ≤ j at hj; omega : J ≤ j+1)
  have hsq := mul_self_le_mul_self (Nat.cast_nonneg J : (0 : ℝ) ≤ J) hji
  have harg : -(((j+1 : ℕ) : ℝ)^2)/(b : ℝ) ≤ -Real.log (4*(b : ℝ)/ε) := by
    rw [div_le_iff₀ hbr]
    nlinarith
  have he : Real.exp (-(((j+1 : ℕ) : ℝ)^2)/(b : ℝ)) ≤ ε/(4*(b : ℝ)) := by
    apply (Real.exp_le_exp.mpr harg).trans_eq
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4*(b : ℝ)/ε)]
    simp [inv_div]
  rw [nearOptimalReciprocal_coef_abs]
  apply (mul_le_mul_of_nonneg_left (nearOptimalReciprocal_binomial_tail b (j+1) hb0) (by norm_num : (0 : ℝ) ≤ 4)).trans
  have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 4)
  have hc : 4*(ε/(4*(b : ℝ)))=ε/(b : ℝ) := by ring
  rwa [hc] at hh

theorem nearOptimalReciprocal_truncation_error (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(nearOptimalReciprocalPolynomial κ ε).eval x-
      (Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial (nearOptimalReciprocalB κ ε)).eval x| ≤ ε := by
  let b := nearOptimalReciprocalB κ ε
  let J := nearOptimalReciprocalJ κ ε
  let f : ℕ → ℝ := fun j => nearOptimalReciprocal_coef b j*(Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)).eval x
  have hg : (nearOptimalReciprocalPolynomial κ ε).eval x = ∑ j ∈ Finset.range (J+1), f j := by
    simp only [nearOptimalReciprocalPolynomial, eval_finsetSum, eval_mul, eval_C]
    rfl
  have hf : (Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial b).eval x = ∑ j ∈ Finset.range b, f j := by
    rw [← nearOptimalReciprocal_full_expansion]
    simp only [eval_finsetSum, eval_mul, eval_C]
    rfl
  rw [hg,hf]
  have hb := (nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1).1
  change 1 ≤ b at hb
  have hbr : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  by_cases hJ : J+1 ≤ b
  · have hs := Finset.sum_range_add_sum_Ico f hJ
    have he : (∑ j ∈ Finset.range (J+1), f j)-(∑ j ∈ Finset.range b, f j) =
        -(∑ j ∈ Finset.Ico (J+1) b, f j) := by linarith
    rw [he, abs_neg]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.Ico (J+1) b, ε/(b : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        have ht : |(Chebyshev.T ℝ ((2*j+1 : ℕ) : ℤ)).eval x| ≤ 1 := by
          rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos]
          exact Real.abs_cos_le_one _
        dsimp [f]
        rw [abs_mul]
        simpa only [mul_one] using! mul_le_mul (nearOptimalReciprocal_omitted_coef κ ε hκ hε hε1 j hj'.1) ht
          (abs_nonneg _) (by positivity : 0 ≤ ε/(b : ℝ))
      _ ≤ ε := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have hcount : ((b-(J+1) : ℕ) : ℝ) ≤ b := by exact_mod_cast (Nat.sub_le b (J+1))
        have hh := mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ ε/(b : ℝ))
        have hc : (b : ℝ)*(ε/(b : ℝ)) = ε := by field_simp
        rwa [hc] at hh
  · have hs := Finset.sum_range_add_sum_Ico f (by omega : b ≤ J+1)
    have hz : ∑ j ∈ Finset.Ico b (J+1), f j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [f, nearOptimalReciprocal_coef_zero b j (Finset.mem_Ico.mp hj).1, zero_mul]
    rw [hz, add_zero] at hs
    rw [← hs, sub_self, abs_zero]
    exact hε.le

theorem nearOptimalReciprocal_error_of_abs (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2)
    (x : ℝ) (hx : |x| ∈ Set.Icc κ⁻¹ 1) :
    |(nearOptimalReciprocalPolynomial κ ε).eval x-x⁻¹| ≤ 2*ε := by
  have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hx.2
  calc
    _ = |((nearOptimalReciprocalPolynomial κ ε).eval x-
        (Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial (nearOptimalReciprocalB κ ε)).eval x)+
          ((Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial (nearOptimalReciprocalB κ ε)).eval x-x⁻¹)| := by
      congr 1
      ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε+ε := add_le_add (nearOptimalReciprocal_truncation_error κ ε hκ hε hε1 x hx')
      (nearOptimalReciprocal_geometric_error_of_abs κ ε hκ hε x hx)
    _ = 2*ε := by ring

theorem nearOptimalReciprocal_error_bounds (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε < 1/2) :
    (∀ x ∈ Set.Icc κ⁻¹ 1,
      |(Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial (nearOptimalReciprocalB κ ε)).eval x-x⁻¹| ≤ ε) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(nearOptimalReciprocalPolynomial κ ε).eval x-
        (Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalPolynomial (nearOptimalReciprocalB κ ε)).eval x| ≤ ε) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(nearOptimalReciprocalPolynomial κ ε).eval x| ≤ 4*(nearOptimalReciprocalJ κ ε : ℝ)) ∧
    (∀ x ∈ Set.Icc κ⁻¹ 1, |(nearOptimalReciprocalPolynomial κ ε).eval x-x⁻¹| ≤ 2*ε) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(4*(nearOptimalReciprocalJ κ ε : ℝ))⁻¹*(nearOptimalReciprocalPolynomial κ ε).eval x| ≤ 1) := by
  refine ⟨?_, nearOptimalReciprocal_truncation_error κ ε hκ hε hε1.le,
    nearOptimalReciprocal_size_bound κ ε hκ hε hε1.le, ?_,
    nearOptimalReciprocal_scale_bounded κ ε hκ hε hε1.le⟩
  · intro x hx
    exact nearOptimalReciprocal_geometric_error κ ε hκ hε x hx
  · intro x hx
    have hx0 : 0 ≤ x := (inv_nonneg.mpr (by linarith : 0 ≤ κ)).trans hx.1
    exact nearOptimalReciprocal_error_of_abs κ ε hκ hε hε1.le x
      (by simpa only [abs_of_nonneg hx0] using! hx)

end Qatlib.Concepts.QsvtCore.LinearSystems
