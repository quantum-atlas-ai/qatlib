/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Computed integer polynomials bound the actual flat cutoff derivatives -/
set_option autoImplicit false
open Polynomial Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Semantic polynomial, identified below with the executable integer row. -/
noncomputable def cutoffDerivativePolynomial : ℕ → ℤ[X]
  | 0 => 1
  | n+1 => X^2*(cutoffDerivativePolynomial n-(cutoffDerivativePolynomial n).derivative)

/-- Definition of cutoff Coefficient At in the Hopf Atlas construction. -/
def cutoffCoefficientAt {N : ℕ} (row : Vector ℤ N) (m : ℕ) : ℤ :=
  if hm : m<N then row[m] else 0

/-- Definition of cutoff Next Coefficient Row in the Hopf Atlas construction. -/
def cutoffNextCoefficientRow (n : ℕ) (row : Vector ℤ (2*n+1)) : Vector ℤ (2*(n+1)+1) :=
  Vector.ofFn (fun k => if 2 ≤ k.val then
    cutoffCoefficientAt row (k.val-2)-(k.val-1 : ℤ)*cutoffCoefficientAt row (k.val-1) else 0)

/-- Definition of cutoff Coefficient Row in the Hopf Atlas construction. -/
def cutoffCoefficientRow : (n : ℕ) → Vector ℤ (2*n+1)
  | 0 => Vector.ofFn (fun _ => 1)
  | n+1 => cutoffNextCoefficientRow n (cutoffCoefficientRow n)

/-- Definition of cutoff Bump Majorant in the Hopf Atlas construction. -/
def cutoffBumpMajorant (n : ℕ) : ℕ :=
  ∑ m ∈ range (2*n+1), (cutoffCoefficientAt (cutoffCoefficientRow n) m).natAbs*max 1 (m^m)

noncomputable section

/-- Definition of cutoff Real Polynomial in the Hopf Atlas construction. -/
def cutoffRealPolynomial (n : ℕ) : ℝ[X] :=
  (cutoffDerivativePolynomial n).map (Int.castRingHom ℝ)

/-- Original `cutoffRealPolynomial_succ` guarantee for the `CutoffPolynomial` construction; the complete source hypotheses are retained. -/
theorem cutoffRealPolynomial_succ (n : ℕ) :
    cutoffRealPolynomial (n+1)=X^2*(cutoffRealPolynomial n-(cutoffRealPolynomial n).derivative) := by
  simp [cutoffRealPolynomial,cutoffDerivativePolynomial,Polynomial.derivative_map]

/-- Original `iteratedDeriv_expNegInvGlue` guarantee for the `CutoffPolynomial` construction; the complete source hypotheses are retained. -/
theorem iteratedDeriv_expNegInvGlue (n : ℕ) :
    iteratedDeriv n expNegInvGlue=fun x => (cutoffRealPolynomial n).eval x⁻¹*expNegInvGlue x := by
  induction n with
  | zero => simp [iteratedDeriv_zero,cutoffRealPolynomial,cutoffDerivativePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    rw [cutoffRealPolynomial_succ]
    exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (cutoffRealPolynomial n) x).deriv

/-- Original `cutoffDerivativePolynomial_degree` guarantee for the `CutoffPolynomial` construction; the complete source hypotheses are retained. -/
theorem cutoffDerivativePolynomial_degree (n : ℕ) :
    (cutoffDerivativePolynomial n).natDegree ≤ 2*n := by
  induction n with
  | zero => simp [cutoffDerivativePolynomial]
  | succ n ih =>
    have hd : (cutoffDerivativePolynomial n).derivative.natDegree ≤ 2*n :=
      ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)).trans ih
    have hs : (cutoffDerivativePolynomial n-(cutoffDerivativePolynomial n).derivative).natDegree ≤ 2*n :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le ih hd)
    rw [cutoffDerivativePolynomial]
    calc
      _ ≤ (X^2 : ℤ[X]).natDegree+
          (cutoffDerivativePolynomial n-(cutoffDerivativePolynomial n).derivative).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 2+2*n := by simpa only [Polynomial.natDegree_X_pow] using Nat.add_le_add_left hs 2
      _ = 2*(n+1) := by omega

/-- Original `cutoffRealPolynomial_degree` guarantee for the `CutoffPolynomial` construction; the complete source hypotheses are retained. -/
theorem cutoffRealPolynomial_degree (n : ℕ) : (cutoffRealPolynomial n).natDegree ≤ 2*n :=
  (Polynomial.natDegree_map_le).trans (cutoffDerivativePolynomial_degree n)

/-- Each entry computed by the finite vector program is the actual
coefficient of the derivative polynomial, including its zero extension. -/
theorem cutoffCoefficientAt_eq (n m : ℕ) :
    cutoffCoefficientAt (cutoffCoefficientRow n) m=(cutoffDerivativePolynomial n).coeff m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [cutoffCoefficientAt,cutoffCoefficientRow,cutoffDerivativePolynomial,Polynomial.coeff_one]
    | succ m => simp [cutoffCoefficientAt,cutoffDerivativePolynomial,Polynomial.coeff_one]
  | succ n ih =>
    by_cases hm : m<2*(n+1)+1
    · rw [cutoffCoefficientAt,dif_pos hm]
      simp only [cutoffCoefficientRow,cutoffNextCoefficientRow,Vector.getElem_ofFn]
      rw [cutoffDerivativePolynomial,Polynomial.coeff_X_pow_mul']
      by_cases htwo : 2 ≤ m
      · simp only [if_pos htwo,ih,Polynomial.coeff_sub,Polynomial.coeff_derivative]
        rw [show m-2+1=m-1 by omega]
        simp only [Nat.cast_sub htwo,Nat.cast_ofNat]
        ring
      · simp only [if_neg htwo]
    · rw [cutoffCoefficientAt,dif_neg hm]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (cutoffDerivativePolynomial_degree (n+1)) (by omega))).symm

/-- A global monomial-exponential estimate with the same integer weights
as the executable polynomial coefficient budget. -/
theorem monomial_mul_exp_neg_le (u : ℝ) (hu : 0 ≤ u) (m : ℕ) :
    u^m*Real.exp (-u) ≤ ((max 1 (m^m) : ℕ) : ℝ) := by
  have hfac : (0 : ℝ)<m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp u hu m)
  have hbound : u^m*Real.exp (-u) ≤ (m.factorial : ℝ) := by
    calc
      _ ≤ (Real.exp u*(m.factorial : ℝ))*Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = (m.factorial : ℝ) := by
        rw [mul_right_comm,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
  apply hbound.trans
  exact_mod_cast (Nat.factorial_le_pow m).trans (le_max_right 1 (m^m))

/-- Original `cutoffBumpMajorant_cast` guarantee for the `CutoffPolynomial` construction; the complete source hypotheses are retained. -/
theorem cutoffBumpMajorant_cast (n : ℕ) : (cutoffBumpMajorant n : ℝ)=
    ∑ m ∈ range (2*n+1), |((cutoffDerivativePolynomial n).coeff m : ℝ)| *
      ((max 1 (m^m) : ℕ) : ℝ) := by
  simp only [cutoffBumpMajorant,Nat.cast_sum,Nat.cast_mul,cutoffCoefficientAt_eq,
    Nat.cast_natAbs,Int.cast_abs]

/-- Original `cutoffRealPolynomial_coeff` guarantee for the `CutoffPolynomial` construction; the complete source hypotheses are retained. -/
theorem cutoffRealPolynomial_coeff (n m : ℕ) :
    (cutoffRealPolynomial n).coeff m=((cutoffDerivativePolynomial n).coeff m : ℝ) := by
  simp [cutoffRealPolynomial]

/-- Actual derivatives of the flat function are bounded by the executable
integer-vector coefficient budget, on the whole real line. -/
theorem iteratedDeriv_expNegInvGlue_abs_le (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤ (cutoffBumpMajorant n : ℝ) := by
  rw [congrFun (iteratedDeriv_expNegInvGlue n) x]
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx,mul_zero,abs_zero]
    exact Nat.cast_nonneg _
  · have hu : 0 ≤ x⁻¹ := inv_nonneg.mpr (lt_of_not_ge hx).le
    have hdeg : (cutoffRealPolynomial n).natDegree<2*n+1 :=
      Nat.lt_succ_of_le (cutoffRealPolynomial_degree n)
    rw [Polynomial.eval_eq_sum_range' hdeg,
      show expNegInvGlue x=Real.exp (-x⁻¹) by simp only [expNegInvGlue,if_neg hx],Finset.sum_mul]
    calc
      _ ≤ ∑ m ∈ range (2*n+1),
          |(cutoffRealPolynomial n).coeff m*(x⁻¹)^m*Real.exp (-x⁻¹)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ range (2*n+1), |((cutoffDerivativePolynomial n).coeff m : ℝ)| *
          ((max 1 (m^m) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [abs_mul,abs_mul,cutoffRealPolynomial_coeff,
          abs_of_nonneg (pow_nonneg hu m),abs_of_pos (Real.exp_pos _)]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (monomial_mul_exp_neg_le x⁻¹ hu m) (abs_nonneg ((cutoffDerivativePolynomial n).coeff m : ℝ))
      _ = (cutoffBumpMajorant n : ℝ) := (cutoffBumpMajorant_cast n).symm

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
