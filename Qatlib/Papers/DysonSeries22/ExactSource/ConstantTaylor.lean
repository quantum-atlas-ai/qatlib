/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DysonSeries22.Truncation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Constant-matrix Dyson and forcing Taylor polynomials

Each recursive integral raises the time exponent by one and contributes the
next factorial. The forcing series starts with the integral of the constant
driving vector and therefore has one extra time power.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.DysonSeries22.ExactSource Qatlib.Papers.DysonSeries22.Truncation

namespace Qatlib.Papers.DysonSeries22.ExactSource

/-- Integrating a Taylor monomial advances its factorial denominator. -/
private theorem integral_taylor_scalar (k : ℕ) (t : ℝ) :
    (∫ u in (0 : ℝ)..t, u ^ k / (k.factorial : ℝ)) =
      t ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (by omega : k + 1 ≠ 0),
    sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp

/-- The homogeneous recursive integral equals its constant-matrix Taylor term. -/
private theorem orderedDysonTerm_const {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (k : ℕ) (t : ℝ) :
    orderedDysonTerm (fun _ => -A) 0 k t = (t ^ k / (k.factorial : ℝ)) • A ^ k := by
  induction k generalizing t with
  | zero => simp [orderedDysonTerm]
  | succ k ih =>
    simp_rw [orderedDysonTerm, neg_mul, neg_neg, ih, mul_smul_comm, ← pow_succ']
    rw [intervalIntegral.integral_smul_const, integral_taylor_scalar]

/-- The constant driving term has one extra power of the interval length. -/
private theorem dysonSourceTerm_const {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (b : QState I) (k : ℕ) (t : ℝ) :
    dysonSourceTerm (fun _ => A) (fun _ => b) 0 k t =
      (t ^ (k + 1) / ((k + 1).factorial : ℝ)) • (A ^ k *ᵥ b) := by
  induction k generalizing t with
  | zero => simp [dysonSourceTerm, intervalIntegral.integral_const]
  | succ k ih =>
    simp_rw [dysonSourceTerm, ih, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ']
    rw [intervalIntegral.integral_smul_const, integral_taylor_scalar]

/-- Equation (16) is the exact finite homogeneous expansion for constant coefficients. -/
theorem truncatedEvolution_const {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) (K : ℕ) :
    truncatedEvolution (fun _ => A) 0 t K =
      ∑ k ∈ Finset.range (K + 1), (t ^ k / (k.factorial : ℝ)) • A ^ k := by
  unfold truncatedEvolution
  apply Finset.sum_congr rfl
  intro k _
  exact orderedDysonTerm_const A k t

/-- Equation (17) is the exact forcing expansion in the Euclidean state representation. -/
theorem truncatedSource_const {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (b : QState I) (t : ℝ) (K : ℕ) :
    truncatedSource (fun _ => A) (fun _ => b) 0 t K =
      ∑ k ∈ Finset.range K,
        (t ^ (k + 1) / ((k + 1).factorial : ℝ)) • toEuclidean_fromVec (A ^ k *ᵥ b) := by
  unfold truncatedSource
  apply Finset.sum_congr rfl
  intro k _
  rw [dysonSourceTerm_const]
  rfl

end Qatlib.Papers.DysonSeries22.ExactSource
