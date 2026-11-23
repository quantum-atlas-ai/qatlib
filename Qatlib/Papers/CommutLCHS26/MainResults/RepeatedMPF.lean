/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# Geometric error growth for repeated product formulas

This module isolates the raw product-formula amplification used before the outer
LCHS quadrature is applied.  If one exact local propagator is a contraction and
one product-formula step has operator error at most `ε / r`, then repeating
that step `r > 0` times has error at most `e ε` whenever `0 < ε ≤ 1`.
The matrix norm is the spectral operator norm, and the vector statement acts on
`EuclideanSpace`.

The geometric estimate formalizes the pointwise operator bound in
[AftabAnTrivisa2026], equation (3.33).  The local error bound is an input.

* [Aftab et al., 2026](https://arxiv.org/abs/2606.11475v1)
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- A uniform telescoping bound for a positive number of repeated matrices.

The exponent records the standard geometric growth of a raw repeated product
formula.  No commutation between the exact and approximate step is assumed.
-/
theorem repeated_power_error_geometric_of_succ (U W : Matrix I I ℂ) (r : ℕ) {η : ℝ}
    (hη : 0 ≤ η) (hU : ‖U‖ ≤ 1) (herr : ‖U - W‖ ≤ η) :
    ‖U ^ (r + 1) - W ^ (r + 1)‖
      ≤ ((r : ℝ) + 1) * η * (1 + η) ^ r := by
  have hW : ‖W‖ ≤ 1 + η := by
    calc ‖W‖ = ‖U - (U - W)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖U‖ + ‖U - W‖ := norm_sub_le _ _
      _ ≤ 1 + η := add_le_add hU herr
  induction r with
  | zero =>
      calc ‖U ^ (0 + 1) - W ^ (0 + 1)‖ = ‖U - W‖ := by simp
        _ ≤ η := herr
        _ = (((0 : ℕ) + 1) : ℝ) * η * (1 + η) ^ 0 := by norm_num
  | succ n ih =>
    have hIdentity : U ^ (n + 2) - W ^ (n + 2) =
        U ^ (n + 1) * (U - W) + (U ^ (n + 1) - W ^ (n + 1)) * W := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    have hUbase : ∀ k : ℕ, ‖U‖ ^ k ≤ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ]
          nlinarith [ih, hU, norm_nonneg U]
    have hUpow : ‖U ^ (n + 1)‖ ≤ 1 := by
      calc ‖U ^ (n + 1)‖ ≤ ‖U‖ ^ (n + 1) := norm_pow_le U (n + 1)
        _ ≤ 1 := hUbase (n + 1)
    have hFirst : ‖U ^ (n + 1) * (U - W)‖ ≤ η := by
      calc ‖U ^ (n + 1) * (U - W)‖ ≤ ‖U ^ (n + 1)‖ * ‖U - W‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ 1 * η := by
            nlinarith [hUpow, herr, norm_nonneg (U ^ (n + 1)),
              norm_nonneg (U - W)]
        _ = η := one_mul _
    have hAmass : (0 : ℝ) ≤ ((n : ℝ) + 1) * η * (1 + η) ^ n := by positivity
    have hSecond : ‖(U ^ (n + 1) - W ^ (n + 1)) * W‖
        ≤ ((n : ℝ) + 1) * η * (1 + η) ^ (n + 1) := by
      calc ‖(U ^ (n + 1) - W ^ (n + 1)) * W‖
          ≤ ‖U ^ (n + 1) - W ^ (n + 1)‖ * ‖W‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ (((n : ℝ) + 1) * η * (1 + η) ^ n) * ‖W‖ :=
            mul_le_mul_of_nonneg_right ih (norm_nonneg W)
        _ ≤ (((n : ℝ) + 1) * η * (1 + η) ^ n) * (1 + η) :=
            by nlinarith [hW, hAmass, norm_nonneg W]
        _ = ((n : ℝ) + 1) * η * (1 + η) ^ (n + 1) := by ring
    have hone : η ≤ η * (1 + η) ^ (n + 1) := by
      have honebase : (1 : ℝ) ≤ 1 + η := by linarith
      have honepow : ∀ k : ℕ, (1 : ℝ) ≤ (1 + η) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [pow_succ]
            nlinarith [ih, honebase, hη]
      have honele : (1 : ℝ) ≤ (1 + η) ^ (n + 1) := honepow (n + 1)
      nlinarith [honele, hη]
    calc ‖U ^ (n + 2) - W ^ (n + 2)‖
        ≤ ‖U ^ (n + 1) * (U - W)‖ + ‖(U ^ (n + 1) - W ^ (n + 1)) * W‖ := by
            rw [hIdentity]; exact norm_add_le _ _
      _ ≤ η + ((n : ℝ) + 1) * η * (1 + η) ^ (n + 1) := add_le_add hFirst hSecond
      _ ≤ η * (1 + η) ^ (n + 1) + ((n : ℝ) + 1) * η * (1 + η) ^ (n + 1) :=
          add_le_add_left hone _
      _ = (((n : ℝ) + 1) + 1) * η * (1 + η) ^ (n + 1) := by ring
      _ = ((((n + 1 : ℕ) : ℝ) + 1) * η * (1 + η) ^ (n + 1)) := by
            rw [Nat.cast_succ]

/-- The successor bound restated for an arbitrary positive repetition count. -/
theorem repeated_power_error_geometric (U W : Matrix I I ℂ) (r : ℕ) {η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hU : ‖U‖ ≤ 1) (herr : ‖U - W‖ ≤ η) :
    ‖U ^ r - W ^ r‖ ≤ (r : ℝ) * η * (1 + η) ^ (r - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, n + 1 = r := ⟨r - 1, Nat.succ_pred_eq_of_pos hr⟩
  simpa only [Nat.cast_succ, Nat.add_sub_cancel] using
    repeated_power_error_geometric_of_succ U W n hη hU herr

/-- The raw repeated-step error is bounded by `e ε` for an `ε ≤ 1` budget.

The local error is taken to be `ε / r`; in particular, the amplification
constant is fixed before all choices of matrices, dimensions, and repetitions.
-/
theorem repeated_mpf_error_le_exp (U W : Matrix I I ℂ) {r : ℕ} {ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hU : ‖U‖ ≤ 1) (herr : ‖U - W‖ ≤ ε / r) :
    ‖U ^ r - W ^ r‖ ≤ Real.exp 1 * ε := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hgeometric := repeated_power_error_geometric U W r hr (by positivity) hU herr
  have hexponent : (1 + ε / r) ^ (r - 1) ≤ Real.exp 1 := by
    have hdivpos : (0 : ℝ) < ε / r := div_pos hε hrR
    have hstep : (1 + ε / r) ^ r ≤ Real.exp ε := by
      have hbase : (1 : ℝ) + ε / r ≤ Real.exp (ε / r) := by
        have hx := Real.add_one_le_exp (ε / r)
        linarith
      have hpowexp : ∀ k : ℕ,
          (1 + ε / r) ^ k ≤ Real.exp ((ε / r) * k) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            calc (1 + ε / r) ^ (k + 1)
                = (1 + ε / r) ^ k * (1 + ε / r) := pow_succ _ _
              _ ≤ Real.exp ((ε / r) * k) * (1 + ε / r) :=
                  mul_le_mul_of_nonneg_right ih (by nlinarith [hdivpos])
              _ ≤ Real.exp ((ε / r) * k) * Real.exp (ε / r) :=
                  mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
              _ = Real.exp ((ε / r) * ((k + 1 : ℕ) : ℝ)) := by
                  rw [Nat.cast_succ,
                    show (ε / r) * ((k : ℝ) + 1) =
                      (ε / r) * (k : ℝ) + ε / r from by ring,
                    ← Real.exp_add]
      calc (1 + ε / r) ^ r ≤ Real.exp ((ε / r) * r) := hpowexp r
        _ = Real.exp ε := by field_simp [hrR.ne']
    have hone : (1 : ℝ) ≤ 1 + ε / r := by nlinarith [hdivpos]
    have hApositive : (0 : ℝ) ≤ (1 + ε / r) ^ (r - 1) :=
      pow_nonneg (by nlinarith) _
    have hAstep : (1 + ε / r) ^ (r - 1) ≤ (1 + ε / r) ^ ((r - 1) + 1) := by
      rw [pow_succ]
      nlinarith [hApositive, hone]
    calc (1 + ε / r) ^ (r - 1) ≤ (1 + ε / r) ^ ((r - 1) + 1) := hAstep
      _ = (1 + ε / r) ^ r := by
            rw [show (r - 1 : ℕ) + 1 = r from by omega]
      _ ≤ Real.exp ε := hstep
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hεle
  calc ‖U ^ r - W ^ r‖ ≤ (r : ℝ) * (ε / r) * (1 + ε / r) ^ (r - 1) :=
        hgeometric
    _ = ε * (1 + ε / r) ^ (r - 1) := by field_simp [hrR.ne']
    _ ≤ ε * Real.exp 1 := by nlinarith [hexponent, hε.le]
    _ = Real.exp 1 * ε := mul_comm _ _

/-- The repeated product error acts on genuine Euclidean quantum states. -/
theorem repeated_mpf_vector_error_le_exp
    (U W : Matrix I I ℂ) {r : ℕ} {ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hU : ‖U‖ ≤ 1) (herr : ‖U - W‖ ≤ ε / r) (x : EuclideanSpace ℂ I) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (U ^ r - W ^ r) x‖
      ≤ Real.exp 1 * ε * ‖x‖ := by
  have hoperator := repeated_mpf_error_le_exp U W hr hε hεle hU herr
  have haction :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (U ^ r - W ^ r)).le_opNorm x
  rw [Matrix.l2_opNorm_toEuclideanCLM] at haction
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (U ^ r - W ^ r) x‖
      ≤ ‖U ^ r - W ^ r‖ * ‖x‖ := haction
    _ ≤ Real.exp 1 * ε * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right hoperator (norm_nonneg x)

/-- The `e` growth factor is a uniform constant outside every input quantifier. -/
theorem repeated_mpf_growth_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] [DecidableEq J] [Nonempty J],
      ∀ (U W : Matrix J J ℂ) (r : ℕ) (ε : ℝ), 0 < r → 0 < ε → ε ≤ 1 →
      ‖U‖ ≤ 1 → ‖U - W‖ ≤ ε / r →
      ‖U ^ r - W ^ r‖ ≤ C * ε := by
  refine ⟨Real.exp 1, Real.exp_pos 1, fun J _ _ _ U W r ε hr hε hεle hU herr => ?_⟩
  exact repeated_mpf_error_le_exp U W hr hε hεle hU herr

end Qatlib.Papers.CommutLCHS26.MainResults
