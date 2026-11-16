/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.DiscreteOptim.ReciprocalCost.IntegerChoice
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Actual source scalar cost and exact integer certificates

Fixed arXiv:1005.1318v3 Section IV. The source's ceiling-free upper-bound
family has order-dependent factor (25/3)^(k-1) B^(1/(2k)). Its logarithm is
linear plus reciprocal. The paper's nearest-integer prescription is not an
exact integer minimizer in general. We prove a counterexample in this actual
family and a sufficient global integer-minimum certificate. This does not
establish a Hamiltonian simulation error or its primitive execution budget.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.DiscreteOptim.ReciprocalCost.IntegerChoice

namespace Qatlib.Papers.HamEfficiency10.OrderSelection.IntegerChoice

/-- The actual order-dependent ceiling-free bound, with its positive order-independent prefactor. -/
def sourceBound (C B : ℝ) (k : ℕ) : ℝ :=
  C * (25/3 : ℝ)^(k-1) * B^(1 / (2 * (k : ℝ)))

/-- The genuine source bound is positive on every positive input. -/
theorem boundPos {C B : ℝ} (hC : 0 < C) (hB : 0 < B) (k : ℕ) :
    0 < sourceBound C B k := by unfold sourceBound; positivity

/-- The complete source logarithm is the actual shared linear-reciprocal cost. -/
theorem logBound {C B : ℝ} (hC : 0 < C) (hB : 0 < B) {k : ℕ} (hk : 0 < k) :
    Real.log (sourceBound C B k) =
      Real.log C + cost (Real.log (25/3)) (Real.log B / 2) k := by
  have hp : 0 < (25/3 : ℝ)^(k-1) := by positivity
  have hb : 0 < B^(1 / (2 * (k : ℝ))) := Real.rpow_pos_of_pos hB _
  rw [sourceBound, Real.log_mul (mul_pos hC hp).ne' hb.ne',
    Real.log_mul hC.ne' hp.ne', Real.log_pow, Real.log_rpow hB]
  have hc : ((k-1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k from hk), Nat.cast_one]
  rw [hc]
  unfold cost
  ring

/-- A global minimum certificate for the actual source bound, not just its abstract logarithm. -/
theorem boundMin {C B : ℝ} (hC : 0 < C) (hB : 0 < B) {k : ℕ} (hk : 0 < k)
    (hl : Real.log (25/3) * ((k : ℝ)-1) * (k : ℝ) ≤ Real.log B / 2)
    (hr : Real.log B / 2 ≤ Real.log (25/3) * (k : ℝ) * ((k : ℝ)+1)) :
    ∀ j : ℕ, 0 < j → sourceBound C B k ≤ sourceBound C B j := by
  intro j hj
  apply (Real.log_le_log_iff (boundPos hC hB k) (boundPos hC hB j)).mp
  rw [logBound hC hB hk, logBound hC hB hj]
  have hm := globalMin (Real.log_pos (by norm_num : (1 : ℝ) < 25/3)).le hk hl hr j hj
  linarith

/-- A positive source parameter whose continuous logarithmic optimum is 29/20. -/
def badB : ℝ := Real.exp (2 * (841/400 : ℝ) * Real.log (25/3))

/-- The concrete source parameter is positive, so its logarithm has no domain defect. -/
theorem badBPos : 0 < badB := Real.exp_pos _

/-- The counterexample lies deep inside the source small-error parameter regime. -/
theorem badBValid : 8 * Real.exp 1 < badB := by
  have he0 : 0 < Real.exp 1 := Real.exp_pos _
  have he2 : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have ha : (1 : ℝ) < Real.log (25/3) := by
    have h := Real.log_lt_log he0 (he3.trans (by norm_num : (3 : ℝ) < 25/3))
    simpa only [Real.log_exp] using h
  have hx : (4 : ℝ) < 2 * (841/400 : ℝ) * Real.log (25/3) := by nlinarith
  have hs : (4 : ℝ) < Real.exp 1 ^ 2 := by nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have hc : (8 : ℝ) < Real.exp 1 ^ 3 := by
    nlinarith [mul_lt_mul_of_pos_right hs he0]
  have hf : 8 * Real.exp 1 < Real.exp 1 ^ 4 := by
    nlinarith [mul_lt_mul_of_pos_right hc he0]
  have he4 : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
    simp
  exact hf.trans (he4 ▸ Real.exp_lt_exp.mpr hx)

/-- Its actual continuous stationary point rounds to the integer one under the printed rule. -/
theorem badRound :
    max 1 ⌊Real.sqrt (Real.log badB / (2 * Real.log (25/3))) + 1/2⌋₊ = 1 := by
  have ha : 0 < Real.log (25/3 : ℝ) := Real.log_pos (by norm_num)
  have hr : Real.log badB / (2 * Real.log (25/3)) = (29/20 : ℝ)^2 := by
    rw [badB, Real.log_exp]
    field_simp
    ring
  rw [hr, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 29/20)]
  norm_num
  exact (Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 39/20)).mpr (by norm_num)

/-- The corrected integer two is globally optimal for this actual source counterexample. -/
theorem exactWinner {C : ℝ} (hC : 0 < C) :
    ∀ j : ℕ, 0 < j → sourceBound C badB 2 ≤ sourceBound C badB j := by
  apply boundMin hC badBPos (by decide : 0 < 2)
  all_goals
    have ha : 0 < Real.log (25/3 : ℝ) := Real.log_pos (by norm_num)
    simp only [badB, Real.log_exp, Nat.cast_ofNat]
    nlinarith

/-- Integer two is strictly cheaper than the printed rounded integer one in the actual source family. -/
theorem roundedLoses {C : ℝ} (hC : 0 < C) : sourceBound C badB 2 < sourceBound C badB 1 := by
  apply (Real.log_lt_log_iff (boundPos hC badBPos 2) (boundPos hC badBPos 1)).mp
  rw [logBound hC badBPos (by decide : 0 < 2), logBound hC badBPos (by decide : 0 < 1)]
  have ha : 0 < Real.log (25/3 : ℝ) := Real.log_pos (by norm_num)
  simp only [badB, Real.log_exp, cost, Nat.cast_ofNat, Nat.cast_one]
  nlinarith

end Qatlib.Papers.HamEfficiency10.OrderSelection.IntegerChoice
