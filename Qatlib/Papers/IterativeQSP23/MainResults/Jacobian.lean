/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Shared QSP products and a numerical operation-count bound

The sweep and FFT counts are explicit scalar definitions. Their asymptotic
bound does not prove that an implementation executes this many operations.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.IterativeQSP23.MainResults.Jacobian

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs (PhaseRotation)

/-- Left-associated product of a list of two-dimensional complex matrices. -/
def matProd (l : List (Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  l.foldl (· * ·) 1

/-- Changing one isolated phase leaves its prefix and suffix shared. -/
theorem qsp_prefix (pre suf : List (Matrix (Fin 2) (Fin 2) ℂ)) (φ₁ φ₂ : ℝ) :
    (matProd pre * PhaseRotation φ₁ * matProd suf) 0 0 -
      (matProd pre * PhaseRotation φ₂ * matProd suf) 0 0 =
      (matProd pre * (PhaseRotation φ₁ - PhaseRotation φ₂) * matProd suf) 0 0 := by
  rw [mul_sub, sub_mul]
  rfl

/-- The selected entry is a two-term prefix/suffix contraction. -/
theorem qsp_entry (pre suf : List (Matrix (Fin 2) (Fin 2) ℂ)) (φ : ℝ) :
    (matProd pre * PhaseRotation φ * matProd suf) 0 0 =
      ∑ k : Fin 2, (matProd pre * PhaseRotation φ) 0 k * matProd suf k 0 := by
  simp only [Matrix.mul_apply]

/-- Numerical count assigned to the shared sweep. -/
def sweepCount (d : ℕ) : ℕ := (d + 1) * (d + 1)

/-- Numerical count assigned to independent column evaluation. -/
def naiveCount (d : ℕ) : ℕ := (d + 1) * (d + 1) * (d + 1)

/-- The two numerical counts differ by exactly one factor of the phase length. -/
theorem count_factor (d : ℕ) : naiveCount d = sweepCount d * (d + 1) := rfl

/-- Numerical FFT count using the integer base-two logarithm. -/
def fftCost (d : ℕ) : ℕ := (d + 1) * (d + 1) * Nat.log 2 (d + 1)

/-- Sum of the numerical sweep and FFT counts. -/
def totalCost (d : ℕ) : ℕ := sweepCount d + fftCost d

/-- The numerical total count is eventually bounded by a constant times d² log d. -/
theorem cost_bound (d : ℕ) (hd : 2 ≤ d) :
    (totalCost d : ℝ) ≤ (12 / Real.log 2) * (d : ℝ) ^ 2 * Real.log d := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hld : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
  have hlog : Real.log ((d : ℝ) + 1) ≤ 2 * Real.log d := by
    calc Real.log ((d : ℝ) + 1) ≤ Real.log ((d : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log d := by rw [Real.log_pow]; norm_num
  have hnlog : (Nat.log 2 (d + 1) : ℝ) ≤ 2 * Real.log d / Real.log 2 := by
    calc (Nat.log 2 (d + 1) : ℝ) ≤ Real.logb 2 ((d : ℝ) + 1) := by
          simpa using Real.natLog_le_logb (d + 1) 2
      _ ≤ _ := by
        rw [Real.logb]
        exact div_le_div_of_nonneg_right hlog hl2.le
  have hs : ((d : ℝ) + 1) ^ 2 ≤ 4 * (d : ℝ) ^ 2 := by nlinarith
  have hx : 0 ≤ 1 + 2 * Real.log d / Real.log 2 := by positivity
  have he : (totalCost d : ℝ) = ((d : ℝ) + 1) ^ 2 *
      (1 + (Nat.log 2 (d + 1) : ℝ)) := by
    simp only [totalCost, sweepCount, fftCost, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  rw [he]
  calc
    _ ≤ ((d : ℝ) + 1) ^ 2 * (1 + 2 * Real.log d / Real.log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ ≤ (4 * (d : ℝ) ^ 2) * (1 + 2 * Real.log d / Real.log 2) :=
      mul_le_mul_of_nonneg_right hs hx
    _ ≤ (4 * (d : ℝ) ^ 2) * (3 * Real.log d / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (le_div_iff₀ hl2).2
      rw [add_mul, div_mul_cancel₀ _ hl2.ne']
      nlinarith
    _ = _ := by ring

/-- The explicit numerical count satisfies the original asymptotic scalar contract. -/
theorem cost_bigO : Asymptotics.IsBigO (Filter.atTop : Filter ℕ)
    (fun d : ℕ => (totalCost d : ℝ)) (fun d : ℕ => (d : ℝ) ^ 2 * Real.log d) := by
  apply Asymptotics.IsBigO.of_bound (12 / Real.log 2)
  filter_upwards [Filter.eventually_ge_atTop 2] with d hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hn : 0 ≤ (d : ℝ) ^ 2 * Real.log d := by
    apply mul_nonneg (sq_nonneg _)
    exact Real.log_nonneg (by linarith)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ totalCost d from Nat.cast_nonneg _),
    abs_of_nonneg hn, mul_assoc] using cost_bound d hd

end Qatlib.Papers.IterativeQSP23.MainResults.Jacobian
