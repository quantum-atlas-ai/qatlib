/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QSDPSolvers17.MainResults

/-- The explicit logarithmic overhead in the source cost ledgers. -/
def logBudget (n m : ℕ) : ℝ := Real.log ((n : ℝ) + 2) + Real.log ((m : ℝ) + 2) + 1

/-- Positive dimensions give nonnegative logarithms controlled by the common overhead. -/
theorem logBudget_bounds (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    1 ≤ logBudget n m ∧ 0 ≤ Real.log (n : ℝ) ∧
      0 ≤ Real.log (m : ℝ) ∧ Real.log (n : ℝ) ≤ logBudget n m ∧
      Real.log (m : ℝ) + 1 ≤ logBudget n m := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have ha0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hb0 : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  have ha := Real.log_le_log hn0 (by linarith : (n : ℝ) ≤ n + 2)
  have hb := Real.log_le_log hm0 (by linarith : (m : ℝ) ≤ m + 2)
  dsimp [logBudget]
  exact ⟨by linarith, Real.log_nonneg hn1, Real.log_nonneg hm1,
    by linarith, by linarith⟩

/-- The source rounds count used only as an arithmetic ledger. -/
def rounds (n : ℕ) (ε : ℝ) : ℝ := 16 * Real.log (n : ℝ) / ε ^ 2

/-- The source failure allowance assigned to one round. -/
def roundFailure (n : ℕ) (ε : ℝ) : ℝ := ε ^ 2 / (400 * Real.log (n : ℝ))

/-- The scalar union-bound ledger before connecting it to any quantum procedure. -/
def totalFailure (n : ℕ) (ε : ℝ) : ℝ := rounds n ε * roundFailure n ε

/-- Multiplying the source round count and per-round allowance gives failure at most four percent. -/
theorem plain_model_success_probability {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (1 : ℝ) - totalFailure n ε ≥ 0.96 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn1)
  unfold totalFailure rounds roundFailure
  field_simp [hlog, hε.ne']
  norm_num

/-- The explicit source Algorithm 4 scalar cost before any circuit implementation bridge. -/
def algorithm4TotalCost (s m n : ℕ) (ε sTr tGibbs tTr : ℝ) : ℝ :=
  rounds n ε *
    ((16 * s * Real.log (n : ℝ) / ε ^ 2) * Real.log (m : ℝ) * (sTr * tGibbs) +
      (16 * s * Real.log (n : ℝ) / ε ^ 2) * Real.sqrt m * tTr * (Real.log (m : ℝ) + 1))

/-- The explicit Algorithm 4 scalar ledger is bounded by its displayed fourth-power logarithmic overhead. -/
theorem plain_model_gate_count (s m n : ℕ) (ε sTr tGibbs tTr : ℝ)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hε : 0 < ε) (hs : 0 < s)
    (hsTr : 0 ≤ sTr) (htGibbs : 0 ≤ tGibbs) (htTr : 0 ≤ tTr) :
    algorithm4TotalCost s m n ε sTr tGibbs tTr ≤
      512 * (s / ε ^ 4) * logBudget n m ^ 4 *
        (sTr * tGibbs + Real.sqrt m * tTr) := by
  obtain ⟨hL1, ha0, hb0, haL, hbL⟩ := logBudget_bounds n m (by omega) hm
  set L := logBudget n m
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hLfour : L ^ 3 ≤ L ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hL0 3) (sub_nonneg.mpr hL1)]
  have ha2 : Real.log (n : ℝ) ^ 2 ≤ L ^ 2 := by gcongr
  have hbL' : Real.log (m : ℝ) ≤ L := by linarith
  have hc1 : Real.log (n : ℝ) ^ 2 * Real.log (m : ℝ) ≤ L ^ 4 := by
    calc _ ≤ L ^ 2 * L := mul_le_mul ha2 hbL' hb0 (sq_nonneg L)
      _ = L ^ 3 := by ring
      _ ≤ L ^ 4 := hLfour
  have hc2 : Real.log (n : ℝ) ^ 2 * (Real.log (m : ℝ) + 1) ≤ L ^ 4 := by
    calc _ ≤ L ^ 2 * L := mul_le_mul ha2 hbL (by linarith) (sq_nonneg L)
      _ = L ^ 3 := by ring
      _ ≤ L ^ 4 := hLfour
  have hX : 0 ≤ sTr * tGibbs := mul_nonneg hsTr htGibbs
  have hY : 0 ≤ Real.sqrt (m : ℝ) * tTr := mul_nonneg (Real.sqrt_nonneg _) htTr
  have hs0 : (0 : ℝ) ≤ s := by exact_mod_cast (show 0 ≤ s by omega)
  have hscale : 0 ≤ (s : ℝ) / ε ^ 4 := div_nonneg hs0 (by positivity)
  have heq : algorithm4TotalCost s m n ε sTr tGibbs tTr =
      256 * ((s : ℝ) / ε ^ 4) *
        (Real.log (n : ℝ) ^ 2 * Real.log (m : ℝ) * (sTr * tGibbs) +
          Real.log (n : ℝ) ^ 2 * (Real.log (m : ℝ) + 1) * (Real.sqrt m * tTr)) := by
    unfold algorithm4TotalCost rounds
    field_simp [hε.ne']
    ring
  rw [heq]
  calc _ ≤ 256 * ((s : ℝ) / ε ^ 4) *
        (L ^ 4 * (sTr * tGibbs) + L ^ 4 * (Real.sqrt m * tTr)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_right hc1 hX)
              (mul_le_mul_of_nonneg_right hc2 hY)) (by positivity)
    _ = 256 * ((s : ℝ) / ε ^ 4) * L ^ 4 * (sTr * tGibbs + Real.sqrt m * tTr) := by ring
    _ ≤ 512 * ((s : ℝ) / ε ^ 4) * L ^ 4 * (sTr * tGibbs + Real.sqrt m * tTr) := by
      have h : 0 ≤ ((s : ℝ) / ε ^ 4) * L ^ 4 * (sTr * tGibbs + Real.sqrt m * tTr) :=
        mul_nonneg (mul_nonneg hscale (pow_nonneg hL0 4)) (add_nonneg hX hY)
      nlinarith

/-- The two scalar Algorithm 4 ledger estimates can be retained together without asserting an algorithm. -/
theorem plain_model_solver (s m n : ℕ) (ε sTr tGibbs tTr : ℝ)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hε : 0 < ε) (hs : 0 < s)
    (hsTr : 0 ≤ sTr) (htGibbs : 0 ≤ tGibbs) (htTr : 0 ≤ tTr) :
    (1 : ℝ) - totalFailure n ε ≥ 0.96 ∧
      algorithm4TotalCost s m n ε sTr tGibbs tTr ≤
        512 * (s / ε ^ 4) * logBudget n m ^ 4 *
          (sTr * tGibbs + Real.sqrt m * tTr) :=
  ⟨plain_model_success_probability hn hε,
    plain_model_gate_count s m n ε sTr tGibbs tTr hn hm hε hs hsTr htGibbs htTr⟩

/-- The Algorithm 5 scalar ledger with trace and Gibbs costs supplied as parameters. -/
def quantumInputCost (n m : ℕ) (ε STr TGibbs TTr : ℝ) : ℝ :=
  (1 / ε ^ 2) *
    ((16 * Real.log (n : ℝ)) * (STr * TGibbs) +
      (16 * Real.log (n : ℝ)) * (Real.sqrt m * TTr))

/-- The two Algorithm 5 scalar ledgers satisfy their explicit cubic-logarithm bound. -/
theorem quantum_input_solver (n m : ℕ) (ε STr TGibbs TTr : ℝ)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hε : 0 < ε)
    (hSTr : 0 ≤ STr) (hTGibbs : 0 ≤ TGibbs) (hTTr : 0 ≤ TTr) :
    (1 - totalFailure n ε ≥ 0.96) ∧
      quantumInputCost n m ε STr TGibbs TTr ≤
        16 * (1 / ε ^ 2) *
          (logBudget n m ^ 3 * (STr * TGibbs + Real.sqrt m * TTr)) := by
  refine ⟨plain_model_success_probability hn hε, ?_⟩
  obtain ⟨hL1, ha0, hb0, haL, hbL⟩ := logBudget_bounds n m (by omega) (by omega)
  set L := logBudget n m
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hL3 : L ≤ L ^ 3 := by
    calc L = L * 1 := by ring
      _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left hL2 hL0
      _ = L ^ 3 := by ring
  have ha3 : Real.log (n : ℝ) ≤ L ^ 3 := le_trans haL hL3
  have hXY : 0 ≤ STr * TGibbs + Real.sqrt (m : ℝ) * TTr :=
    add_nonneg (mul_nonneg hSTr hTGibbs) (mul_nonneg (Real.sqrt_nonneg _) hTTr)
  calc quantumInputCost n m ε STr TGibbs TTr =
      (16 * (1 / ε ^ 2)) * (Real.log (n : ℝ) * (STr * TGibbs + Real.sqrt m * TTr)) := by
        unfold quantumInputCost
        ring
    _ ≤ (16 * (1 / ε ^ 2)) * (L ^ 3 * (STr * TGibbs + Real.sqrt m * TTr)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha3 hXY) (by positivity)

end Qatlib.Papers.QSDPSolvers17.MainResults
