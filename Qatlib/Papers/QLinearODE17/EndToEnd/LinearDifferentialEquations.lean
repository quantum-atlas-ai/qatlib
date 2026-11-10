/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.EndToEnd.LinearDifferentialEquationsDefs
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearODE17.EndToEnd

open Qatlib.Papers.QLinearODE17.EndToEnd
set_option warningAsError false

theorem clause18_source_access_ledger (m ρ bits workspace : ℕ) :
    (sourceAccessLedger m ρ bits workspace).controlledPreparations = (m + 1) * ρ ∧
      (sourceAccessLedger m ρ bits workspace).oracleCalls = m + 1 ∧
      (sourceAccessLedger m ρ bits workspace).classicalBits = bits ∧
      (sourceAccessLedger m ρ bits workspace).peakWorkspace = workspace := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem clause18_source_access_ledger_mono (m m' ρ ρ' : ℕ) (hm : m ≤ m') (hρ : ρ ≤ ρ') :
    (sourceAccessLedger m ρ 0 0).controlledPreparations ≤
      (sourceAccessLedger m' ρ' 0 0).controlledPreparations := by
  simp only [sourceAccessLedger, SourceAccessLedger.controlledPreparations]
  exact Nat.mul_le_mul (Nat.succ_le_succ hm) hρ

theorem clause18_endpoint :
    (∀ m ρ bits workspace : ℕ,
      (sourceAccessLedger m ρ bits workspace).controlledPreparations = (m + 1) * ρ ∧
        (sourceAccessLedger m ρ bits workspace).oracleCalls = m + 1) ∧
      (∀ m m' ρ ρ' : ℕ, m ≤ m' → ρ ≤ ρ' →
        (sourceAccessLedger m ρ 0 0).controlledPreparations ≤
          (sourceAccessLedger m' ρ' 0 0).controlledPreparations) := by
  refine ⟨fun m ρ bits workspace => ⟨rfl, rfl⟩, fun m m' ρ ρ' hm hρ => ?_⟩
  exact clause18_source_access_ledger_mono m m' ρ ρ' hm hρ

theorem clause19_amplified_query_count (pars : Section7Parameters) (s nq r r' : ℕ) (hr : r ≤ r') :
    amplifiedQueryCount r (eq112QueryCount pars s nq) ≤
      amplifiedQueryCount r' (eq112QueryCount pars s nq) := by
  simp only [amplifiedQueryCount]
  exact Nat.mul_le_mul_right _ hr

theorem clause19_query_count_charges_inverse (pars : Section7Parameters) (s nq : ℕ) :
    2 * nq - 1 ≤ eq112QueryCount pars s nq := by
  simp only [eq112QueryCount]
  exact Nat.le_add_right _ _

theorem clause19_endpoint :
    (∀ pars : Section7Parameters, ∀ s nq r r' : ℕ, r ≤ r' →
      amplifiedQueryCount r (eq112QueryCount pars s nq) ≤
        amplifiedQueryCount r' (eq112QueryCount pars s nq)) ∧
      (∀ pars : Section7Parameters, ∀ s nq : ℕ,
        2 * nq - 1 ≤ eq112QueryCount pars s nq) := by
  refine ⟨fun pars s nq r r' hr => clause19_amplified_query_count pars s nq r r' hr,
    fun pars s nq => clause19_query_count_charges_inverse pars s nq⟩

theorem clause20_finite_digit_backend_counts (x : ℝ) (bits : ℕ) :
    finiteDigitBitCount (roundFiniteDigit x bits) = bits + 1 ∧
      finiteDigitGateCount (roundFiniteDigit x bits) = bits := by
  exact ⟨rfl, rfl⟩

theorem clause20_dyadic_magnitude_nonneg (x : ℝ) (bits : ℕ) :
    0 ≤ dyadicMagnitude x bits := by
  simp only [dyadicMagnitude]
  exact div_nonneg (Nat.cast_nonneg (Nat.floor (|x| * 2 ^ bits))) (by positivity)

theorem clause20_dyadic_magnitude_le (x : ℝ) (bits : ℕ) :
    dyadicMagnitude x bits ≤ |x| := by
  have hle : (Nat.floor (|x| * 2 ^ bits) : ℝ) ≤ |x| * 2 ^ bits :=
    Nat.floor_le (by positivity : (0:ℝ) ≤ |x| * 2 ^ bits)
  unfold dyadicMagnitude
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ bits)]
  exact hle

theorem clause20_dyadic_error_bound (x : ℝ) (bits : ℕ) :
    |x| - dyadicMagnitude x bits < finiteDigitErrorBudget bits := by
  have hs : (0:ℝ) < 2 ^ bits := by positivity
  have hfl : |x| * 2 ^ bits < (Nat.floor (|x| * 2 ^ bits) : ℝ) + 1 :=
    Nat.lt_floor_add_one (|x| * 2 ^ bits : ℝ)
  unfold dyadicMagnitude finiteDigitErrorBudget
  rw [sub_div' (by simpa using! hs.ne'), div_lt_iff₀ hs,
    div_mul_cancel₀ 1 (by simpa using! hs.ne')]
  linarith

theorem clause20_finite_digit_sign (x : ℝ) (bits : ℕ) :
    (roundFiniteDigit x bits).sign = decide (x < 0) := rfl

theorem clause20_finite_digit_value_eq (x : ℝ) (bits : ℕ) :
    (roundFiniteDigit x bits).value =
      (if x < 0 then -1 else 1) * dyadicMagnitude x bits := by
  by_cases hsb : (roundFiniteDigit x bits).sign = true
  · have hneg : x < 0 := by
      have hd : decide (x < 0) = true := by
        rw [← clause20_finite_digit_sign]
        exact hsb
      exact of_decide_eq_true hd
    have hval : (roundFiniteDigit x bits).value =
        (-1) * (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits := by
      simp only [FiniteDigit.value, if_pos hsb]
      simp only [roundFiniteDigit]
    refine hval.trans (by rw [dyadicMagnitude, if_pos hneg, mul_div_assoc])
  · have hge : ¬ x < 0 := by
      intro hx
      apply hsb
      rw [clause20_finite_digit_sign]
      exact decide_eq_true hx
    have hval : (roundFiniteDigit x bits).value =
        (1) * (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits := by
      simp only [FiniteDigit.value, if_neg hsb]
      simp only [roundFiniteDigit]
    refine hval.trans (by rw [dyadicMagnitude, if_neg hge, mul_div_assoc])

theorem clause20_finite_digit_value_abs (x : ℝ) (bits : ℕ) :
    |(roundFiniteDigit x bits).value| = dyadicMagnitude x bits := by
  have hvm := clause20_finite_digit_value_eq x bits
  by_cases hneg : x < 0
  · rw [hvm, if_pos hneg, abs_mul, abs_of_nonpos (by norm_num : (-1:ℝ) ≤ 0),
      abs_of_nonneg (clause20_dyadic_magnitude_nonneg x bits)]
    ring
  · rw [hvm, if_neg hneg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)),
      abs_of_nonneg (clause20_dyadic_magnitude_nonneg x bits)]
    ring

theorem clause20_finite_digit_signed_error (x : ℝ) (bits : ℕ) :
    |x - (roundFiniteDigit x bits).value| < finiteDigitErrorBudget bits := by
  have herr := clause20_dyadic_error_bound x bits
  have hle : dyadicMagnitude x bits ≤ |x| := clause20_dyadic_magnitude_le x bits
  by_cases hneg : x < 0
  · have hvm := clause20_finite_digit_value_eq x bits
    have hval : (roundFiniteDigit x bits).value = -dyadicMagnitude x bits := by
      rw [hvm, if_pos hneg]
      ring
    rw [hval]
    have h1 : |x| = -x := abs_of_neg hneg
    have hle' : x + dyadicMagnitude x bits ≤ 0 := by linarith
    rw [show x - -dyadicMagnitude x bits = x + dyadicMagnitude x bits by ring,
      abs_of_nonpos hle']
    rw [h1] at herr
    linarith
  · have hvm := clause20_finite_digit_value_eq x bits
    have hval : (roundFiniteDigit x bits).value = dyadicMagnitude x bits := by
      rw [hvm, if_neg hneg]
      ring
    rw [hval]
    have h1 : |x| = x := abs_of_nonneg (not_lt.mp hneg)
    have hle' : 0 ≤ x - dyadicMagnitude x bits := by linarith
    rw [abs_of_nonneg hle']
    rw [h1] at herr
    linarith

theorem clause20_endpoint :
    (∀ x : ℝ, ∀ bits : ℕ,
      finiteDigitBitCount (roundFiniteDigit x bits) = bits + 1 ∧
        finiteDigitGateCount (roundFiniteDigit x bits) = bits) ∧
      (∀ x : ℝ, ∀ bits : ℕ, 0 ≤ dyadicMagnitude x bits) ∧
      (∀ x : ℝ, ∀ bits : ℕ, dyadicMagnitude x bits ≤ |x|) ∧
      (∀ x : ℝ, ∀ bits : ℕ,
        |x| - dyadicMagnitude x bits < finiteDigitErrorBudget bits) ∧
      (∀ x : ℝ, ∀ bits : ℕ,
        |(roundFiniteDigit x bits).value| = dyadicMagnitude x bits) ∧
      (∀ x : ℝ, ∀ bits : ℕ,
        |x - (roundFiniteDigit x bits).value| < finiteDigitErrorBudget bits) := by
  refine ⟨fun x bits => clause20_finite_digit_backend_counts x bits,
    fun x bits => clause20_dyadic_magnitude_nonneg x bits, ?_, ?_, ?_, ?_⟩
  · intro x bits
    exact clause20_dyadic_magnitude_le x bits
  · intro x bits
    exact clause20_dyadic_error_bound x bits
  · intro x bits
    exact clause20_finite_digit_value_abs x bits
  · intro x bits
    exact clause20_finite_digit_signed_error x bits

theorem clause21_small_order_uniform (k b : ℕ) :
    (Nat.factorial b : ℝ) / (Nat.factorial (k + 1) : ℝ) ≤ (Nat.factorial b : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have hF1 : (1:ℕ) ≤ Nat.factorial (k + 1) := Nat.succ_le_of_lt (Nat.factorial_pos _)
  have hF1' : (1:ℝ) ≤ (Nat.factorial (k + 1) : ℝ) := by exact_mod_cast hF1
  have hfacb : (0:ℝ) ≤ (Nat.factorial b : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hF1' hfacb]

theorem clause21_small_order_mono (k b : ℕ) :
    (Nat.factorial b : ℝ) * (Nat.factorial (k + 1) : ℝ)
      ≤ (Nat.factorial b : ℝ) * (Nat.factorial (k + 2) : ℝ) := by
  rw [Nat.factorial_succ (k + 1)]
  push_cast
  have hk2 : (1:ℝ) ≤ (k + 2 : ℝ) := by
    have h : (1:ℕ) ≤ k + 2 := by omega
    exact_mod_cast h
  have hnonneg : (0:ℝ) ≤ (Nat.factorial (k + 1) : ℝ) := by
    exact Nat.cast_nonneg (Nat.factorial (k + 1))
  have hinner : (Nat.factorial (k + 1) : ℝ)
      ≤ (k + 2 : ℝ) * (Nat.factorial (k + 1) : ℝ) := by
    nlinarith [hk2, hnonneg]
  have hmul : (Nat.factorial b : ℝ) * (Nat.factorial (k + 1) : ℝ)
      ≤ (Nat.factorial b : ℝ) * ((k + 2 : ℝ) * (Nat.factorial (k + 1) : ℝ)) :=
    mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg (Nat.factorial b))
  nlinarith [hmul]

theorem clause21_endpoint :
    (∀ k b : ℕ,
      (Nat.factorial b : ℝ) / (Nat.factorial (k + 1) : ℝ) ≤ (Nat.factorial b : ℝ)) ∧
      (∀ k b : ℕ,
        (Nat.factorial b : ℝ) * (Nat.factorial (k + 1) : ℝ)
          ≤ (Nat.factorial b : ℝ) * (Nat.factorial (k + 2) : ℝ)) := by
  refine ⟨fun k b => clause21_small_order_uniform k b, fun k b => clause21_small_order_mono k b⟩

end Qatlib.Papers.QLinearODE17.EndToEnd
