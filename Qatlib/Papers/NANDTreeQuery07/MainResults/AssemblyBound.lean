/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NANDTreeQuery07.MainResults

theorem log_rpow_le_mul_rpow {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → Real.log x ^ a ≤ C * x ^ η := by
  rcases eq_or_lt_of_le ha with rfl | hapos
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [Real.rpow_zero]
    have hxη : (1 : ℝ) ≤ x ^ η := Real.one_le_rpow hx hη.le
    nlinarith
  · set e : ℝ := η / a with he
    have he_pos : 0 < e := div_pos hη hapos
    have he_pow_pos : 0 < e ^ a := Real.rpow_pos_of_pos he_pos a
    refine ⟨1 / e ^ a, div_pos one_pos he_pow_pos, fun x hx => ?_⟩
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
    have hstep : Real.log x ≤ x ^ e / e := Real.log_le_rpow_div hx0 he_pos
    have hmono : Real.log x ^ a ≤ (x ^ e / e) ^ a :=
      Real.rpow_le_rpow hlog_nonneg hstep ha
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hxe_nonneg : (0 : ℝ) ≤ x ^ e := (Real.rpow_pos_of_pos hx_pos e).le
    have he_nonneg : (0 : ℝ) ≤ e := he_pos.le
    have hsplit : (x ^ e / e) ^ a = (x ^ e) ^ a / e ^ a :=
      Real.div_rpow hxe_nonneg he_nonneg a
    have hxee : (x ^ e) ^ a = x ^ (e * a) := (Real.rpow_mul hx0 e a).symm
    have hea : e * a = η := by rw [he]; field_simp
    have htarget : (x ^ e / e) ^ a = (1 / e ^ a) * x ^ η := by
      rw [hsplit, hxee, hea]; ring
    calc Real.log x ^ a ≤ (x ^ e / e) ^ a := hmono
      _ = (1 / e ^ a) * x ^ η := htarget

theorem sqrt_log_pow_le_rpow (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : δ / 2 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      (x * Real.log x) ^ ((1 + δ) / 2) ≤ C * x ^ (1 / 2 + ε) := by
  have ha : 0 ≤ (1 + δ) / 2 := by positivity
  have hη : 0 < ε - δ / 2 := by linarith
  obtain ⟨C1, hC1, hbound⟩ := log_rpow_le_mul_rpow ha hη
  refine ⟨C1, hC1, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxl : (0 : ℝ) ≤ x * Real.log x := mul_nonneg hx0 hlog_nonneg
  have hmul : (x * Real.log x) ^ ((1 + δ) / 2)
      = x ^ ((1 + δ) / 2) * Real.log x ^ ((1 + δ) / 2) :=
    Real.mul_rpow hx0 hlog_nonneg
  rw [hmul]
  have hlogb : Real.log x ^ ((1 + δ) / 2) ≤ C1 * x ^ (ε - δ / 2) := hbound x hx
  have hxpow_nonneg : (0 : ℝ) ≤ x ^ ((1 + δ) / 2) :=
    (Real.rpow_pos_of_pos hx_pos ((1 + δ) / 2)).le
  calc x ^ ((1 + δ) / 2) * Real.log x ^ ((1 + δ) / 2)
      ≤ x ^ ((1 + δ) / 2) * (C1 * x ^ (ε - δ / 2)) := by
        exact mul_le_mul_of_nonneg_left hlogb hxpow_nonneg
    _ = C1 * (x ^ ((1 + δ) / 2) * x ^ (ε - δ / 2)) := by ring
    _ = C1 * x ^ ((1 + δ) / 2 + (ε - δ / 2)) := by
        rw [Real.rpow_add hx_pos]
    _ = C1 * x ^ (1 / 2 + ε) := by
        have hexp : (1 + δ) / 2 + (ε - δ / 2) = 1 / 2 + ε := by ring
        rw [hexp]

theorem discrete_query_bound_of_step_bound
    (ε δ : ℝ) (hδ : 0 ≤ δ) (hε : δ / 2 < ε)
    (C₀ c : ℝ) (hC₀ : 0 < C₀) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ K : ℕ,
      (K : ℝ) ≤ C₀ * (3 * (c * Real.sqrt ((2 : ℝ) ^ n * Real.log ((2 : ℝ) ^ n)))) ^ (1 + δ) →
      (2 * K : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (1 / 2 + ε) := by
  obtain ⟨C1, hC1, hbound⟩ := sqrt_log_pow_le_rpow δ ε hδ hε
  refine ⟨2 * C₀ * (3 * c) ^ (1 + δ) * C1, ?_, fun n K hK => ?_⟩
  · have h3c : 0 < 3 * c := by positivity
    have h3cp : 0 < (3 * c) ^ (1 + δ) := Real.rpow_pos_of_pos h3c _
    positivity
  · set N : ℝ := (2 : ℝ) ^ n with hNdef
    have hN1 : (1 : ℝ) ≤ N := by
      rw [hNdef]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
    have hlog_nonneg : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hNL_nonneg : (0 : ℝ) ≤ N * Real.log N := mul_nonneg hN0.le hlog_nonneg
    have hsq : Real.sqrt (N * Real.log N) = (N * Real.log N) ^ (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow _
    have h3t : (3 * (c * Real.sqrt (N * Real.log N))) ^ (1 + δ)
        = (3 * c) ^ (1 + δ) * (N * Real.log N) ^ ((1 + δ) / 2) := by
      rw [hsq]
      rw [show (3 * (c * (N * Real.log N) ^ (1 / 2 : ℝ)))
            = (3 * c) * ((N * Real.log N) ^ (1 / 2 : ℝ)) by ring]
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hNL_nonneg _)]
      congr 1
      rw [← Real.rpow_mul hNL_nonneg (1 / 2) (1 + δ)]
      rw [show (1 / 2 : ℝ) * (1 + δ) = (1 + δ) / 2 by ring]
    have hK1 : (K : ℝ) ≤ C₀ * (3 * c) ^ (1 + δ) * (N * Real.log N) ^ ((1 + δ) / 2) := by
      calc (K : ℝ) ≤ C₀ * (3 * (c * Real.sqrt (N * Real.log N))) ^ (1 + δ) := hK
        _ = C₀ * (3 * c) ^ (1 + δ) * (N * Real.log N) ^ ((1 + δ) / 2) := by
            rw [h3t]; ring
    have hbig : (N * Real.log N) ^ ((1 + δ) / 2) ≤ C1 * N ^ (1 / 2 + ε) := hbound N hN1
    have hnon : (0 : ℝ) ≤ C₀ * (3 * c) ^ (1 + δ) := by positivity
    have hK2 : (K : ℝ) ≤ C₀ * (3 * c) ^ (1 + δ) * (C1 * N ^ (1 / 2 + ε)) := by
      calc (K : ℝ) ≤ C₀ * (3 * c) ^ (1 + δ) * (N * Real.log N) ^ ((1 + δ) / 2) := hK1
        _ ≤ C₀ * (3 * c) ^ (1 + δ) * (C1 * N ^ (1 / 2 + ε)) :=
            mul_le_mul_of_nonneg_left hbig hnon
    have h2 : (2 * K : ℝ) ≤ 2 * (C₀ * (3 * c) ^ (1 + δ) * (C1 * N ^ (1 / 2 + ε))) := by
      linarith
    calc (2 * K : ℝ)
        ≤ 2 * (C₀ * (3 * c) ^ (1 + δ) * (C1 * N ^ (1 / 2 + ε))) := h2
      _ = (2 * C₀ * (3 * c) ^ (1 + δ) * C1) * N ^ (1 / 2 + ε) := by ring
      _ = (2 * C₀ * (3 * c) ^ (1 + δ) * C1) * ((2 : ℝ) ^ n) ^ (1 / 2 + ε) := by rw [hNdef]

end Qatlib.Papers.NANDTreeQuery07.MainResults
