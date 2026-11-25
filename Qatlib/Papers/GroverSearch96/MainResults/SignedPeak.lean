/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroverSearch96.MainResults.GainConvergence

@[expose] public section

/-!
# The positive marked amplitude in Section 4

The known-count iteration formula places the final rotation within one
initial angle of `π/2`. The singleton marked amplitude, with the initial
uniform phase convention of [Grover][Grover1996], is the sine of that
rotation and exceeds the source threshold on registers of at least two qubits.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Papers.GroverSearch96.MainResults

namespace Qatlib.Papers.GroverSearch96.MainResults

/-- Section 4's positive real marked amplitude is attained below the
source iteration bound when the register has at least two qubits. -/
theorem section4_signed_amplitude (n : ℕ) (hn : 2 ≤ n) (w : Reg n) :
    ∃ j : ℕ, (j : ℝ) < Real.sqrt (2 * (2 : ℝ) ^ n) ∧
      1 / Real.sqrt 2 < (GroverState ({w} : Finset (Reg n)) j w).re := by
  have hN4 : 4 ≤ Fintype.card (Reg n) := by
    rw [card_reg]
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let N : ℝ := Fintype.card (Reg n)
  have hN : 4 ≤ N := by
    dsimp [N]
    exact_mod_cast hN4
  have hN0 : 0 < N := by linarith
  have hNm : 0 < Fintype.card (Reg n) := by omega
  have hdensity : (1 : ℝ) / N ≤ 1 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  let θ := knownCountAngle (1 / N)
  obtain ⟨hθ, hθhalf, hsin, hsinSq, hcos⟩ :
      0 < θ ∧ θ < Real.pi / 2 ∧ Real.sin θ = Real.sqrt (1 / N) ∧
        (Real.sin θ) ^ 2 = 1 / N ∧ Real.cos θ ≠ 0 :=
    knownCountAngle_spec (by positivity) (by linarith)
  have hsin0 : 0 < Real.sin θ := by rw [hsin]; positivity
  let j := groverIterations θ
  let x := (2 * (j : ℝ) + 1) * θ
  have hphase : |x - Real.pi / 2| ≤ θ := groverIterations_phase_error hθ
  have hsigned : Real.cos θ ≤ Real.sin x := by
    rw [← Real.cos_sub_pi_div_two, ← Real.cos_abs (x - Real.pi / 2)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hphase
  have hcos0 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθhalf⟩
  have hstrict : 1 / Real.sqrt 2 < Real.cos θ := by
    by_contra! hle
    have hsq := pow_le_pow_left₀ hcos0.le hle 2
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)] at hsq
    nlinarith [Real.sin_sq_add_cos_sq θ, hsinSq]
  have hnorm : (Real.sqrt N)⁻¹ * Real.sin x / Real.sin θ = Real.sin x := by
    rw [hsin, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hN0)]
  have hstate : (GroverState ({w} : Finset (Reg n)) j w).re = Real.sin x := by
    have hfrac : (Real.sin θ) ^ 2 =
        (({w} : Finset (Reg n)).card : ℝ) / Fintype.card (Reg n) := by
      simpa only [Finset.card_singleton, Nat.cast_one] using hsinSq
    rw [groverState_eq hNm {w} θ hfrac hsin0.ne' hcos j]
    change (MarkedVector ({w} : Finset (Reg n))
      ((Real.sqrt N)⁻¹ * Real.sin x / Real.sin θ : ℂ) _ w).re = _
    simp only [MarkedVector, Finset.mem_singleton_self, ite_eq_left,
      ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    exact hnorm
  have hbudget : (j : ℝ) ≤ Real.pi / 4 * Real.sqrt N := by
    have h := groverIterations_le hθ hsin0
    change (j : ℝ) ≤ _ at h
    rw [hsin, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at h
    convert h using 1
    field_simp [ne_of_gt (Real.sqrt_pos.2 hN0)]
  have hNpow : N = (2 : ℝ) ^ n := by
    dsimp [N]
    rw [card_reg, Nat.cast_pow]
    norm_num
  have hlt : (j : ℝ) < Real.sqrt (2 * (2 : ℝ) ^ n) := by
    have hpi : Real.pi / 4 < 1 := by linarith [Real.pi_lt_d2]
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    rw [← hNpow]
    calc
      _ ≤ Real.pi / 4 * Real.sqrt N := hbudget
      _ < 1 * Real.sqrt N := mul_lt_mul_of_pos_right hpi hsqrt
      _ ≤ Real.sqrt (2 * N) := by rw [one_mul]; exact Real.sqrt_le_sqrt (by linarith)
  exact ⟨j, hlt, by rw [hstate]; exact hstrict.trans_le hsigned⟩

end Qatlib.Papers.GroverSearch96.MainResults
