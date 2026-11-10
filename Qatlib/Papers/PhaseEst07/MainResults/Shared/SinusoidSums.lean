/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
set_option warningAsError false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.Shared

open scoped BigOperators

theorem sum_cos_two_pi_div (M : ℕ) (hM : 2 ≤ M) :
    ∑ k : Fin M, Real.cos (2 * Real.pi * (k : ℝ) / (M : ℝ)) = 0 := by
  have hMpos : 0 < M := by omega
  have hndvd : ¬ (M : ℤ) ∣ (1 : ℤ) := by
    intro h
    have hle : (M : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h
    omega
  have hz : ∑ y : Fin M, primRoot M ^ ((1 : ℤ) * (y : ℤ)) = 0 :=
    sum_primRoot_zpow hMpos hndvd
  have hterm : ∀ y : Fin M,
      (primRoot M ^ ((1 : ℤ) * (y : ℤ))).re
        = Real.cos (2 * Real.pi * (y : ℝ) / (M : ℝ)) := by
    intro y
    rw [primRoot_zpow_eq_exp,
      show 2 * Real.pi * Complex.I * (((((1 : ℤ) * (y : ℤ) : ℤ)) : ℝ) / (M : ℝ))
          = ((2 * Real.pi * (y : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
      Complex.exp_ofReal_mul_I_re]
  have hsum : (∑ y : Fin M, Real.cos (2 * Real.pi * (y : ℝ) / (M : ℝ)))
      = (∑ y : Fin M, primRoot M ^ ((1 : ℤ) * (y : ℤ))).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun y _ => (hterm y).symm)
  rw [hsum, hz, Complex.zero_re]

theorem sum_cos_shift (M : ℕ) (hM : 2 ≤ M) :
    ∑ j ∈ Finset.range (M - 1), Real.cos (2 * (((j : ℝ) + 1) * Real.pi / (M : ℝ))) = -1 := by
  have hfull := sum_cos_two_pi_div M hM
  rw [Fin.sum_univ_eq_sum_range (fun k => Real.cos (2 * Real.pi * (k : ℝ) / (M : ℝ))) M] at hfull
  have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel (by omega)
  rw [← hM1, Finset.sum_range_succ'] at hfull
  simp only [hM1, Nat.cast_zero, Nat.cast_add, Nat.cast_one, mul_zero, zero_div,
    Real.cos_zero] at hfull
  have hcongr : (∑ j ∈ Finset.range (M - 1),
        Real.cos (2 * Real.pi * ((j : ℝ) + 1) / (M : ℝ)))
      = (∑ j ∈ Finset.range (M - 1),
        Real.cos (2 * (((j : ℝ) + 1) * Real.pi / (M : ℝ)))) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  rw [hcongr] at hfull
  linarith

theorem sum_sin_sq_pi_div (M : ℕ) (hM : 2 ≤ M) :
    ∑ j ∈ Finset.range (M - 1), Real.sin (((j : ℝ) + 1) * Real.pi / (M : ℝ)) ^ 2
      = (M : ℝ) / 2 := by
  have hcos := sum_cos_shift M hM
  have hterm : ∀ j ∈ Finset.range (M - 1),
      Real.sin (((j : ℝ) + 1) * Real.pi / (M : ℝ)) ^ 2
        = 1 / 2 - Real.cos (2 * (((j : ℝ) + 1) * Real.pi / (M : ℝ))) / 2 := by
    intro j _
    exact Real.sin_sq_eq_half_sub _
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.sum_div, hcos]
  have hMp : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hn : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hn]
  ring

theorem sum_cos_odd_zero (M : ℕ) (hM : 2 ≤ M) :
    ∑ k : Fin M, Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (M : ℝ)) = 0 := by
  have hMpos : 0 < M := by omega
  have hndvd : ¬ ((M : ℤ) ∣ (1 : ℤ)) := by
    intro h
    have hle : (M : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h
    omega
  have hz : ∑ k : Fin M, primRoot M ^ ((1 : ℤ) * (k : ℤ)) = 0 :=
    sum_primRoot_zpow hMpos hndvd
  set φ : ℂ := Complex.exp (Complex.I * ((Real.pi / (M : ℝ) : ℝ) : ℂ)) with hφ
  have hterm : ∀ k : Fin M,
      Complex.exp (Complex.I * ((((2 * (k : ℝ) + 1)) * Real.pi / (M : ℝ) : ℝ) : ℂ))
        = φ * primRoot M ^ ((1 : ℤ) * (k : ℤ)) := by
    intro k
    rw [hφ, primRoot_zpow_eq_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsumzero :
      (∑ k : Fin M,
        Complex.exp (Complex.I * ((((2 * (k : ℝ) + 1)) * Real.pi / (M : ℝ) : ℝ) : ℂ))) = 0 := by
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, hz, mul_zero]
  have hre : (∑ k : Fin M, Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (M : ℝ)))
      = (∑ k : Fin M,
          Complex.exp (Complex.I * ((((2 * (k : ℝ) + 1)) * Real.pi / (M : ℝ) : ℝ) : ℂ))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    have harg : Complex.I * ((((2 * (k : ℝ) + 1)) * Real.pi / (M : ℝ) : ℝ) : ℂ)
        = ((((2 * (k : ℝ) + 1)) * Real.pi / (M : ℝ) : ℝ) : ℂ) * Complex.I := mul_comm _ _
    rw [harg, Complex.exp_ofReal_mul_I_re]
  rw [hre, hsumzero, Complex.zero_re]

end Qatlib.Papers.PhaseEst07.MainResults.Shared
