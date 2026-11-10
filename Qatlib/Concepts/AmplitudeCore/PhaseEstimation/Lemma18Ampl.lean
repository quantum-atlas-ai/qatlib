/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Stat

open scoped BigOperators

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

lemma zoo_amplified_qft_lemma18_exp_pow (θ : ℝ) (k : ℕ) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ k =
      Complex.exp (((θ * (k : ℝ) : ℝ) : ℂ) * Complex.I) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Complex.exp_add]
      congr 1
      push_cast
      ring

lemma zoo_amplified_qft_lemma18_chord_sq (θ : ℝ) :
    ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 = 4 * (Real.sin (θ / 2)) ^ 2 := by
  have hre : (1 - Complex.exp ((θ : ℂ) * Complex.I)).re = 1 - Real.cos θ := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (1 - Complex.exp ((θ : ℂ) * Complex.I)).im = - Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 : Real.cos (2 * (θ / 2)) = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      rw [Real.cos_two_mul', Real.cos_sq']; ring
    rwa [show 2 * (θ / 2) = θ from by ring] at h1
  calc ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2
      = Complex.normSq (1 - Complex.exp ((θ : ℂ) * Complex.I)) :=
        (Complex.normSq_eq_norm_sq _).symm
    _ = (1 - Real.cos θ) ^ 2 + Real.sin θ ^ 2 := by
        rw [Complex.normSq_apply, hre, him]; ring
    _ = 4 * (Real.sin (θ / 2)) ^ 2 := by
        rw [Real.sin_sq, hcos]; ring

lemma zoo_amplified_qft_lemma18_norm_one_sub_pow (N k : ℕ) :
    ‖1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) ^ k‖ ^ 2
      = 4 * (Real.sin (Real.pi * (k : ℝ) / (N : ℝ))) ^ 2 := by
  rw [zoo_amplified_qft_lemma18_exp_pow (-2 * Real.pi / (N : ℝ)) k,
    zoo_amplified_qft_lemma18_chord_sq ((-2 * Real.pi / (N : ℝ)) * (k : ℝ))]
  congr 1
  have hang : -2 * Real.pi / (N : ℝ) * (k : ℝ) / 2
      = -(Real.pi * (k : ℝ) / (N : ℝ)) := by ring
  rw [hang, Real.sin_neg, neg_sq]

lemma zoo_amplified_qft_lemma18_sin_ne_zero {N k : ℕ} (hN : 0 < N) (hmod : k % N ≠ 0) :
    Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ≠ 0 := by
  intro hs
  rw [Real.sin_eq_zero_iff] at hs
  obtain ⟨n, hn⟩ := hs
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have h2 : (↑n * Real.pi) * (N : ℝ) = Real.pi * (k : ℝ) := by
    have h : (↑n * Real.pi) * (N : ℝ) = (Real.pi * (k : ℝ) / (N : ℝ)) * (N : ℝ) := by
      rw [hn]
    rw [div_mul_cancel₀ _ hN'] at h
    exact h
  have h3 : Real.pi * ((n : ℝ) * (N : ℝ)) = Real.pi * (k : ℝ) := by
    linear_combination h2
  have h4 : (n : ℝ) * (N : ℝ) = (k : ℝ) := mul_left_cancel₀ Real.pi_ne_zero h3
  have h5 : n * (N : ℤ) = (k : ℤ) := by exact_mod_cast h4
  have hdvd : (N : ℤ) ∣ (k : ℤ) := ⟨n, by rw [← h5]; ring⟩
  rw [Int.natCast_dvd_natCast] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_mod_right] at hmod
  exact hmod rfl

theorem zoo_amplified_qft_lemma18 :
    ∀ (n : ℕ),
      let N : ℕ := 2 ^ n;
      ∀ (M P : ℕ) (y : Fin N),
        0 < M →
        0 < P →
        (P * y.val) % N ≠ 0 →
        let ω : ℂ := Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I);
        ‖(1 - ω ^ (M * P * y.val)) / (1 - ω ^ (P * y.val))‖ ^ 2 =
          (Real.sin (Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 /
            (Real.sin (Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 ∧
        (Real.sin (Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 /
            (Real.sin (Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 ≤
          (M : ℝ) ^ 2 := by
  intro n N M P y hM hP hmod ω
  have hNdef : N = 2 ^ n := rfl
  have hN : 0 < N := by rw [hNdef]; positivity
  have hE1 : ‖Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hden_ne :
      (1 : ℂ) -
          Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) ^ (P * y.val)
        ≠ 0 := by
    intro hz
    have h0 : ‖(1 : ℂ) -
        Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) ^ (P * y.val)‖ ^ 2
        = 0 := by rw [hz]; simp
    rw [zoo_amplified_qft_lemma18_norm_one_sub_pow] at h0
    have hsq0 : (Real.sin (Real.pi * ((P * y.val : ℕ) : ℝ) / (N : ℝ))) ^ 2 = 0 :=
      (mul_eq_zero.mp h0).resolve_left (by norm_num)
    have hB : Real.sin (Real.pi * ((P * y.val : ℕ) : ℝ) / (N : ℝ)) = 0 :=
      sq_eq_zero_iff.mp hsq0
    exact zoo_amplified_qft_lemma18_sin_ne_zero hN hmod hB
  have hFirst :
      ‖(1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (M * P * y.val)) /
          (1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val))‖ ^ 2 =
        (Real.sin (Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 /
          (Real.sin (Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ))) ^ 2 := by
    rw [norm_div, div_pow,
      zoo_amplified_qft_lemma18_norm_one_sub_pow N (M * P * y.val),
      zoo_amplified_qft_lemma18_norm_one_sub_pow N (P * y.val)]
    have hMj : Real.pi * ((M * P * y.val : ℕ) : ℝ) / (N : ℝ)
        = Real.pi * (M : ℝ) * (P : ℝ) * (y.val : ℝ) / (N : ℝ) := by push_cast; ring
    have hPk : Real.pi * ((P * y.val : ℕ) : ℝ) / (N : ℝ)
        = Real.pi * (P : ℝ) * (y.val : ℝ) / (N : ℝ) := by push_cast; ring
    rw [hMj, hPk, mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]
  have hq1 :
      Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) ^ (P * y.val)
        ≠ 1 := by
    intro hq
    exact hden_ne (sub_eq_zero.mpr hq.symm)
  have hj :
      Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) ^ (M * P * y.val)
        = (Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)) ^ M := by
    rw [← pow_mul]
    congr 1
    ring
  have hgeom :
      (1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (M * P * y.val)) /
          (1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val))
        = ∑ r ∈ Finset.range M,
            (Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
              ^ (P * y.val)) ^ r := by
    have h4 : (1 - (Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)) ^ M) /
          (1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val))
        = ((Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)) ^ M - 1) /
          (Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val) - 1) := by
      have e1 : (1 : ℂ) - (Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)) ^ M
          = -(((Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)) ^ M) - 1) := by ring
      have e2 : (1 : ℂ) - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)
          = -((Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)) - 1) := by ring
      rw [e1, e2, neg_div_neg_eq]
    rw [geom_sum_eq hq1 M, ← h4, ← hj]
  have hnorm :
      ‖(1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (M * P * y.val)) /
          (1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val))‖ ≤ (M : ℝ) := by
    rw [hgeom]
    have hsummand : ∀ r ∈ Finset.range M,
        ‖(Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val)) ^ r‖ = 1 := by
      intro r _
      rw [norm_pow, norm_pow, hE1]
      simp
    calc ‖∑ r ∈ Finset.range M,
            (Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
              ^ (P * y.val)) ^ r‖
        ≤ ∑ r ∈ Finset.range M,
            ‖(Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
              ^ (P * y.val)) ^ r‖ := norm_sum_le _ _
      _ = ∑ r ∈ Finset.range M, (1 : ℝ) := Finset.sum_congr rfl hsummand
      _ = (M : ℝ) := by simp
  have hsq :
      ‖(1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (M * P * y.val)) /
          (1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            ^ (P * y.val))‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
    have h0 := norm_nonneg (((1 : ℂ) -
      Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) ^ (M * P * y.val)) /
        (1 - Complex.exp (((-2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)
          ^ (P * y.val)))
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := le_trans h0 hnorm
    have h := mul_le_mul hnorm hnorm h0 hM0
    rw [pow_two, pow_two]
    exact h
  refine ⟨hFirst, ?_⟩
  rw [← hFirst]
  exact hsq

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
