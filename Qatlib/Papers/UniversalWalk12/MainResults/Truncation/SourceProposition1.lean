/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Krylov Subspace Truncation Bound for Unitary Hamiltonian Evolution

This module proves Proposition 1: if a self-adjoint Hamiltonian `H`, an orthogonal
projection `P`, and a unit state `Φ` satisfy the Krylov annihilation condition
`⟪α, H^n Φ⟫ = 0` for all `(1 - P) α = α` and `n < N₀`, then for `t ≥ 0` the
projected evolution `e^{-it PHP} Φ` approximates `e^{-it H} Φ` within
`2 (e ‖H‖ t / N₀)^{N₀}`.

## Main statements

* `source_prop1_exponential`: `‖exp(-it PHP) Φ - exp(-it H) Φ‖ ≤ 2 * (e ‖H‖ t / N₀)^{N₀}`.

## References

* [Childs, Gosset, and Webb, 2013][ChildsGossetWebb2013], Proposition 1, Eqs. (33)--(38), p. 21.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Set

namespace Qatlib.Papers.UniversalWalk12.MainResults.Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private lemma norm_exp_skew_apply (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (t : ℝ) (ψ : E) :
    ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • A) ψ‖ = ‖ψ‖ := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff, star_smul, hA.star_eq]
  simp [star_mul, mul_comm]

/-- Compare the cancelled exponential series with the series at the cutoff. -/
private lemma exp_apply_sub_le (A B : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : 0 ≤ x) (hxN : x ≤ N)
    (hA : ‖A‖ ≤ x) (hB : ‖B‖ ≤ x)
    (hpow : ∀ n < N, (A ^ n) ψ = (B ^ n) ψ) :
    ‖NormedSpace.exp A ψ - NormedSpace.exp B ψ‖ ≤
      2 * (Real.exp 1 * x / N) ^ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 ≤ x / N := div_nonneg hx hNpos.le
  have hr1 : x / N ≤ 1 := (div_le_one hNpos).2 hxN
  have hterm (C : E →L[ℂ] E) (hC : ‖C‖ ≤ x) (n : ℕ) :
      ‖(C ^ n) ψ‖ ≤ x ^ n := by
    induction n with
    | zero => simpa using hψ.le
    | succ n ih =>
      rw [pow_succ']
      calc
        ‖(C * C ^ n) ψ‖ ≤ ‖C‖ * ‖(C ^ n) ψ‖ := C.le_opNorm _
        _ ≤ x * x ^ n := mul_le_mul hC ih (norm_nonneg _) hx
        _ = x ^ (n + 1) := by ring
  have hs := ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).sub
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B)).map
      (ContinuousLinearMap.apply ℂ E ψ) (ContinuousLinearMap.apply ℂ E ψ).continuous
  have hg := (NormedSpace.expSeries_div_hasSum_exp (N : ℝ)).mul_left
    (2 * (x / N) ^ N)
  have hbound : ‖NormedSpace.exp A ψ - NormedSpace.exp B ψ‖ ≤
      (2 * (x / N) ^ N) * NormedSpace.exp (N : ℝ) := by
    apply hs.norm_le_of_bounded hg
    intro n
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, sub_apply,
      smul_apply, ← smul_sub]
    by_cases hn : n < N
    · rw [hpow n hn, sub_self, smul_zero, norm_zero]
      positivity
    · have hratio := pow_le_pow_of_le_one hr hr1 (Nat.le_of_not_gt hn)
      have hpower : x ^ n ≤ (x / N) ^ N * (N : ℝ) ^ n := by
        calc
          x ^ n = (x / N) ^ n * (N : ℝ) ^ n := by
            rw [← mul_pow, div_mul_cancel₀ _ hNpos.ne']
          _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)
      calc
        ‖(n.factorial : ℂ)⁻¹ • ((A ^ n) ψ - (B ^ n) ψ)‖
            = (n.factorial : ℝ)⁻¹ * ‖(A ^ n) ψ - (B ^ n) ψ‖ := by
              simp [norm_smul]
        _ ≤ (n.factorial : ℝ)⁻¹ * (x ^ n + x ^ n) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (hterm A hA n) (hterm B hB n))
        _ ≤ (2 * (x / N) ^ N) * ((N : ℝ) ^ n / n.factorial) := by
          convert mul_le_mul_of_nonneg_left hpower
            (show 0 ≤ 2 * (n.factorial : ℝ)⁻¹ by positivity) using 1 <;> ring
  calc
    _ ≤ (2 * (x / N) ^ N) * NormedSpace.exp (N : ℝ) := hbound
    _ = 2 * (Real.exp 1 * x / N) ^ N := by
      rw [← Real.exp_eq_exp_ℝ, show Real.exp (N : ℝ) = Real.exp 1 ^ N by
        rw [← Real.exp_nat_mul, mul_one]]
      rw [mul_assoc, ← mul_pow]
      congr 2
      ring

/-- **Proposition 1**: under Krylov subspace containment up to order `N₀ > 0`,
`‖exp(-it PHP) Φ - exp(-it H) Φ‖ ≤ 2 (e ‖H‖ t / N₀)^{N₀}` for all `t ≥ 0`. -/
theorem source_prop1_exponential
    (H P : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hPidem : P * P = P) (hPself : star P = P)
    (Φ : E) (hΦ : ‖Φ‖ = 1)
    (N₀ : ℕ) (hN₀ : 0 < N₀)
    (horth : ∀ α : E, (1 - P) α = α → ∀ n : ℕ, n < N₀ → inner (𝕜 := ℂ) α ((H ^ n) Φ) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ
        - NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ‖
      ≤ 2 * ((Real.exp 1 * ‖H‖ * t / (N₀ : ℝ)) ^ N₀) := by
  have hPsymm := (show IsSelfAdjoint P from hPself).isSymmetric
  have hPnorm : ‖P‖ ≤ 1 := IsStarProjection.norm_le P ⟨hPidem, hPself⟩
  have hPHP : IsSelfAdjoint (P * H * P) := by
    change star (P * H * P) = P * H * P
    simp only [star_mul, hPself, hH.star_eq, mul_assoc]
  have hPHPnorm : ‖P * H * P‖ ≤ ‖H‖ := by
    calc
      ‖P * H * P‖ ≤ ‖P‖ * ‖H‖ * ‖P‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖H‖ * 1 := by gcongr
      _ = ‖H‖ := by ring
  have hcontain (n : ℕ) (hn : n < N₀) : P ((H ^ n) Φ) = (H ^ n) Φ := by
    let v := (H ^ n) Φ
    have hPv : P (P v) = P v := congrArg (fun C : E →L[ℂ] E => C v) hPidem
    have hPa : P ((1 - P) v) = 0 := by
      simp [hPv]
    have hQa : (1 - P) ((1 - P) v) = (1 - P) v := by
      simp [hPv]
    have ha : inner (𝕜 := ℂ) ((1 - P) v) ((1 - P) v) = 0 := by
      rw [sub_apply, one_apply_eq_self, inner_sub_right,
        ← hPsymm.apply_clm, show P (v - P v) = 0 from hPa, inner_zero_left, sub_zero]
      exact horth _ hQa n hn
    have hz := (inner_self_eq_zero (𝕜 := ℂ)).1 ha
    exact (sub_eq_zero.1 (show v - P v = 0 from hz)).symm
  have hpows (n : ℕ) (hn : n < N₀) : ((P * H * P) ^ n) Φ = (H ^ n) Φ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn' : n < N₀ := Nat.lt_of_succ_lt hn
      rw [pow_succ', pow_succ']
      change P (H (P (((P * H * P) ^ n) Φ))) = H ((H ^ n) Φ)
      rw [ih hn', hcontain n hn']
      simpa only [pow_succ', mul_apply_eq_comp] using hcontain (n + 1) hn
  by_cases hlarge : 1 ≤ Real.exp 1 * ‖H‖ * t / (N₀ : ℝ)
  · calc
      _ ≤ ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖ +
          ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_exp_skew_apply _ hPHP, norm_exp_skew_apply _ hH, hΦ]; norm_num
      _ ≤ 2 * (Real.exp 1 * ‖H‖ * t / (N₀ : ℝ)) ^ N₀ := by
        nlinarith [one_le_pow₀ hlarge (n := N₀)]
  · have hNpos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
    have hexp : 1 ≤ Real.exp 1 := by simp
    have hx : ‖H‖ * t ≤ (N₀ : ℝ) := by
      have hlt := (div_lt_one hNpos).1 (lt_of_not_ge hlarge)
      nlinarith [mul_nonneg (norm_nonneg H) ht]
    have hc : ‖-(t : ℂ) * Complex.I‖ = t := by
      simp [Complex.norm_real, Real.norm_of_nonneg ht]
    have h := exp_apply_sub_le
      ((-(t : ℂ) * Complex.I) • (P * H * P))
      ((-(t : ℂ) * Complex.I) • H) Φ hΦ N₀ hN₀ (‖H‖ * t)
      (mul_nonneg (norm_nonneg H) ht) hx
      (by rw [norm_smul, hc]; nlinarith [mul_le_mul_of_nonneg_left hPHPnorm ht])
      (by rw [norm_smul, hc]; exact le_of_eq (mul_comm _ _))
      (by intro n hn; simp only [smul_pow, smul_apply, hpows n hn])
    simpa only [mul_assoc] using h

end Qatlib.Papers.UniversalWalk12.MainResults.Truncation
