/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Qatlib.Papers.PhaseEst07.MainResults.QubitExample

set_option backward.isDefEq.respectTransparency false

/-!
# Global optimality of balanced identical-qubit preparations in phase estimation

This file formalizes Section IV, Eq. (48) (p. 6) of [van Dam et al., 2007][VanDamEtAl2007]:
among all normalized `N`-qubit product states `(a |0⟩ + b |1⟩)^{⊗ N}` with real nonnegative
amplitudes `a, b ≥ 0` satisfying `a² + b² = 1`, the phase-estimation variance cost
`sourceQubitCost N a b` is globally minimized at the balanced state `a = b = 1 / √2`, attaining
`sourceQubitMinCost N`.

## Main statements

* `source_qubit_ab_optimal`: for all `N ≥ 1` and `a, b ≥ 0` with `a² + b² = 1`,
  `sourceQubitCost N a b ≥ sourceQubitMinCost N` (Eq. (48)).

## References

* [van Dam et al., 2007][VanDamEtAl2007]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.PhaseEst07.MainResults.QubitExample

namespace Qatlib.Papers.PhaseEst07.MainResults.QubitExample

open scoped BigOperators

/-- Adjacent binomial root weight `√(C(N, k) · C(N, k + 1))`. -/
private def adjBinomWeight (N k : ℕ) : ℝ :=
  Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ))

/-- Symmetry `adjBinomWeight N (N - 1 - k) = adjBinomWeight N k` for `k < N`. -/
private lemma adjBinomWeight_reflect {N k : ℕ} (hk : k < N) :
    adjBinomWeight N (N - 1 - k) = adjBinomWeight N k := by
  unfold adjBinomWeight
  have h1 : N - (N - 1 - k) = k + 1 := by omega
  have h2 : N - (N - 1 - k + 1) = k := by omega
  have hc1 : Nat.choose N (N - 1 - k) = Nat.choose N (k + 1) := by
    rw [← Nat.choose_symm (by omega : N - 1 - k ≤ N), h1]
  have hc2 : Nat.choose N (N - 1 - k + 1) = Nat.choose N k := by
    rw [← Nat.choose_symm (by omega : N - 1 - k + 1 ≤ N), h2]
  rw [hc1, hc2]
  congr 1
  ring

/-- Squared binomial-weight ratio `c(k + 1)² · ((k + 1)(k + 2)) = c(k)² · ((N - k)(N - k - 1))`. -/
private lemma adjBinomWeight_sq_rel (N k : ℕ) :
    adjBinomWeight N (k + 1) ^ 2 * (((k + 1) * (k + 2) : ℕ) : ℝ) =
      adjBinomWeight N k ^ 2 * (((N - k) * (N - k - 1) : ℕ) : ℝ) := by
  unfold adjBinomWeight
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hnat : Nat.choose N (k + 1) * Nat.choose N (k + 2) * ((k + 1) * (k + 2)) =
      Nat.choose N k * Nat.choose N (k + 1) * ((N - k) * (N - k - 1)) := by
    have h1 := Nat.choose_succ_right_eq N k
    have h2 := Nat.choose_succ_right_eq N (k + 1)
    have hsub : N - (k + 1) = N - k - 1 := by omega
    rw [hsub] at h2
    calc Nat.choose N (k + 1) * Nat.choose N (k + 2) * ((k + 1) * (k + 2))
        = (Nat.choose N (k + 1) * (k + 1)) * (Nat.choose N (k + 2) * (k + 2)) := by ring
      _ = (Nat.choose N k * (N - k)) * (Nat.choose N (k + 1) * (N - k - 1)) := by rw [h1, h2]
      _ = Nat.choose N k * Nat.choose N (k + 1) * ((N - k) * (N - k - 1)) := by ring
  exact_mod_cast hnat

/-- Sign alignment between `(2k + 3) c(k + 1) - (2N - 2k - 1) c(k)` and `(N - k)(N - k - 1) -
(k + 1)(k + 2)` for `k + 1 < N`. -/
private lemma deriv_coeff_sign {N k : ℕ} (hk : k + 1 < N) :
    (((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) -
        ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k) *
      (((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) +
        ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k) *
      (((k + 1) * (k + 2) : ℕ) : ℝ) =
    adjBinomWeight N k ^ 2 *
      ((((N - k) * (N - k - 1) : ℕ) : ℝ) - (((k + 1) * (k + 2) : ℕ) : ℝ)) := by
  have hrel := adjBinomWeight_sq_rel N k
  let A : ℝ := (((k + 1) * (k + 2) : ℕ) : ℝ)
  let B : ℝ := (((N - k) * (N - k - 1) : ℕ) : ℝ)
  have hA_sq : ((2 * k + 3 : ℕ) : ℝ) ^ 2 = 4 * A + 1 := by
    dsimp [A]
    push_cast
    ring
  have hB_sq : ((2 * N - 2 * k - 1 : ℕ) : ℝ) ^ 2 = 4 * B + 1 := by
    have hc1 : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N - k), Nat.cast_sub (by omega : k ≤ N), Nat.cast_one]
    have hc2 : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) :=
      Nat.cast_sub (by omega : k ≤ N)
    have hc3 : ((2 * N - 2 * k - 1 : ℕ) : ℝ) = 2 * (N : ℝ) - 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * N - 2 * k), Nat.cast_sub (by omega : 2 * k ≤ 2 * N)]
      push_cast
      ring
    dsimp [B]
    rw [Nat.cast_mul, hc2, hc1, hc3]
    ring
  change (((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) -
      ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k) *
    (((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) +
      ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k) * A =
    adjBinomWeight N k ^ 2 * (B - A)
  calc (((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) -
          ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k) *
        (((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) +
          ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k) * A
      = ((2 * k + 3 : ℕ) : ℝ) ^ 2 * (adjBinomWeight N (k + 1) ^ 2 * A) -
          ((2 * N - 2 * k - 1 : ℕ) : ℝ) ^ 2 * adjBinomWeight N k ^ 2 * A := by ring
    _ = (4 * A + 1) * (adjBinomWeight N k ^ 2 * B) -
          (4 * B + 1) * adjBinomWeight N k ^ 2 * A := by
          rw [hA_sq, hB_sq]
          dsimp [A, B] at hrel ⊢
          rw [hrel]
    _ = adjBinomWeight N k ^ 2 * (B - A) := by ring

/-- Symmetry `sourceQubitCost N b a = sourceQubitCost N a b` for `a, b ≥ 0`. -/
private lemma sourceQubitCost_comm (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sourceQubitCost N b a = sourceQubitCost N a b := by
  have hterm : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → ∀ k < N,
      sourceQubitAmplitude N x y k * sourceQubitAmplitude N x y (k + 1) =
        adjBinomWeight N k * x ^ (2 * N - 2 * k - 1) * y ^ (2 * k + 1) := by
    intro x y _ _ k hk
    unfold sourceQubitAmplitude adjBinomWeight
    have hsqrt : Real.sqrt (Nat.choose N k : ℝ) * Real.sqrt (Nat.choose N (k + 1) : ℝ) =
        Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) :=
      (Real.sqrt_mul (by positivity) _).symm
    have hexpx : (N - k) + (N - (k + 1)) = 2 * N - 2 * k - 1 := by omega
    have hexpy : k + (k + 1) = 2 * k + 1 := by omega
    calc (Real.sqrt (Nat.choose N k : ℝ) * x ^ (N - k) * y ^ k) *
          (Real.sqrt (Nat.choose N (k + 1) : ℝ) * x ^ (N - (k + 1)) * y ^ (k + 1))
        = (Real.sqrt (Nat.choose N k : ℝ) * Real.sqrt (Nat.choose N (k + 1) : ℝ)) *
            (x ^ (N - k) * x ^ (N - (k + 1))) * (y ^ k * y ^ (k + 1)) := by ring
      _ = Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) *
            x ^ (2 * N - 2 * k - 1) * y ^ (2 * k + 1) := by
            rw [hsqrt, ← pow_add, ← pow_add, hexpx, hexpy]
  unfold sourceQubitCost
  congr 2
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_lt : k < N := Finset.mem_range.mp hk
  have hk_ref_lt : N - 1 - k < N := by omega
  rw [hterm b a hb ha (N - 1 - k) hk_ref_lt, hterm a b ha hb k hk_lt,
    adjBinomWeight_reflect hk_lt]
  have he1 : 2 * N - 2 * (N - 1 - k) - 1 = 2 * k + 1 := by omega
  have he2 : 2 * (N - 1 - k) + 1 = 2 * N - 2 * k - 1 := by omega
  rw [he1, he2]
  ring

/-- **Eq. (48)** ([van Dam et al., 2007][VanDamEtAl2007], Section IV, p. 6): among all normalized
product preparations `a² + b² = 1` with `a, b ≥ 0`, the variance cost `sourceQubitCost N a b` is
minimized at `a = b = 1 / √2`, attaining `sourceQubitMinCost N`. -/
theorem source_qubit_ab_optimal (N : ℕ) (hN : 1 ≤ N) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + b ^ 2 = 1) :
    sourceQubitCost N a b ≥ sourceQubitMinCost N := by
  -- Reduce to `b ≤ a` by symmetry.
  suffices hmain : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → y ≤ x → x ^ 2 + y ^ 2 = 1 →
      sourceQubitCost N x y ≥ sourceQubitMinCost N by
    rcases le_total b a with hba | hab
    · exact hmain a b ha hb hba h
    · rw [← sourceQubitCost_comm N ha hb]
      exact hmain b a hb ha hab (by linarith)
  intro x y hx hy hyx hxy
  by_cases hN1 : N = 1
  · subst hN1
    exact source_qubit_optimal_one x y hxy
  by_cases hN2 : N = 2
  · subst hN2
    exact source_qubit_optimal_two x y hxy
  have hN3 : 3 ≤ N := by omega
  -- Parameterize `(x, y) = (cos θ₀, sin θ₀)` with `θ₀ ∈ [0, π / 4]`.
  have hy_sq_le : y ^ 2 ≤ 1 / 2 := by nlinarith
  have hy_le_inv_sqrt2 : y ≤ 1 / Real.sqrt 2 := by
    rw [← Real.sqrt_sq hy,
      show (1 : ℝ) / Real.sqrt 2 = Real.sqrt (1 / 2) by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hy_sq_le
  have hy_le_one : y ≤ 1 := by nlinarith [sq_nonneg x]
  let θ₀ : ℝ := Real.arcsin y
  have hθ₀_nonneg : 0 ≤ θ₀ := Real.arcsin_nonneg.mpr hy
  have hθ₀_le : θ₀ ≤ Real.pi / 4 := by
    have hsin : Real.sin (Real.pi / 4) = 1 / Real.sqrt 2 := by
      rw [Real.sin_pi_div_four, div_eq_div_iff (by norm_num) (Real.sqrt_ne_zero'.mpr (by norm_num))]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have harcsin_pi4 : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 :=
      Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [← harcsin_pi4, hsin]
    exact Real.arcsin_le_arcsin hy_le_inv_sqrt2
  have hsin_θ₀ : Real.sin θ₀ = y := Real.sin_arcsin (by linarith) hy_le_one
  have hcos_θ₀ : Real.cos θ₀ = x := by
    rw [Real.cos_arcsin]
    have hx_sq : 1 - y ^ 2 = x ^ 2 := by linarith
    rw [hx_sq, Real.sqrt_sq hx]
  let g : ℝ → ℝ := fun θ =>
    ∑ k ∈ Finset.range N,
      adjBinomWeight N k * Real.cos θ ^ (2 * N - 2 * k - 1) * Real.sin θ ^ (2 * k + 1)
  have hcorr_eq : ∀ (u v : ℝ), 0 ≤ u → 0 ≤ v →
      (∑ k ∈ Finset.range N, sourceQubitAmplitude N u v k * sourceQubitAmplitude N u v (k + 1)) =
        ∑ k ∈ Finset.range N,
          adjBinomWeight N k * u ^ (2 * N - 2 * k - 1) * v ^ (2 * k + 1) := by
    intro u v _ _
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_lt : k < N := Finset.mem_range.mp hk
    unfold sourceQubitAmplitude adjBinomWeight
    have hsqrt : Real.sqrt (Nat.choose N k : ℝ) * Real.sqrt (Nat.choose N (k + 1) : ℝ) =
        Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) :=
      (Real.sqrt_mul (by positivity) _).symm
    have hexpu : (N - k) + (N - (k + 1)) = 2 * N - 2 * k - 1 := by omega
    have hexpv : k + (k + 1) = 2 * k + 1 := by omega
    calc (Real.sqrt (Nat.choose N k : ℝ) * u ^ (N - k) * v ^ k) *
          (Real.sqrt (Nat.choose N (k + 1) : ℝ) * u ^ (N - (k + 1)) * v ^ (k + 1))
        = (Real.sqrt (Nat.choose N k : ℝ) * Real.sqrt (Nat.choose N (k + 1) : ℝ)) *
            (u ^ (N - k) * u ^ (N - (k + 1))) * (v ^ k * v ^ (k + 1)) := by ring
      _ = Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) *
            u ^ (2 * N - 2 * k - 1) * v ^ (2 * k + 1) := by
            rw [hsqrt, ← pow_add, ← pow_add, hexpu, hexpv]
  have hg_θ₀ : g θ₀ = ∑ k ∈ Finset.range N,
      sourceQubitAmplitude N x y k * sourceQubitAmplitude N x y (k + 1) := by
    rw [hcorr_eq x y hx hy]
    simp [g, hcos_θ₀, hsin_θ₀]
  have hpi4_sc : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 ∧
      Real.sin (Real.pi / 4) = 1 / Real.sqrt 2 := by
    have h1 : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
      rw [div_eq_div_iff (by norm_num) (Real.sqrt_ne_zero'.mpr (by norm_num))]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact ⟨Real.cos_pi_div_four.trans h1, Real.sin_pi_div_four.trans h1⟩
  have hg_pi4 : g (Real.pi / 4) = ∑ k ∈ Finset.range N,
      sourceQubitAmplitude N (1 / Real.sqrt 2) (1 / Real.sqrt 2) k *
        sourceQubitAmplitude N (1 / Real.sqrt 2) (1 / Real.sqrt 2) (k + 1) := by
    rw [hcorr_eq (1 / Real.sqrt 2) (1 / Real.sqrt 2) (by positivity) (by positivity)]
    simp [g, hpi4_sc.1, hpi4_sc.2]
  -- Differentiate `g` and show `g' θ ≥ 0` on `[0, π / 4]`.
  let termDeriv (k : ℕ) (θ : ℝ) : ℝ :=
    adjBinomWeight N k * ((2 * k + 1 : ℕ) : ℝ) * Real.cos θ ^ (2 * N - 2 * k) * Real.sin θ ^ (2 * k) -
      adjBinomWeight N k * ((2 * N - 2 * k - 1 : ℕ) : ℝ) *
        Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)
  have hg_deriv : ∀ θ : ℝ, HasDerivAt g (∑ k ∈ Finset.range N, termDeriv k θ) θ := by
    intro θ
    refine HasDerivAt.fun_sum fun k hk => ?_
    have hk_lt : k < N := Finset.mem_range.mp hk
    have hcos_pow : HasDerivAt (fun t => Real.cos t ^ (2 * N - 2 * k - 1))
        (((2 * N - 2 * k - 1 : ℕ) : ℝ) * Real.cos θ ^ (2 * N - 2 * k - 2) * (-Real.sin θ)) θ := by
      have hexp : 2 * N - 2 * k - 1 - 1 = 2 * N - 2 * k - 2 := by omega
      simpa [hexp] using (Real.hasDerivAt_cos θ).fun_pow (2 * N - 2 * k - 1)
    have hsin_pow : HasDerivAt (fun t => Real.sin t ^ (2 * k + 1))
        (((2 * k + 1 : ℕ) : ℝ) * Real.sin θ ^ (2 * k) * Real.cos θ) θ := by
      simpa using (Real.hasDerivAt_sin θ).fun_pow (2 * k + 1)
    have hprod := ((hcos_pow.const_mul (adjBinomWeight N k)).mul hsin_pow)
    convert hprod using 1
    dsimp [termDeriv]
    have he1 : (2 * N - 2 * k - 1) + 1 = 2 * N - 2 * k := by omega
    have he2 : (2 * k + 1) + 1 = 2 * k + 2 := by omega
    calc adjBinomWeight N k * ((2 * k + 1 : ℕ) : ℝ) * Real.cos θ ^ (2 * N - 2 * k) *
          Real.sin θ ^ (2 * k) -
        adjBinomWeight N k * ((2 * N - 2 * k - 1 : ℕ) : ℝ) *
          Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)
        = adjBinomWeight N k * ((2 * k + 1 : ℕ) : ℝ) *
            (Real.cos θ ^ (2 * N - 2 * k - 1) * Real.cos θ) * Real.sin θ ^ (2 * k) -
          adjBinomWeight N k * ((2 * N - 2 * k - 1 : ℕ) : ℝ) *
            Real.cos θ ^ (2 * N - 2 * k - 2) * (Real.sin θ * Real.sin θ ^ (2 * k + 1)) := by
          rw [← pow_succ, he1, ← pow_succ', he2]
      _ = _ := by ring
  have hg'_nonneg : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      0 ≤ ∑ k ∈ Finset.range N, termDeriv k θ := by
    intro θ hθ
    have hsin_nonneg : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hsin_le : Real.sin θ ≤ Real.sin (Real.pi / 4) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]) hθ.2
    have hcos_ge : Real.cos (Real.pi / 4) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos]) hθ.2
    have hsin_le_cos : Real.sin θ ≤ Real.cos θ := by
      have heq : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
        rw [hpi4_sc.1, hpi4_sc.2]
      linarith
    have hcos_nonneg : 0 ≤ Real.cos θ := le_trans hsin_nonneg hsin_le_cos
    -- Reindex `∑_{k < N} termDeriv k θ` into boundary + interior sum over `range (N - 1)`.
    let e (k : ℕ) : ℝ :=
      ((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) -
        ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k
    have hsplit : (∑ k ∈ Finset.range N, termDeriv k θ) =
        (adjBinomWeight N 0 * Real.cos θ ^ (2 * N) -
          adjBinomWeight N (N - 1) * Real.sin θ ^ (2 * N)) +
        ∑ k ∈ Finset.range (N - 1),
          e k * Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2) := by
      have hrange : Finset.range N = Finset.range ((N - 1) + 1) :=
        congrArg Finset.range (by omega : N = (N - 1) + 1)
      dsimp only [termDeriv]
      rw [Finset.sum_sub_distrib]
      have h1 : (∑ x ∈ Finset.range N,
          adjBinomWeight N x * ((2 * x + 1 : ℕ) : ℝ) * Real.cos θ ^ (2 * N - 2 * x) *
            Real.sin θ ^ (2 * x)) =
          adjBinomWeight N 0 * Real.cos θ ^ (2 * N) +
            ∑ k ∈ Finset.range (N - 1),
              ((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) *
                Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2) := by
        conv_lhs => rw [hrange, Finset.sum_range_succ']
        have hb0 : adjBinomWeight N 0 * ((2 * 0 + 1 : ℕ) : ℝ) *
            Real.cos θ ^ (2 * N - 2 * 0) * Real.sin θ ^ (2 * 0) =
            adjBinomWeight N 0 * Real.cos θ ^ (2 * N) := by simp
        rw [hb0, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have ha1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
        have ha2 : 2 * N - 2 * (k + 1) = 2 * N - 2 * k - 2 := by omega
        have ha3 : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [ha1, ha2, ha3]
        ring
      have h2 : (∑ x ∈ Finset.range N,
          adjBinomWeight N x * ((2 * N - 2 * x - 1 : ℕ) : ℝ) *
            Real.cos θ ^ (2 * N - 2 * x - 2) * Real.sin θ ^ (2 * x + 2)) =
          (∑ k ∈ Finset.range (N - 1),
            ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k *
              Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)) +
          adjBinomWeight N (N - 1) * Real.sin θ ^ (2 * N) := by
        conv_lhs => rw [hrange, Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun k _ => by ring
        · have hb1 : 2 * N - 2 * (N - 1) - 1 = 1 := by omega
          have hb2 : 2 * N - 2 * (N - 1) - 2 = 0 := by omega
          have hb3 : 2 * (N - 1) + 2 = 2 * N := by omega
          rw [hb1, hb2, hb3]
          simp
      rw [h1, h2]
      have hsub_sum :
          (∑ k ∈ Finset.range (N - 1),
              ((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) *
                Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)) -
            (∑ k ∈ Finset.range (N - 1),
              ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k *
                Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)) =
            ∑ k ∈ Finset.range (N - 1),
              e k * Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp [e]
        ring
      linarith
    rw [hsplit]
    have hbnd_nonneg : 0 ≤ adjBinomWeight N 0 * Real.cos θ ^ (2 * N) -
        adjBinomWeight N (N - 1) * Real.sin θ ^ (2 * N) := by
      have hc0 : adjBinomWeight N (N - 1) = adjBinomWeight N 0 := by
        simpa using adjBinomWeight_reflect (show 0 < N by omega)
      rw [hc0]
      have hpow_le : Real.sin θ ^ (2 * N) ≤ Real.cos θ ^ (2 * N) :=
        pow_le_pow_left₀ hsin_nonneg hsin_le_cos (2 * N)
      have hw0 : 0 ≤ adjBinomWeight N 0 := Real.sqrt_nonneg _
      nlinarith
    -- Symmetrize the interior sum via `Finset.sum_range_reflect`.
    let S_int : ℝ := ∑ k ∈ Finset.range (N - 1),
      e k * Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)
    have h2S_nonneg : 0 ≤ 2 * S_int := by
      have href : S_int = ∑ k ∈ Finset.range (N - 1),
          (-e k) * Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * N - 2 * k - 2) := by
        dsimp [S_int]
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk_lt : k < N - 1 := Finset.mem_range.mp hk
        have he_ref : e (N - 1 - 1 - k) = -e k := by
          dsimp [e]
          have hc_a : adjBinomWeight N (N - 1 - 1 - k + 1) = adjBinomWeight N k := by
            have hidx : N - 1 - 1 - k + 1 = N - 1 - k := by omega
            rw [hidx, adjBinomWeight_reflect (by omega)]
          have hc_b : adjBinomWeight N (N - 1 - 1 - k) = adjBinomWeight N (k + 1) := by
            have hidx : N - 1 - 1 - k = N - 1 - (k + 1) := by omega
            rw [hidx, adjBinomWeight_reflect (by omega)]
          have hn1 : 2 * (N - 1 - 1 - k) + 3 = 2 * N - 2 * k - 1 := by omega
          have hn2 : 2 * N - 2 * (N - 1 - 1 - k) - 1 = 2 * k + 3 := by omega
          rw [hc_a, hc_b, hn1, hn2]
          ring
        have hp1 : 2 * N - 2 * (N - 1 - 1 - k) - 2 = 2 * k + 2 := by omega
        have hp2 : 2 * (N - 1 - 1 - k) + 2 = 2 * N - 2 * k - 2 := by omega
        rw [he_ref, hp1, hp2]
      have hdouble : 2 * S_int = ∑ k ∈ Finset.range (N - 1),
          e k * (Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2) -
            Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * N - 2 * k - 2)) := by
        calc 2 * S_int = S_int + S_int := two_mul S_int
          _ = (∑ k ∈ Finset.range (N - 1),
                e k * Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)) +
              (∑ k ∈ Finset.range (N - 1),
                (-e k) * Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * N - 2 * k - 2)) := by
              conv_rhs => rw [← href]
          _ = _ := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun k _ => by ring
      rw [hdouble]
      refine Finset.sum_nonneg fun k hk => ?_
      have hk1 : k + 1 < N := by
        have := Finset.mem_range.mp hk
        omega
      have hsign := deriv_coeff_sign hk1
      have hsum_pos : 0 < (((2 * k + 3 : ℕ) : ℝ) * adjBinomWeight N (k + 1) +
          ((2 * N - 2 * k - 1 : ℕ) : ℝ) * adjBinomWeight N k) *
          (((k + 1) * (k + 2) : ℕ) : ℝ) := by
        have hck_pos : 0 < adjBinomWeight N k := by
          unfold adjBinomWeight
          have h1 : 0 < Nat.choose N k := Nat.choose_pos (by omega)
          have h2 : 0 < Nat.choose N (k + 1) := Nat.choose_pos (by omega)
          exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.mul_pos h1 h2)
        have hck1_nonneg : 0 ≤ adjBinomWeight N (k + 1) := Real.sqrt_nonneg _
        have hcoef_pos : (0 : ℝ) < ((2 * N - 2 * k - 1 : ℕ) : ℝ) := by
          have : 0 < 2 * N - 2 * k - 1 := by omega
          exact_mod_cast this
        have hA_pos : (0 : ℝ) < (((k + 1) * (k + 2) : ℕ) : ℝ) := by positivity
        exact mul_pos (by nlinarith) hA_pos
      rcases le_or_gt (2 * k + 2) N with hsmall | hlarge
      · -- `2k + 2 ≤ N`: `e k ≥ 0` and `cos^{2N-2k-2} sin^{2k+2} ≥ cos^{2k+2} sin^{2N-2k-2}`
        have hAB_le : (k + 1) * (k + 2) ≤ (N - k) * (N - k - 1) := by
          rcases eq_or_lt_of_le hsmall with heq | hlt
          · have h1 : N - k = k + 2 := by omega
            have h2 : N - k - 1 = k + 1 := by omega
            rw [h2, h1, Nat.mul_comm]
          · rw [Nat.mul_comm (N - k) (N - k - 1)]
            exact Nat.mul_le_mul (by omega) (by omega)
        have hAB_real : (((k + 1) * (k + 2) : ℕ) : ℝ) ≤ (((N - k) * (N - k - 1) : ℕ) : ℝ) := by
          exact_mod_cast hAB_le
        have hrhs_nonneg : 0 ≤ adjBinomWeight N k ^ 2 *
            ((((N - k) * (N - k - 1) : ℕ) : ℝ) - (((k + 1) * (k + 2) : ℕ) : ℝ)) :=
          mul_nonneg (sq_nonneg _) (by linarith)
        have he_nonneg : 0 ≤ e k := by
          dsimp [e] at *
          rw [mul_assoc] at hsign
          rw [← hsign] at hrhs_nonneg
          exact nonneg_of_mul_nonneg_left hrhs_nonneg hsum_pos
        have hp_diff : 2 * N - 2 * k - 2 = (2 * k + 2) + (2 * N - 4 * k - 4) := by omega
        have hmon_ge : Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * N - 2 * k - 2) ≤
            Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2) := by
          have hpow_le : Real.sin θ ^ (2 * N - 4 * k - 4) ≤ Real.cos θ ^ (2 * N - 4 * k - 4) :=
            pow_le_pow_left₀ hsin_nonneg hsin_le_cos _
          calc Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * N - 2 * k - 2)
              = (Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * k + 2)) *
                  Real.sin θ ^ (2 * N - 4 * k - 4) := by
                rw [hp_diff, pow_add]
                ring
            _ ≤ (Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * k + 2)) *
                  Real.cos θ ^ (2 * N - 4 * k - 4) :=
                mul_le_mul_of_nonneg_left hpow_le (by positivity)
            _ = Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2) := by
                rw [hp_diff, pow_add]
                ring
        exact mul_nonneg he_nonneg (sub_nonneg.mpr hmon_ge)
      · -- `N < 2k + 2`: `e k ≤ 0` and `cos^{2N-2k-2} sin^{2k+2} ≤ cos^{2k+2} sin^{2N-2k-2}`
        have hBA_le : (N - k) * (N - k - 1) ≤ (k + 1) * (k + 2) :=
          Nat.mul_le_mul (by omega) (by omega)
        have hBA_real : (((N - k) * (N - k - 1) : ℕ) : ℝ) ≤ (((k + 1) * (k + 2) : ℕ) : ℝ) := by
          exact_mod_cast hBA_le
        have hrhs_nonpos : adjBinomWeight N k ^ 2 *
            ((((N - k) * (N - k - 1) : ℕ) : ℝ) - (((k + 1) * (k + 2) : ℕ) : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
        have he_nonpos : e k ≤ 0 := by
          dsimp [e] at *
          rw [mul_assoc] at hsign
          rw [← hsign] at hrhs_nonpos
          by_contra hpos
          push Not at hpos
          have := mul_pos hpos hsum_pos
          linarith
        have hp_diff : 2 * k + 2 = (2 * N - 2 * k - 2) + (4 * k + 4 - 2 * N) := by omega
        have hmon_le : Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2) ≤
            Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * N - 2 * k - 2) := by
          have hpow_le : Real.sin θ ^ (4 * k + 4 - 2 * N) ≤ Real.cos θ ^ (4 * k + 4 - 2 * N) :=
            pow_le_pow_left₀ hsin_nonneg hsin_le_cos _
          calc Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * k + 2)
              = (Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * N - 2 * k - 2)) *
                  Real.sin θ ^ (4 * k + 4 - 2 * N) := by
                rw [hp_diff, pow_add]
                ring
            _ ≤ (Real.cos θ ^ (2 * N - 2 * k - 2) * Real.sin θ ^ (2 * N - 2 * k - 2)) *
                  Real.cos θ ^ (4 * k + 4 - 2 * N) :=
                mul_le_mul_of_nonneg_left hpow_le (by positivity)
            _ = Real.cos θ ^ (2 * k + 2) * Real.sin θ ^ (2 * N - 2 * k - 2) := by
                rw [hp_diff, pow_add]
                ring
        exact mul_nonneg_of_nonpos_of_nonpos he_nonpos (sub_nonpos.mpr hmon_le)
    linarith
  have hg_mono : MonotoneOn g (Set.Icc 0 (Real.pi / 4)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 4))
      (fun θ _ => (hg_deriv θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hg_deriv θ).differentiableAt.differentiableWithinAt) ?_
    intro θ hθ
    rw [(hg_deriv θ).deriv]
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) := by
      simpa [interior_Icc] using hθ
    exact hg'_nonneg θ ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩
  have hg_le : g θ₀ ≤ g (Real.pi / 4) :=
    hg_mono ⟨hθ₀_nonneg, hθ₀_le⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩ hθ₀_le
  rw [← source_qubit_cost_balanced N]
  unfold sourceQubitCost
  rw [← hg_θ₀, ← hg_pi4]
  linarith

end Qatlib.Papers.PhaseEst07.MainResults.QubitExample
