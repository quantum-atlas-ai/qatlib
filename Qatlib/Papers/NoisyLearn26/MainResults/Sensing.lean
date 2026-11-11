/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels

/-!
# Noise accumulation and sensing estimates

Defines scalar jump probabilities, decoherence time, and precision expressions for interstitial
noise. Elementary exponential bounds and the contractive-channel estimate
`channel_telescoping_bound` provide finite-step controls used in the sensing analysis. See
[CotlerGongKannan2025] for the surrounding analysis.

## Main statements

* `noiseJumpProb_interstitial`: Substituting interstitial noise into `noiseJumpProb` gives `1 -
  exp(-4 * η * τ * n)`.
* `channel_telescoping_bound`: If `Φ = (1 - p) • Ψ + p • χ` and the stated pairwise bound holds
  on the unit ball, the difference between the `N`-fold iterates of `Ψ` and `Φ` has norm at most
  `2 * p * N` for nonnegative `p`.
* `heisenberg_threshold_noise`: For positive `η` and `τ`, the stated small-noise hypotheses give
  decoherence time at most `1 / (4 * η * n)` and precision expression at most `8 * η * n` for `n
  ≥ 1`.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.Sensing

open Qatlib.Papers.NoisyLearn26.MainResults

/-- The scalar jump probability `1 - (1 - lam)^n`. -/
def noiseJumpProb (lam : ℝ) (n : ℕ) : ℝ := 1 - (1 - lam) ^ n

/-- The interstitial noise parameter `1 - exp(-4 * η * τ)`. -/
def interstitialLam (η τ : ℝ) : ℝ := 1 - Real.exp (-(4 * η * τ))

/-- The scalar decoherence-time expression `τ / (2 * noiseJumpProb (interstitialLam η τ) n)`. -/
def sensingDecoherenceTime (η τ : ℝ) (n : ℕ) : ℝ :=
  τ / (2 * noiseJumpProb (interstitialLam η τ) n)

/-- The scalar precision expression `2 * noiseJumpProb (interstitialLam η τ) n / τ`. -/
def sensingPrecision (η τ : ℝ) (n : ℕ) : ℝ :=
  2 * noiseJumpProb (interstitialLam η τ) n / τ

/-- Substituting interstitial noise into `noiseJumpProb` gives `1 - exp(-4 * η * τ * n)`
[CotlerGongKannan2025]. -/
theorem noiseJumpProb_interstitial (η τ : ℝ) (n : ℕ) :
    noiseJumpProb (interstitialLam η τ) n = 1 - Real.exp (-(4 * η * τ * n)) := by
  unfold noiseJumpProb interstitialLam
  have h1 : (1 : ℝ) - (1 - Real.exp (-(4 * η * τ))) = Real.exp (-(4 * η * τ)) := by ring
  rw [h1, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- For `0 ≤ y ≤ 1`, the quantity `1 - exp(-y)` is at least `y / 2`. -/
theorem one_sub_exp_neg_ge {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    y / 2 ≤ 1 - Real.exp (-y) := by
  have hpos : (0 : ℝ) < 1 + y := by linarith
  have hexp : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hdiv : 1 / Real.exp y ≤ 1 / (1 + y) := one_div_le_one_div_of_le hpos hexp
  have hneg : Real.exp (-y) = 1 / Real.exp y := by rw [Real.exp_neg, one_div]
  have hfrac : y / 2 ≤ 1 - 1 / (1 + y) := by
    have heq : (1 : ℝ) - 1 / (1 + y) = y / (1 + y) := by
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_left h0 hpos (by linarith)
  rw [hneg]
  linarith

/-- For nonnegative `y`, the quantity `1 - exp(-y)` is at most `y`. -/
theorem one_sub_exp_neg_le {y : ℝ} (h0 : 0 ≤ y) : 1 - Real.exp (-y) ≤ y := by
  have h := Real.add_one_le_exp (-y)
  linarith

/-- Every iterate of a contractive channel maps a vector of norm at most one to a vector of norm
at most one. -/
theorem norm_iterate_le_one {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (Φ : Channel E) {x : E} (hx : ‖x‖ ≤ 1) (N : ℕ) :
    ‖Channel.iterate Φ N x‖ ≤ 1 := by
  induction N with
  | zero => simpa [Channel.iterate] using hx
  | succ N ih =>
      have hstep : Channel.iterate Φ (N + 1) x = Φ.toFun (Channel.iterate Φ N x) := rfl
      rw [hstep]
      exact le_trans (Φ.contract _) ih

/-- If `Φ = (1 - p) • Ψ + p • χ` and the stated pairwise bound holds on the unit ball, the
difference between the `N`-fold iterates of `Ψ` and `Φ` has norm at most `2 * p * N` for
nonnegative `p` [CotlerGongKannan2025]. -/
theorem channel_telescoping_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ Φ χ : Channel E) (p : ℝ) (hp : 0 ≤ p)
    (hΦ : ∀ x, Φ.toFun x = (1 - p) • Ψ.toFun x + p • χ.toFun x)
    (hpair : ∀ x, ‖x‖ ≤ 1 → ‖Ψ.toFun x - χ.toFun x‖ ≤ 2)
    (ρ : E) (hρ : ‖ρ‖ ≤ 1) (N : ℕ) :
    ‖Channel.iterate Ψ N ρ - Channel.iterate Φ N ρ‖ ≤ 2 * p * (N : ℝ) := by
  induction N with
  | zero => simp [Channel.iterate]
  | succ N ih =>
      have hΨ : Channel.iterate Ψ (N + 1) ρ = Ψ.toFun (Channel.iterate Ψ N ρ) := rfl
      have hΦ' : Channel.iterate Φ (N + 1) ρ = Φ.toFun (Channel.iterate Φ N ρ) := rfl
      rw [hΨ, hΦ']
      have hsplit :
          Ψ.toFun (Channel.iterate Ψ N ρ) - Φ.toFun (Channel.iterate Φ N ρ) =
            (Ψ.toFun (Channel.iterate Ψ N ρ) - Ψ.toFun (Channel.iterate Φ N ρ)) +
            (Ψ.toFun (Channel.iterate Φ N ρ) - Φ.toFun (Channel.iterate Φ N ρ)) := by
        abel
      rw [hsplit]
      have hcontr : ‖Ψ.toFun (Channel.iterate Ψ N ρ) - Ψ.toFun (Channel.iterate Φ N ρ)‖ ≤
          ‖Channel.iterate Ψ N ρ - Channel.iterate Φ N ρ‖ := by
        rw [← Channel.map_sub]
        exact Ψ.contract _
      have hnormΦ : ‖Channel.iterate Φ N ρ‖ ≤ 1 := norm_iterate_le_one Φ hρ N
      have hstep : ‖Ψ.toFun (Channel.iterate Φ N ρ) - Φ.toFun (Channel.iterate Φ N ρ)‖ ≤
          2 * p := by
        have heq : Ψ.toFun (Channel.iterate Φ N ρ) - Φ.toFun (Channel.iterate Φ N ρ) =
            p • (Ψ.toFun (Channel.iterate Φ N ρ) - χ.toFun (Channel.iterate Φ N ρ)) := by
          rw [hΦ, smul_sub, sub_smul, one_smul]
          abel
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
        nlinarith [hpair _ hnormΦ]
      calc ‖(Ψ.toFun (Channel.iterate Ψ N ρ) - Ψ.toFun (Channel.iterate Φ N ρ)) +
              (Ψ.toFun (Channel.iterate Φ N ρ) - Φ.toFun (Channel.iterate Φ N ρ))‖
          ≤ ‖Ψ.toFun (Channel.iterate Ψ N ρ) - Ψ.toFun (Channel.iterate Φ N ρ)‖ +
              ‖Ψ.toFun (Channel.iterate Φ N ρ) - Φ.toFun (Channel.iterate Φ N ρ)‖ :=
            norm_add_le _ _
        _ ≤ ‖Channel.iterate Ψ N ρ - Channel.iterate Φ N ρ‖ + 2 * p := by linarith
        _ ≤ 2 * p * (N : ℝ) + 2 * p := by linarith
        _ = 2 * p * ((N : ℝ) + 1) := by ring
        _ = 2 * p * ((N + 1 : ℕ) : ℝ) := by push_cast; ring

/-- For positive `η` and `τ`, the stated small-noise hypotheses give decoherence time at most `1
/ (4 * η * n)` and precision expression at most `8 * η * n` for `n ≥ 1`
[CotlerGongKannan2025]. -/
theorem heisenberg_threshold_noise {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    (∀ n : ℕ, 1 ≤ n → 4 * η * τ * n ≤ 1 →
        sensingDecoherenceTime η τ n ≤ 1 / (4 * η * n)) ∧
    (∀ n : ℕ, 1 ≤ n → 0 ≤ 4 * η * τ * n → 4 * η * τ * n ≤ 1 →
        sensingPrecision η τ n ≤ 8 * η * n) := by
  constructor
  · intro n hn1 hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h0 : 0 ≤ 4 * η * τ * n := by positivity
    have hlow : 2 * η * τ * n ≤ noiseJumpProb (interstitialLam η τ) n := by
      have := one_sub_exp_neg_ge h0 hn
      rw [noiseJumpProb_interstitial]
      linarith
    have hpos2 : (0 : ℝ) < 2 * η * τ * n := by positivity
    have hp2 : (0 : ℝ) < 2 * noiseJumpProb (interstitialLam η τ) n := by linarith
    unfold sensingDecoherenceTime
    rw [div_le_iff₀ hp2]
    have h4 : (0 : ℝ) < 4 * η * n := by positivity
    rw [one_div, inv_mul_eq_div, le_div_iff₀ h4]
    nlinarith
  · intro n hn1 h0 hn
    have hup : noiseJumpProb (interstitialLam η τ) n ≤ 4 * η * τ * n := by
      rw [noiseJumpProb_interstitial]
      exact one_sub_exp_neg_le h0
    have hp : (0 : ℝ) ≤ noiseJumpProb (interstitialLam η τ) n := by
      rw [noiseJumpProb_interstitial]
      have hle : Real.exp (-(4 * η * τ * n)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      linarith
    unfold sensingPrecision
    rw [div_le_iff₀ hτ]
    nlinarith

end Qatlib.Papers.NoisyLearn26.MainResults.Sensing
