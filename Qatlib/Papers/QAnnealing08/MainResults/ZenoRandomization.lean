/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Qatlib.Papers.QAnnealing08.MainResults.SzegedyPhaseGap

/-!
# Randomized phases and annealing error budgets

The finite exponential average `randomExpAvg` models suppression of an off-phase component under
randomized evolution. Geometric-sum and sine estimates bound its norm and repeated powers in
terms of phase separation, as used in [SommaEtAl2008].

The remaining scalar lemmas combine the off-phase and Gibbs error budgets and compare
logarithmic final-temperature expressions.

## Main statements

* `norm_randomExpAvg_le`: the inverse-sine suppression bound.
* `decoherenceFactor_le_sqrt_delta`: a bound from a positive gap.
* `qsa_final_error_bound`: the combined final error estimate.

## References

* [Somma et al., 2008][SommaEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QAnnealing08.MainResults.ZenoRandomization

/-- The average of the phases `exp (irθ)` for integers `r` from zero to `N - 1`. -/
def randomExpAvg (N : ℕ) (θ : ℝ) : ℂ :=
  (1 / (N : ℂ)) * ∑ r ∈ Finset.range N, Complex.exp (Complex.I * ((r : ℂ) * (θ : ℂ)))

/-- For positive `N` and nonzero `sin (θ / 2)`, the exponential average has norm at most `1 / (N
* |sin (θ / 2)|)` [SommaEtAl2008]. -/
theorem norm_randomExpAvg_le (N : ℕ) (hN : 0 < N) (θ : ℝ)
    (hsin : Real.sin (θ / 2) ≠ 0) :
    ‖randomExpAvg N θ‖ ≤ 1 / ((N : ℝ) * |Real.sin (θ / 2)|) := by
  set z : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with hz
  have hz1 : z ≠ 1 := by
    intro h
    have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one θ
    rw [hz] at h
    rw [h] at hnorm
    simp only [sub_self, norm_zero] at hnorm
    have h2 : ‖2 * Real.sin (θ / 2)‖ = 0 := hnorm.symm
    rw [Real.norm_eq_abs, abs_eq_zero] at h2
    exact hsin ((mul_eq_zero.mp h2).resolve_left (by norm_num))
  have hzpow : ∀ r : ℕ, Complex.exp (Complex.I * ((r : ℂ) * (θ : ℂ))) = z ^ r := by
    intro r
    rw [hz]
    rw [show Complex.I * ((r : ℂ) * (θ : ℂ))
        = (r : ℂ) * (Complex.I * (θ : ℂ)) by ring, Complex.exp_nat_mul]
  have hsumrew : (∑ r ∈ Finset.range N, Complex.exp (Complex.I * ((r : ℂ) * (θ : ℂ))))
      = ∑ r ∈ Finset.range N, z ^ r :=
    Finset.sum_congr rfl (fun r _ => hzpow r)
  have hznorm : ‖z‖ = 1 := by
    rw [hz]; exact Complex.norm_exp_I_mul_ofReal θ
  have hzN : ‖z ^ N‖ = 1 := by rw [Complex.norm_pow, hznorm, one_pow]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    have h := norm_sub_le (z ^ N) (1 : ℂ)
    rw [hzN, norm_one] at h
    linarith
  have hden : ‖z - 1‖ = 2 * |Real.sin (θ / 2)| := by
    rw [hz, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
    norm_num
  have hdenpos : 0 < ‖z - 1‖ := by
    rw [hden]
    exact mul_pos (by norm_num) (abs_pos.mpr hsin)
  have hsum_bound : ‖∑ r ∈ Finset.range N, z ^ r‖ ≤ 2 / ‖z - 1‖ := by
    rw [geom_sum_eq hz1 N, Complex.norm_div]
    exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
  have hcoef : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by
    rw [Complex.norm_div, norm_one, Complex.norm_natCast]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold randomExpAvg
  rw [hsumrew, Complex.norm_mul, hcoef]
  calc (1 / (N : ℝ)) * ‖∑ r ∈ Finset.range N, z ^ r‖
      ≤ (1 / (N : ℝ)) * (2 / ‖z - 1‖) := by
        exact mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    _ = 1 / ((N : ℝ) * |Real.sin (θ / 2)|) := by
        rw [hden]
        have hsinpos : (0 : ℝ) < |Real.sin (θ / 2)| := abs_pos.mpr hsin
        have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
        have hsne : |Real.sin (θ / 2)| ≠ 0 := ne_of_gt hsinpos
        field_simp

/-- The norm of the `s`th power of the exponential average is bounded by the `s`th power of the
inverse-sine bound [SommaEtAl2008]. -/
theorem norm_randomExpAvg_pow_le (N : ℕ) (hN : 0 < N) (θ : ℝ) (s : ℕ)
    (hsin : Real.sin (θ / 2) ≠ 0) :
    ‖(randomExpAvg N θ) ^ s‖ ≤ (1 / ((N : ℝ) * |Real.sin (θ / 2)|)) ^ s := by
  rw [Complex.norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_randomExpAvg_le N hN θ hsin) s

/-- For `0 < φ ≤ π / 2` and positive `N`, the inverse-sine factor is at most `π / (2Nφ)`. -/
theorem decoherenceFactor_le_pi (N : ℕ) (hN : 0 < N) (φ : ℝ)
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi / 2) :
    1 / ((N : ℝ) * |Real.sin φ|) ≤ Real.pi / (2 * (N : ℝ) * φ) := by
  have hsin : 2 / Real.pi * φ ≤ Real.sin φ := Real.mul_le_sin (le_of_lt hφ0) hφπ
  have hsinpos : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  have habs : |Real.sin φ| = Real.sin φ := abs_of_pos hsinpos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [habs]
  have hden : 2 * (N : ℝ) * φ / Real.pi ≤ (N : ℝ) * Real.sin φ := by
    have h := mul_le_mul_of_nonneg_left hsin (le_of_lt hNpos)
    calc 2 * (N : ℝ) * φ / Real.pi = (N : ℝ) * (2 / Real.pi * φ) := by ring
      _ ≤ (N : ℝ) * Real.sin φ := h
  have h1 : 1 / ((N : ℝ) * Real.sin φ) ≤ 1 / (2 * (N : ℝ) * φ / Real.pi) :=
    one_div_le_one_div_of_le (by positivity) hden
  have h2 : 1 / (2 * (N : ℝ) * φ / Real.pi) = Real.pi / (2 * (N : ℝ) * φ) := by
    field_simp
  exact h1.trans_eq h2

/-- If `0 < φ ≤ π / 2` and `φ ≥ sqrt (2δ)` for positive `δ`, the inverse-sine factor is at most
`π / (2N * sqrt (2δ))` [SommaEtAl2008]. -/
theorem decoherenceFactor_le_sqrt_delta (N : ℕ) (hN : 0 < N) (φ δ : ℝ)
    (hφ0 : 0 < φ) (hφπ : φ ≤ Real.pi / 2)
    (hδ0 : 0 < δ) (hδ : Real.sqrt (2 * δ) ≤ φ) :
    1 / ((N : ℝ) * |Real.sin φ|) ≤ Real.pi / (2 * (N : ℝ) * Real.sqrt (2 * δ)) := by
  have h1 := decoherenceFactor_le_pi N hN φ hφ0 hφπ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (2 * δ) := Real.sqrt_pos.mpr (by linarith)
  have hle : 2 * (N : ℝ) * Real.sqrt (2 * δ) ≤ 2 * (N : ℝ) * φ := by
    have h := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
    linarith
  calc 1 / ((N : ℝ) * |Real.sin φ|) ≤ Real.pi / (2 * (N : ℝ) * φ) := h1
    _ ≤ Real.pi / (2 * (N : ℝ) * Real.sqrt (2 * δ)) :=
        div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity) hle

/-- The condition `8 * (k + 1) ≤ 4 ^ s` implies `(1 / 2) ^ s ≤ 1 / (2 * sqrt (2 * (k + 1)))`
[SommaEtAl2008]. -/
theorem pow_half_le_sqrt_inv {s k : ℕ} (h : 8 * (k + 1) ≤ 4 ^ s) :
    (1 / 2 : ℝ) ^ s ≤ 1 / (2 * Real.sqrt (2 * (k + 1))) := by
  have hT2 : (4 : ℝ) ^ s = ((2 : ℝ) ^ s) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 2 s]
  have hT : (8 : ℝ) * (k + 1) ≤ ((2 : ℝ) ^ s) ^ 2 := by
    rw [← hT2]; exact_mod_cast h
  have hspos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hs8 : Real.sqrt (8 * (k + 1)) ≤ (2 : ℝ) ^ s := by
    rw [← Real.sqrt_sq (le_of_lt hspos)]
    exact Real.sqrt_le_sqrt hT
  have hs8' : 2 * Real.sqrt (2 * (k + 1)) ≤ (2 : ℝ) ^ s := by
    have heq : 2 * Real.sqrt (2 * (k + 1)) = Real.sqrt (8 * (k + 1)) := by
      rw [show (8 : ℝ) * (k + 1) = 4 * (2 * (k + 1)) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [heq]
    exact hs8
  have hgoal : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by
    rw [div_pow, one_pow]
  rw [hgoal]
  exact one_div_le_one_div_of_le (by positivity) hs8'

/-- The stated nonnegative decay factor and bounds on `ν'` and `β ^ s` imply `ν' * β ^ s ≤ μ /
2` [SommaEtAl2008]. -/
theorem zeno_offphase_step (μ ν' β : ℝ) (k s : ℕ)
    (hμ : 0 ≤ μ) (hβ0 : 0 ≤ β)
    (hν : ν' ≤ Real.sqrt (2 * (k + 1)) * μ)
    (hβs : β ^ s ≤ 1 / (2 * Real.sqrt (2 * (k + 1)))) :
    ν' * β ^ s ≤ μ / 2 := by
  have hspos : 0 < Real.sqrt (2 * (k + 1)) := by
    apply Real.sqrt_pos.mpr; positivity
  have hβs0 : 0 ≤ β ^ s := pow_nonneg hβ0 s
  have hν0 : 0 ≤ Real.sqrt (2 * (k + 1)) * μ := mul_nonneg (le_of_lt hspos) hμ
  have hne : Real.sqrt (2 * (k + 1)) ≠ 0 := ne_of_gt hspos
  calc ν' * β ^ s
      ≤ (Real.sqrt (2 * (k + 1)) * μ) * (1 / (2 * Real.sqrt (2 * (k + 1)))) :=
        mul_le_mul hν hβs hβs0 hν0
    _ = μ / 2 := by
        field_simp

/-- For positive `Q` and `ε`, the per-step bound `μ2 ≤ ε / (4Q)` implies `2Q * μ2 ≤ ε / 2`
[SommaEtAl2008]. -/
theorem zeno_success_accumulation (Q : ℕ) (hQ : 0 < Q) (μ2 ε : ℝ)
    (hε : 0 < ε) (hμ : μ2 ≤ ε / (4 * Q)) :
    2 * (Q : ℝ) * μ2 ≤ ε / 2 := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hstep : 2 * (Q : ℝ) * μ2 ≤ 2 * (Q : ℝ) * (ε / (4 * Q)) := by
    exact mul_le_mul_of_nonneg_left hμ (by positivity)
  have heq : 2 * (Q : ℝ) * (ε / (4 * (Q : ℝ))) = ε / 2 := by
    have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
    field_simp
    ring
  rw [show (4 * Q : ℝ) = 4 * (Q : ℝ) by ring] at hstep
  rw [heq] at hstep
  exact hstep

/-- Two real error terms each bounded by `ε / 2` have sum at most `ε`. -/
theorem total_error_le (orth gibbs ε : ℝ) (h1 : orth ≤ ε / 2) (h2 : gibbs ≤ ε / 2) :
    orth + gibbs ≤ ε := by
  linarith

/-- For positive `Q` and `ε`, a per-step bound `μ2 ≤ ε / (4Q)` and Gibbs error at most `ε / 2`
make the combined expression at most `ε` [SommaEtAl2008]. -/
theorem qsa_final_error_bound (Q : ℕ) (μ2 gibbs ε : ℝ)
    (hQ : 0 < Q) (hε : 0 < ε)
    (hμ : μ2 ≤ ε / (4 * Q)) (hg : gibbs ≤ ε / 2) :
    2 * (Q : ℝ) * μ2 + gibbs ≤ ε :=
  total_error_le _ _ _ (zeno_success_accumulation Q hQ μ2 ε hε hμ) hg

/-- For positive `d`, `ε`, and `γ`, replacing `d / (2ε)` by `d / ε` increases the logarithmic
inverse-temperature expression [SommaEtAl2008]. -/
theorem beta_f_le_log (d ε γ : ℝ) (hd : 0 < d) (hε : 0 < ε) (hγ : 0 < γ) :
    Real.log (d / (2 * ε)) / γ ≤ Real.log (d / ε) / γ := by
  have hle : d / (2 * ε) ≤ d / ε := by
    rw [div_le_div_iff₀ (by positivity) hε]
    nlinarith [hd, hε]
  have hpos : 0 < d / (2 * ε) := by positivity
  exact div_le_div_of_nonneg_right (Real.log_le_log hpos hle) (le_of_lt hγ)

end Qatlib.Papers.QAnnealing08.MainResults.ZenoRandomization
