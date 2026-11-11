/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Optimality of the unit phase-measurement kernel

The finite functional `sourceHolevoCost` expresses the cost using spectral-index distances, real
amplitudes, and a real measurement kernel. For nonnegative cost coefficients and positive
amplitudes, `source_holevo_cost_optimal` proves that the constant-one kernel minimizes this
functional among kernels with entries of absolute value at most one. The phase-estimation
setting is described in [VanDamEtAl2007].

## Main statements

* `source_holevo_cost_optimal`: For nonempty index size, nonnegative cost coefficients, positive
  amplitudes, and kernel entries bounded in absolute value by one, the constant-one kernel
  minimizes `sourceHolevoCost` and has the stated coefficient-sum value.
* `source_holevo_term_equality`: For positive `ψ`, nonzero `c`, and `|χ| ≤ 1`, the term `c * ψ *
  χ * ψ` is at most `|c| * ψ ^ 2`, with equality exactly when `χ` has the sign of `c`.

## References

* [van Dam et al., 2007][VanDamEtAl2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.OptimalPOVM

open scoped BigOperators

/-- The absolute difference of two spectral indices, regarded as a natural number. -/
def sourceDist {q : ℕ} (h k : Fin q) : ℕ := Int.natAbs ((h : ℤ) - (k : ℤ))

/-- The finite Holevo cost functional formed from coefficients `c`, amplitudes `ψ`, and kernel
entries `χ` grouped by spectral-index distance. -/
noncomputable def sourceHolevoCost {q : ℕ} (c : ℕ → ℝ) (ψ : Fin q → ℝ)
    (χ : Fin q → Fin q → ℝ) : ℝ :=
  - c 0 - (1 / 2) * ∑ l ∈ Finset.Icc 1 (q - 1), c l *
    ∑ h : Fin q, ∑ k : Fin q,
      (if sourceDist h k = l then ψ h * χ h k * ψ k else 0)

/-- The real kernel whose entries are all one. -/
def sourceUnitChi {q : ℕ} : Fin q → Fin q → ℝ := fun _ _ => 1

/-- For nonempty index size, nonnegative cost coefficients, positive amplitudes, and kernel
entries bounded in absolute value by one, the constant-one kernel minimizes
`sourceHolevoCost` and has the stated coefficient-sum value. See [van Dam et al.,
2007][VanDamEtAl2007]. -/
theorem source_holevo_cost_optimal {q : ℕ} (hq : 1 ≤ q) (c : ℕ → ℝ)
    (hc : ∀ l, 0 ≤ c l) (ψ : Fin q → ℝ) (hψ : ∀ k, 0 < ψ k)
    (χ : Fin q → Fin q → ℝ) (hχ : ∀ h k, |χ h k| ≤ 1) :
    sourceHolevoCost c ψ χ ≥ sourceHolevoCost c ψ sourceUnitChi ∧
    sourceHolevoCost c ψ sourceUnitChi
      = - c 0 - (1 / 2) * ∑ l ∈ Finset.Icc 1 (q - 1), |c l| *
          ∑ h : Fin q, ∑ k : Fin q,
            (if sourceDist h k = l then ψ h * ψ k else 0) := by
  have hS : ∀ l ∈ Finset.Icc 1 (q - 1),
      c l * (∑ h : Fin q, ∑ k : Fin q,
        (if sourceDist h k = l then ψ h * χ h k * ψ k else 0))
      ≤ c l * (∑ h : Fin q, ∑ k : Fin q,
        (if sourceDist h k = l then ψ h * ψ k else 0)) := by
    intro l _
    apply mul_le_mul_of_nonneg_left _ (hc l)
    apply Finset.sum_le_sum
    intro h _
    apply Finset.sum_le_sum
    intro k _
    split_ifs with hd
    · have hχ1 : χ h k ≤ 1 := (abs_le.mp (hχ h k)).2
      have hp : 0 ≤ ψ h * ψ k := (mul_pos (hψ h) (hψ k)).le
      have hchain : ψ h * ψ k * χ h k ≤ ψ h * ψ k * 1 :=
        mul_le_mul_of_nonneg_left hχ1 hp
      nlinarith [hchain]
    · exact le_refl 0
  have hsum : (∑ l ∈ Finset.Icc 1 (q - 1), c l * (∑ h : Fin q, ∑ k : Fin q,
        (if sourceDist h k = l then ψ h * χ h k * ψ k else 0)))
      ≤ ∑ l ∈ Finset.Icc 1 (q - 1), c l * (∑ h : Fin q, ∑ k : Fin q,
        (if sourceDist h k = l then ψ h * ψ k else 0)) :=
    Finset.sum_le_sum hS
  constructor
  · unfold sourceHolevoCost sourceUnitChi
    simp only [mul_one]
    nlinarith [hsum]
  · unfold sourceHolevoCost sourceUnitChi
    simp only [mul_one]
    rw [show (∑ l ∈ Finset.Icc 1 (q - 1), c l *
          ∑ h : Fin q, ∑ k : Fin q, (if sourceDist h k = l then ψ h * ψ k else 0))
        = (∑ l ∈ Finset.Icc 1 (q - 1), |c l| *
          ∑ h : Fin q, ∑ k : Fin q, (if sourceDist h k = l then ψ h * ψ k else 0)) by
      apply Finset.sum_congr rfl
      intro l _
      rw [abs_of_nonneg (hc l)]]

/-- For positive `ψ`, nonzero `c`, and `|χ| ≤ 1`, the term `c * ψ * χ * ψ` is at most `|c| * ψ ^
2`, with equality exactly when `χ` has the sign of `c`. See [van Dam et al.,
2007][VanDamEtAl2007]. -/
theorem source_holevo_term_equality (c ψ χ : ℝ) (hψ : 0 < ψ) (hc : c ≠ 0)
    (hχ : |χ| ≤ 1) :
    c * ψ * χ * ψ ≤ |c| * (ψ * ψ) ∧
    (c * ψ * χ * ψ = |c| * (ψ * ψ) ↔ χ = (if 0 < c then 1 else -1)) := by
  have hψ2 : 0 < ψ * ψ := mul_pos hψ hψ
  by_cases hcpos : 0 < c
  · have habs : |c| = c := abs_of_pos hcpos
    have hψχ : ψ * ψ * χ ≤ ψ * ψ * 1 := mul_le_mul_of_nonneg_left (abs_le.mp hχ).2 hψ2.le
    constructor
    · rw [habs]; nlinarith [hψχ]
    · rw [if_pos hcpos, habs]
      constructor
      · intro he
        have hzero : c * ψ * ψ ≠ 0 := by positivity
        have hχ1 : χ = 1 := by
          have : c * ψ * ψ * χ = c * ψ * ψ * 1 := by nlinarith [he]
          exact mul_left_cancel₀ hzero this
        exact hχ1
      · intro he; rw [he]; ring
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    have habs : |c| = -c := abs_of_neg hcneg
    have hψχ : ψ * ψ * (-1) ≤ ψ * ψ * χ :=
      mul_le_mul_of_nonneg_left (abs_le.mp hχ).1 hψ2.le
    constructor
    · rw [habs]; nlinarith [hψχ]
    · rw [if_neg hcpos, habs]
      constructor
      · intro he
        have hzero : c * ψ * ψ ≠ 0 := by
          have : c * ψ * ψ < 0 := by nlinarith [hψ2]
          exact ne_of_lt this
        have hχ1 : χ = -1 := by
          have : c * ψ * ψ * χ = c * ψ * ψ * (-1) := by nlinarith [he]
          exact mul_left_cancel₀ hzero this
        exact hχ1
      · intro he; rw [he]; ring

end Qatlib.Papers.PhaseEst07.MainResults.OptimalPOVM
