/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Theorem3
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quantum walk reflection cost parameters

`mnrsPhaseGap`, `mnrsQpeCopies`, and `mnrsReflectionCopies` define the angular gap and rounded
repetition parameters used in `mnrsReflectionLedger`. The module derives explicit reflection
cost bounds and verifies the positivity and logarithmic estimates for the scheduled errors
`betaAt (1 / 72) i`. For background on search via quantum walks, see
[MagniezNayakRolandSantha2011].

## Main statements

* `mnrsPhaseGap`: The angular phase gap `2 * Real.arccos r` used in the MNRS cost ledger.
* `mnrs_schedule_reflection_cost_le`: At a positive level, the reflection ledger for the
  scheduled error has the stated `80 * π * U / sqrt δ` logarithmic bound; see [Magniez et al.,
  Theorem 6][MagniezNayakRolandSantha2011].

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Real BigOperators

namespace Qatlib.Concepts.WalkSearch.MainResults.SearchCost

/-- The angular phase gap `2 * Real.arccos r` used in the MNRS cost ledger. -/
noncomputable def mnrsPhaseGap (r : ℝ) : ℝ := 2 * Real.arccos r

/-- The ceiling of `log (2 * π / Δ) / log 2`, specifying the phase estimation precision
exponent. -/
noncomputable def mnrsQpeCopies (Δ : ℝ) : ℕ :=
  Nat.ceil (Real.log (2 * Real.pi / Δ) / Real.log 2)

/-- The ceiling of `log (1 / β) / log 2` plus one, specifying the reflection repetition count. -/
noncomputable def mnrsReflectionCopies (β : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / β) / Real.log 2) + 1

/-- The reflection cost ledger `4 * U * (2 * mnrsReflectionCopies β * 2^(mnrsQpeCopies Δ))`. -/
noncomputable def mnrsReflectionLedger (U Δ β : ℝ) : ℝ :=
  4 * U * (2 * (mnrsReflectionCopies β : ℝ) * 2 ^ mnrsQpeCopies Δ)

/-- For positive `y`, raising two to `Real.log y / Real.log 2` gives `y`. -/
private theorem two_rpow_log_div_log {y : ℝ} (hy : 0 < y) :
    (2 : ℝ) ^ (Real.log y / Real.log 2) = y := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hmul : Real.log 2 * (Real.log y / Real.log 2) = Real.log y := by
    field_simp
  rw [hmul, Real.exp_log hy]

/-- If `0 ≤ r ≤ 1` and `r = 1 - δ`, then `mnrsPhaseGap r ≥ 2 * Real.sqrt δ`. -/
theorem mnrs_phaseGap_ge_two_sqrt_gap {r δ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hrδ : r = 1 - δ) :
    2 * Real.sqrt δ ≤ mnrsPhaseGap r := by
  have hδ0 : 0 ≤ δ := by linarith
  have hsin : Real.sin (Real.arccos r) = Real.sqrt (1 - r ^ 2) := Real.sin_arccos r
  have hle : Real.sin (Real.arccos r) ≤ Real.arccos r := by
    rcases eq_or_lt_of_le (Real.arccos_nonneg r) with h | h
    · rw [← h, Real.sin_zero]
    · exact (Real.sin_lt h).le
  have hsq : δ ≤ 1 - r ^ 2 := by nlinarith
  have hsqrt : Real.sqrt δ ≤ Real.sqrt (1 - r ^ 2) := Real.sqrt_le_sqrt hsq
  have hstep : Real.sqrt δ ≤ Real.arccos r := by
    rw [hsin] at hle
    linarith
  rw [mnrsPhaseGap]
  linarith

/-- For `0 < Δ ≤ π`, the rounded phase estimation size satisfies `2^(mnrsQpeCopies Δ) ≤ 4 * π /
Δ`; see [Magniez et al., Theorem 6][MagniezNayakRolandSantha2011]. -/
theorem mnrs_two_pow_qpeCopies_le {Δ : ℝ} (hΔ : 0 < Δ) (hΔπ : Δ ≤ Real.pi) :
    2 ^ mnrsQpeCopies Δ ≤ 4 * Real.pi / Δ := by
  have hpos : 0 < 2 * Real.pi / Δ := div_pos (by positivity) hΔ
  have hge : 1 ≤ 2 * Real.pi / Δ := by
    rw [le_div_iff₀ hΔ]
    nlinarith [Real.pi_pos]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ Real.log (2 * Real.pi / Δ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hge) hlog2pos.le
  have hceil : ((mnrsQpeCopies Δ : ℕ) : ℝ) < Real.log (2 * Real.pi / Δ) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one hx0
  have hmono : (2 : ℝ) ^ ((mnrsQpeCopies Δ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (Real.log (2 * Real.pi / Δ) / Real.log 2 + 1) := by
    rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    linarith
  have hadd : (2 : ℝ) ^ (Real.log (2 * Real.pi / Δ) / Real.log 2 + 1) =
      2 * (2 * Real.pi / Δ) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), two_rpow_log_div_log hpos]
    ring
  have hnat : (2 : ℝ) ^ ((mnrsQpeCopies Δ : ℕ) : ℝ) = 2 ^ mnrsQpeCopies Δ :=
    Real.rpow_natCast 2 (mnrsQpeCopies Δ)
  rw [hnat, hadd] at hmono
  calc
    2 ^ mnrsQpeCopies Δ ≤ 2 * (2 * Real.pi / Δ) := hmono
    _ = 4 * Real.pi / Δ := by ring

/-- The natural logarithm of two is at least `1 / 2`. -/
private theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- Under the phase gap and error logarithm hypotheses, the reflection ledger is at most `80 * π
* U / sqrt δ * log (1 / β)`; see [Magniez et al., Theorem 7][MagniezNayakRolandSantha2011]. -/
theorem mnrs_reflectionLedger_le {U δ Δ β : ℝ} (hU : 0 ≤ U) (hδ : 0 < δ)
    (hΔ : 0 < Δ) (hΔπ : Δ ≤ Real.pi) (hgap : 2 * Real.sqrt δ ≤ Δ)
    (hL1 : 1 ≤ Real.log (1 / β)) :
    mnrsReflectionLedger U Δ β ≤ 80 * Real.pi * U / Real.sqrt δ * Real.log (1 / β) := by
  have hδs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.log (1 / β) := by linarith
  have hratio : Real.log (1 / β) / Real.log 2 ≤ 2 * Real.log (1 / β) := by
    have h2 : 1 ≤ 2 * Real.log 2 := by linarith [half_le_log_two]
    have hm := mul_le_mul_of_nonneg_left h2 hL0
    rw [div_le_iff₀ hlog2]
    linarith
  have hk : ((mnrsReflectionCopies β : ℕ) : ℝ) ≤ 5 * Real.log (1 / β) := by
    have hceil : ((mnrsReflectionCopies β : ℕ) : ℝ) <
        Real.log (1 / β) / Real.log 2 + 1 + 1 := by
      have hx0 : 0 ≤ Real.log (1 / β) / Real.log 2 := div_nonneg hL0 hlog2.le
      have h := Nat.ceil_lt_add_one hx0
      have hdef : mnrsReflectionCopies β = Nat.ceil (Real.log (1 / β) / Real.log 2) + 1 := rfl
      rw [hdef, Nat.cast_add, Nat.cast_one]
      linarith
    nlinarith
  have hreg : (2 : ℝ) ^ mnrsQpeCopies Δ ≤ 4 * Real.pi / Δ := mnrs_two_pow_qpeCopies_le hΔ hΔπ
  have hpinv : 4 * Real.pi / Δ ≤ 2 * Real.pi / Real.sqrt δ := by
    rw [div_le_div_iff₀ hΔ hδs]
    nlinarith [Real.pi_pos]
  have hreg' : (2 : ℝ) ^ mnrsQpeCopies Δ ≤ 2 * Real.pi / Real.sqrt δ := hreg.trans hpinv
  have hstep1 : mnrsReflectionLedger U Δ β ≤
      4 * U * (2 * (mnrsReflectionCopies β : ℝ)) * (2 * Real.pi / Real.sqrt δ) := by
    have hm := mul_le_mul_of_nonneg_left hreg'
      (by positivity : (0 : ℝ) ≤ 4 * U * (2 * (mnrsReflectionCopies β : ℝ)))
    calc
      mnrsReflectionLedger U Δ β =
          4 * U * (2 * (mnrsReflectionCopies β : ℝ)) * 2 ^ mnrsQpeCopies Δ := by
            rw [mnrsReflectionLedger]; ring
      _ ≤ 4 * U * (2 * (mnrsReflectionCopies β : ℝ)) * (2 * Real.pi / Real.sqrt δ) := hm
  have hstep2 : 4 * U * (2 * (mnrsReflectionCopies β : ℝ)) * (2 * Real.pi / Real.sqrt δ) ≤
      80 * Real.pi * U / Real.sqrt δ * Real.log (1 / β) := by
    have hc : (0 : ℝ) ≤ 16 * Real.pi * U / Real.sqrt δ := by positivity
    have hm := mul_le_mul_of_nonneg_left hk hc
    calc
      4 * U * (2 * (mnrsReflectionCopies β : ℝ)) * (2 * Real.pi / Real.sqrt δ) =
          16 * Real.pi * U / Real.sqrt δ * ((mnrsReflectionCopies β : ℝ)) := by
            field_simp; ring
      _ ≤ 16 * Real.pi * U / Real.sqrt δ * (5 * Real.log (1 / β)) := hm
      _ = 80 * Real.pi * U / Real.sqrt δ * Real.log (1 / β) := by ring
  exact hstep1.trans hstep2

section Schedule

open Qatlib.Concepts.WalkSearch.MnrsAmplify

/-- The scheduled error `betaAt (1 / 72) i` is positive at every positive level. -/
theorem mnrs_betaAt_pos {i : ℕ} (hi : 1 ≤ i) : 0 < betaAt (1 / 72) i := by
  rw [betaAt]
  have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  positivity

/-- The scheduled error `betaAt (1 / 72) i` is at most `1 / 4` at every positive level. -/
theorem mnrs_betaAt_le_quarter {i : ℕ} (hi : 1 ≤ i) : betaAt (1 / 72) i ≤ 1 / 4 := by
  rw [betaAt]
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hi2 : (1 : ℝ) ≤ (i : ℝ) ^ 2 := by nlinarith
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpi3 : (1 : ℝ) ≤ Real.pi ^ 3 := one_le_pow₀ hpi1
  have hden : (0 : ℝ) < 4 * Real.pi ^ 3 := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) ^ 2)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have hprod : (1 : ℝ) ≤ (i : ℝ) ^ 2 * Real.pi ^ 3 := by
    nlinarith [mul_le_mul hi2 hpi3 (by norm_num) (by positivity)]
  nlinarith

/-- At every positive level, `Real.log (1 / betaAt (1 / 72) i)` is at least one. -/
theorem mnrs_betaAt_log_ge_one {i : ℕ} (hi : 1 ≤ i) :
    1 ≤ Real.log (1 / betaAt (1 / 72) i) := by
  have hpos := mnrs_betaAt_pos hi
  have hle := mnrs_betaAt_le_quarter hi
  have hlog4 : 1 ≤ Real.log 4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have := half_le_log_two
    linarith
  have hmono : Real.log 4 ≤ Real.log (1 / betaAt (1 / 72) i) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hpos]
    linarith
  linarith

/-- At a positive level, the reflection ledger for the scheduled error has the stated `80 * π *
U / sqrt δ` logarithmic bound; see [Magniez et al., Theorem
6][MagniezNayakRolandSantha2011]. -/
theorem mnrs_schedule_reflection_cost_le {U δ Δ : ℝ} (hU : 0 ≤ U) (hδ : 0 < δ)
    (hΔ : 0 < Δ) (hΔπ : Δ ≤ Real.pi) (hgap : 2 * Real.sqrt δ ≤ Δ) {i : ℕ} (hi : 1 ≤ i) :
    mnrsReflectionLedger U Δ (betaAt (1 / 72) i) ≤
      80 * Real.pi * U / Real.sqrt δ * Real.log (1 / betaAt (1 / 72) i) :=
  mnrs_reflectionLedger_le hU hδ hΔ hΔπ hgap (mnrs_betaAt_log_ge_one hi)

end Schedule

end Qatlib.Concepts.WalkSearch.MainResults.SearchCost
