/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountQuan

/-!
# Expected cost bounds for adaptive approximate counting

This module bounds the expectation of the total grid-size cost in the approximate counter of
[BrassardEtAl2002]. Estimates for `costPowerMean`, the mean of two raised to the stopping index,
yield separate bounds for empty and nonempty marked sets.

## Main statements

* `bhmt_basic_approx_count_zero_cost`: the exact expected cost for an empty marked set.
* `bhmt_basic_approx_count_expected_cost`: the expected-cost specification with explicit
  constants.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Classical BigOperators

/-- The finite type of complete preliminary readout records for adaptive approximate counting. -/
private abbrev CostRecords (N : ℕ) :=
  (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)

/-- The expectation of two raised to the preliminary stopping index under
`basicApproxCountPrefixWeight`. -/
private noncomputable def costPowerMean {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) : ℝ :=
  ∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω * (2 : ℝ) ^ basicApproxCountStop N ω

/-- Every complete preliminary readout record has nonnegative probability weight. -/
private theorem costWeight_nonneg {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (ω : CostRecords N) :
    0 ≤ basicApproxCountPrefixWeight hN S ω :=
  Finset.prod_nonneg (fun l _ => (basicApproxCountLoopLaw hN S l).nonneg (ω l))

/-- The stopping index is at most the preliminary loop cap. -/
private theorem costStop_le_cap (N : ℕ) (ω : CostRecords N) :
    basicApproxCountStop N ω ≤ basicApproxCountLoopCap N := by
  unfold basicApproxCountStop
  split <;> omega

/-- The expectation `costPowerMean` is nonnegative. -/
private theorem costMean_nonneg {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    0 ≤ costPowerMean hN S :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (costWeight_nonneg hN S ω) (by positivity))

/-- The expectation `costPowerMean` is at least one. -/
private theorem costMean_one {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    1 ≤ costPowerMean hN S := by
  rw [← basicApproxCountPrefixWeight_sum hN S]
  apply Finset.sum_le_sum
  intro ω _
  exact le_mul_of_one_le_right (costWeight_nonneg hN S ω)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- The expectation `costPowerMean` is bounded by two raised to the loop cap. -/
private theorem costMean_cap {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    costPowerMean hN S ≤ (2 : ℝ) ^ basicApproxCountLoopCap N := by
  calc
    _ ≤ ∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω * (2 : ℝ) ^ basicApproxCountLoopCap N := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (costStop_le_cap N ω)) (costWeight_nonneg hN S ω)
    _ = _ := by rw [← Finset.sum_mul, basicApproxCountPrefixWeight_sum, one_mul]

/-- For positive `N`, two raised to the loop cap is at most `4 * Real.sqrt N`. -/
private theorem costCap_upper (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ basicApproxCountLoopCap N ≤ 4 * Real.sqrt (N : ℝ) := by
  have hs : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
  have hlog : 0 ≤ Real.logb 2 (2 * Real.sqrt (N : ℝ)) := by
    apply Real.logb_nonneg (by norm_num)
    linarith
  have hc := Nat.ceil_lt_add_one hlog
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc.le
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (by positivity),
    Real.rpow_one, Real.rpow_natCast] at hp
  exact hp.trans_eq (by ring)

/-- If `2^n * θ ≤ 1/5` and round `n` lies before the cap, then `costPowerMean` is at least
`(7/8) * 2^n`. -/
private theorem costPrefix_power_lower {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : (S.card : ℝ) / N = Real.sin θ ^ 2) (n : ℕ)
    (hn : n + 1 ≤ basicApproxCountLoopCap N) (hsmall : (2 : ℝ) ^ n * θ ≤ 1 / 5) :
    (2 : ℝ) ^ n * (7 / 8) ≤ costPowerMean hN S := by
  classical
  have hp := basicApproxCount_prefix_zero_lower hN S θ hθ0 hθ1 ha n (by omega) hsmall
  change (7 / 8 : ℝ) ≤ ∑ ω : CostRecords N,
    @ite ℝ (∀ l, l.val < n → basicApproxCountObserved N ω l = 0)
      (Classical.propDecidable _) (basicApproxCountPrefixWeight hN S ω) 0 at hp
  have hscaled := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 ^ n)
  apply hscaled.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hz : ∀ l, l.val < n → basicApproxCountObserved N ω l = 0
  · rw [if_pos hz]
    have hstop := basicApproxCountStop_of_prefix hn ω hz
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ basicApproxCountStop N ω :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simpa only [mul_comm] using! mul_le_mul_of_nonneg_left hpow (costWeight_nonneg hN S ω)
  · rw [if_neg hz, mul_zero]
    exact mul_nonneg (costWeight_nonneg hN S ω) (by positivity)

/-- For a nonempty marked set, `costPowerMean` is at least `7 / (40 * π)` times the square root
of the inverse marked fraction. -/
private theorem costMean_lower {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card) :
    7 / (40 * Real.pi) * Real.sqrt ((N : ℝ) / S.card) ≤ costPowerMean hN S := by
  obtain ⟨θ, hθ0, hθ1, ha, hroot, hangle⟩ := basicApproxCount_angle hN S hS
  obtain ⟨n, hn, hcross, hsmall⟩ := basicApproxCount_threshold N hN θ hθ0 hroot
  have hscale : θ * Real.sqrt ((N : ℝ) / S.card) ≤ Real.pi / 2 := by
    rw [Real.sqrt_div (Nat.cast_nonneg N)]
    have ht : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS)
    rw [← mul_div_assoc, div_le_iff₀ ht]
    exact hangle
  have hlow : (7 / 80 : ℝ) ≤ costPowerMean hN S * θ := by
    rcases hsmall with hn0 | hsmall
    · rw [hn0] at hcross
      norm_num at hcross
      have hm := costMean_one hN S
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) hθ0.le]
    · have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      have hθstrict : θ < Real.pi / 2 := by
        have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        have hm := mul_le_mul_of_nonneg_right hone hθ0.le
        linarith [Real.pi_gt_three]
      have hm := costPrefix_power_lower hN S θ hθ0 hθstrict ha n hn hsmall
      have hmul := mul_le_mul_of_nonneg_right hm hθ0.le
      rw [pow_succ] at hcross
      nlinarith
  have hh := mul_le_mul_of_nonneg_right hlow (Real.sqrt_nonneg ((N : ℝ) / S.card))
  have ht := mul_le_mul_of_nonneg_left hscale (costMean_nonneg hN S)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 40 * Real.pi)]
  nlinarith

/-- A scaled amplitude-estimation readout vanishes exactly when its finite grid label is zero. -/
private theorem costObserved_zero_iff {N : ℕ} (hN : 0 < N) (M : ℕ) (hM : 0 < M) (z : Fin M) :
    (N : ℝ) * aeEstimate M z = 0 ↔ z = ⟨0, hM⟩ := by
  by_cases hz : z = ⟨0, hM⟩
  · simp [hz, aeEstimate]
  have hzpos : 0 < z.val := by
    by_contra h
    apply hz
    apply Fin.ext
    change z.val = 0
    omega
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hz0 : (0 : ℝ) < z.val := by exact_mod_cast hzpos
  have hz1 : (z.val : ℝ) < M := by exact_mod_cast z.isLt
  have hx0 : 0 < Real.pi * z.val / M := div_pos (mul_pos Real.pi_pos hz0) hm
  have hx1 : Real.pi * z.val / M < Real.pi := by
    rw [div_lt_iff₀ hm]
    nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi * z.val / M) := Real.sin_pos_of_pos_of_lt_pi hx0 hx1
  have hp : 0 < (N : ℝ) * aeEstimate M z := by
    unfold aeEstimate
    exact mul_pos (by exact_mod_cast hN) (sq_pos_of_pos hs)
  exact iff_of_false (ne_of_gt hp) hz

/-- The expectation of a function of one readout coordinate equals its expectation under that
coordinate's loop law. -/
private theorem costCoordinate_mean {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (k : Fin (basicApproxCountLoopCap N)) (f : Fin (2 * 2 ^ k.val) → ℝ) :
    (∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω * f (ω k)) =
      ∑ z, (basicApproxCountLoopLaw hN S k).prob z * f z := by
  let g := fun (l : Fin (basicApproxCountLoopCap N)) (z : Fin (2 * 2 ^ l.val)) =>
    if h : l = k then f (h ▸ z) else 1
  have he (ω : CostRecords N) : f (ω k) = ∏ l, g l (ω l) := by
    rw [Finset.prod_eq_single k]
    · simp [g]
    · intro l _ hl
      simp [g, hl]
    · simp
  simp_rw [he]
  unfold basicApproxCountPrefixWeight
  simp_rw [← Finset.prod_mul_distrib]
  have hswap : (∑ ω : CostRecords N, ∏ l,
      (basicApproxCountLoopLaw hN S l).prob (ω l) * g l (ω l)) =
      ∑ ω ∈ Fintype.piFinset (fun l : Fin (basicApproxCountLoopCap N) =>
        (Finset.univ : Finset (Fin (2 * 2 ^ l.val)))),
        ∏ l, (basicApproxCountLoopLaw hN S l).prob (ω l) * g l (ω l) :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [hswap]
  have hprod := (Finset.prod_univ_sum
    (t := fun l : Fin (basicApproxCountLoopCap N) => (Finset.univ : Finset (Fin (2 * 2 ^ l.val))))
    (f := fun l z => (basicApproxCountLoopLaw hN S l).prob z * g l z)).symm
  rw [hprod, Finset.prod_eq_single k]
  · simp [g]
  · intro l _ hl
    simpa [g, hl] using! (basicApproxCountLoopLaw hN S l).sum_one
  · simp

/-- The probability that a given observed count is zero equals the zero-label probability of its
loop law. -/
private theorem costCoordinate_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (k : Fin (basicApproxCountLoopCap N)) :
    (∑ ω : CostRecords N, if basicApproxCountObserved N ω k = 0
      then basicApproxCountPrefixWeight hN S ω else 0) =
      (basicApproxCountLoopLaw hN S k).prob ⟨0, by positivity⟩ := by
  have h := costCoordinate_mean hN S k
    (fun z => if (N : ℝ) * aeEstimate (2 * 2 ^ k.val) z = 0 then 1 else 0)
  simpa [basicApproxCountObserved, costObserved_zero_iff hN (2 * 2 ^ k.val) (by positivity)] using!
      h

/-- If the loop continues beyond a positive index `l`, the observation at index `l - 1` is zero. -/
private theorem costStop_previous_zero (N : ℕ) (ω : CostRecords N)
    (l : Fin (basicApproxCountLoopCap N)) (hl : 0 < l.val)
    (hs : l.val < basicApproxCountStop N ω) :
    basicApproxCountObserved N ω ⟨l.val - 1, by omega⟩ = 0 := by
  unfold basicApproxCountStop at hs
  split at hs
  · rename_i k hk
    have hmin := (Fin.mem_find?_iff.mp hk).2
    have h := hmin ⟨l.val - 1, by omega⟩ (by apply Fin.mk_lt_mk.mpr; omega)
    simpa using! h
  · rename_i hn
    simpa using! (Fin.find?_eq_none_iff.mp hn) ⟨l.val - 1, by omega⟩

/-- Bounds `2^s` by `2^n` plus the dyadic layers with indices between `n` and `s`, within a
finite cap. -/
private theorem costPower_layers (s n L : ℕ) (hs : s ≤ L) :
    (2 : ℝ) ^ s ≤ (2 : ℝ) ^ n +
      ∑ l : Fin L, if n ≤ l.val ∧ l.val < s then (2 : ℝ) ^ l.val else 0 := by
  have hsum (s : ℕ) : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ n +
      ∑ l ∈ Finset.range s, if n ≤ l then (2 : ℝ) ^ l else 0 := by
    induction s with
    | zero => simp; exact one_le_pow₀ (by norm_num)
    | succ s ih =>
      rw [Finset.sum_range_succ]
      by_cases hn : n ≤ s
      · rw [if_pos hn, pow_succ]
        linarith
      · have hp : (2 : ℝ) ^ (s + 1) ≤ (2 : ℝ) ^ n :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        exact hp.trans (le_add_of_nonneg_right (by positivity))
  have he : (∑ l : Fin L, if n ≤ l.val ∧ l.val < s then (2 : ℝ) ^ l.val else 0) =
      ∑ l ∈ Finset.range s, if n ≤ l then (2 : ℝ) ^ l else 0 := by
    change (∑ l : Fin L, (fun k : ℕ => if n ≤ k ∧ k < s then (2 : ℝ) ^ k else 0) l.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if n ≤ k ∧ k < s then (2 : ℝ) ^ k else 0) L]
    have hsplit :=
        Finset.sum_range_add (fun l : ℕ => if n ≤ l ∧ l < s then (2 : ℝ) ^ l else 0) s (L - s)
    rw [Nat.add_sub_of_le hs] at hsplit
    rw [hsplit]
    have hz : (∑ l ∈ Finset.range (L - s), if n ≤ s + l ∧ s + l < s then (2 : ℝ) ^ (s + l) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      simp
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro l hl
    simp [Finset.mem_range.mp hl]
  rw [he]
  exact hsum s

/-- The finite tail of the geometric series with ratio 1/2 starting at `n` is at most `2 *
(1/2)^n`. -/
private theorem costTail_sum (L n : ℕ) :
    (∑ l : Fin L, if n ≤ l.val then (1 / 2 : ℝ) ^ l.val else 0) ≤ 2 * (1 / 2 : ℝ) ^ n := by
  have he (L : ℕ) : (∑ l ∈ Finset.range L, if n ≤ l then (1 / 2 : ℝ) ^ l else 0) =
      if n ≤ L then 2 * ((1 / 2 : ℝ) ^ n - (1 / 2 : ℝ) ^ L) else 0 := by
    induction L with
    | zero => by_cases hn : n = 0 <;> simp [hn]
    | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hn : n ≤ L
      · simp only [if_pos hn, if_pos (show n ≤ L + 1 by omega), pow_succ]
        ring
      · by_cases heq : n = L + 1
        · simp [heq]
        · simp [hn, show ¬n ≤ L + 1 by omega]
  change (∑ l : Fin L, (fun k : ℕ => if n ≤ k then (1 / 2 : ℝ) ^ k else 0) l.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if n ≤ k then (1 / 2 : ℝ) ^ k else 0) L, he]
  split_ifs <;> nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) L,
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

/-- For a nonempty marked set and positive round index `l`, the probability of continuing past
`l` is at most `1 / (2^(2*l) * (S.card / N))`. -/
private theorem costLate_zero_bound {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card)
    (l : Fin (basicApproxCountLoopCap N)) (hl : 0 < l.val) :
    (∑ ω : CostRecords N, if l.val < basicApproxCountStop N ω
      then basicApproxCountPrefixWeight hN S ω else 0) ≤
      1 / (((2 : ℝ) ^ l.val) ^ 2 * ((S.card : ℝ) / N)) := by
  let k : Fin (basicApproxCountLoopCap N) := ⟨l.val - 1, by omega⟩
  have hm : 2 ≤ 2 * 2 ^ k.val := by
    have h : 0 < 2 ^ k.val := by positivity
    omega
  have hp := aeLaw_zero_label_mass_bound (2 * 2 ^ k.val) hm (QFTMatrix N)
    ⟨0, hN⟩ S (qftMatrix_unitary hN) (by
      rw [prepared_qft_mark_mass]
      exact div_pos (by exact_mod_cast hS) (by exact_mod_cast hN))
  rw [prepared_qft_mark_mass] at hp
  have hpow : 2 * 2 ^ k.val = 2 ^ l.val := by
    dsimp [k]
    rw [← pow_succ']
    congr 1
    omega
  change (basicApproxCountLoopLaw hN S k).prob ⟨0, by positivity⟩ ≤ _ at hp
  have hpowr : ((2 * 2 ^ k.val : ℕ) : ℝ) = (2 : ℝ) ^ l.val := by exact_mod_cast hpow
  rw [hpowr] at hp
  refine le_trans ?_ hp
  rw [← costCoordinate_zero hN S k]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hs : l.val < basicApproxCountStop N ω
  · have hz := costStop_previous_zero N ω l hl hs
    change basicApproxCountObserved N ω k = 0 at hz
    simp [hs, hz]
  · simp only [if_neg hs]
    split_ifs <;> first | exact costWeight_nonneg hN S ω | exact le_rfl

/-- The expected contribution of a late dyadic stopping layer is bounded by a geometric term
divided by the marked fraction. -/
private theorem costLate_layer_bound {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card)
    (n : ℕ) (hn : 0 < n) (l : Fin (basicApproxCountLoopCap N)) :
    (∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω *
      (if n ≤ l.val ∧ l.val < basicApproxCountStop N ω then (2 : ℝ) ^ l.val else 0)) ≤
      if n ≤ l.val then (1 / ((S.card : ℝ) / N)) * (1 / 2 : ℝ) ^ l.val else 0 := by
  by_cases hl : n ≤ l.val
  · rw [if_pos hl]
    have hp := costLate_zero_bound hN S hS l (by omega)
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 ^ l.val)
    have he : (∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω *
        (if n ≤ l.val ∧ l.val < basicApproxCountStop N ω then (2 : ℝ) ^ l.val else 0)) =
        (2 : ℝ) ^ l.val * ∑ ω : CostRecords N,
          if l.val < basicApproxCountStop N ω then basicApproxCountPrefixWeight hN S ω else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      simp only [hl, true_and]
      split_ifs <;> ring
    rw [he]
    apply hm.trans_eq
    rw [div_pow, one_pow]
    have ha : (0 : ℝ) < (S.card : ℝ) / N :=
      div_pos (by exact_mod_cast hS) (by exact_mod_cast hN)
    field_simp
  · simp [hl]

/-- For `r ≥ 1`, there is a positive dyadic exponent whose power lies between `2 * Real.sqrt r`
and `4 * Real.sqrt r`. -/
private theorem costScale_window (r : ℝ) (hr : 1 ≤ r) :
    ∃ n : ℕ, 0 < n ∧ 2 * Real.sqrt r ≤ (2 : ℝ) ^ n ∧ (2 : ℝ) ^ n ≤ 4 * Real.sqrt r := by
  let n := Nat.ceil (Real.logb 2 (2 * Real.sqrt r))
  have hs : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by linarith : 1 ≤ 2 * Real.sqrt r)
  have hlow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.le_ceil (Real.logb 2 (2 * Real.sqrt r)))
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at hlow
  have hhigh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.ceil_lt_add_one hlog).le
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
    Real.rpow_one, Real.rpow_natCast] at hhigh
  refine ⟨n, ?_, hlow, ?_⟩
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    change 2 * Real.sqrt r ≤ (2 : ℝ) ^ n at hlow
    rw [hn0, pow_zero] at hlow
    linarith
  · exact hhigh.trans_eq (by ring)

/-- For a nonempty marked set, `costPowerMean` is at most eight times the square root of the
inverse marked fraction. -/
private theorem costMean_upper {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card) :
    costPowerMean hN S ≤ 8 * Real.sqrt ((N : ℝ) / S.card) := by
  have ht : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htN : (S.card : ℝ) ≤ N := by exact_mod_cast
    (show S.card ≤ N by simpa using! S.card_le_univ)
  let r : ℝ := (N : ℝ) / S.card
  let a : ℝ := (S.card : ℝ) / N
  have hr : 1 ≤ r := (le_div_iff₀ ht).mpr (by simpa using! htN)
  have ha : 0 < a := div_pos ht hNr
  obtain ⟨n, hn, hlow, hhigh⟩ := costScale_window r hr
  have hmean : costPowerMean hN S ≤ (2 : ℝ) ^ n +
      (1 / a) * ∑ l : Fin (basicApproxCountLoopCap N),
        if n ≤ l.val then (1 / 2 : ℝ) ^ l.val else 0 := by
    calc
      _ ≤ ∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω *
          ((2 : ℝ) ^ n + ∑ l : Fin (basicApproxCountLoopCap N),
            if n ≤ l.val ∧ l.val < basicApproxCountStop N ω then (2 : ℝ) ^ l.val else 0) := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_left
          (costPower_layers _ n _ (costStop_le_cap N ω)) (costWeight_nonneg hN S ω)
      _ = (2 : ℝ) ^ n + ∑ l : Fin (basicApproxCountLoopCap N), ∑ ω : CostRecords N,
          basicApproxCountPrefixWeight hN S ω *
            (if n ≤ l.val ∧ l.val < basicApproxCountStop N ω then (2 : ℝ) ^ l.val else 0) := by
        simp_rw [mul_add, Finset.mul_sum]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, basicApproxCountPrefixWeight_sum, one_mul,
          Finset.sum_comm]
      _ ≤ (2 : ℝ) ^ n + ∑ l : Fin (basicApproxCountLoopCap N),
          if n ≤ l.val then (1 / a) * (1 / 2 : ℝ) ^ l.val else 0 := by
        exact add_le_add le_rfl (Finset.sum_le_sum (fun l _ => costLate_layer_bound hN S hS n hn l))
      _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs <;> ring
  have htail : (1 / a) * (2 * (1 / 2 : ℝ) ^ n) ≤ Real.sqrt r := by
    have har : a * r = 1 := by dsimp [a, r]; field_simp
    have hs : a * Real.sqrt r ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith : 0 ≤ r)]; exact har
    have hm := mul_le_mul_of_nonneg_right hlow
      (mul_nonneg ha.le (Real.sqrt_nonneg r))
    have he : (1 / a) * (2 * (1 / 2 : ℝ) ^ n) = 2 / (a * (2 : ℝ) ^ n) := by
      rw [div_pow, one_pow]
      ring
    rw [he, div_le_iff₀ (by positivity : 0 < a * (2 : ℝ) ^ n)]
    nlinarith only [hm, hs]
  have htailmean := mul_le_mul_of_nonneg_left (costTail_sum (basicApproxCountLoopCap N) n)
    (by positivity : 0 ≤ 1 / a)
  change costPowerMean hN S ≤ 8 * Real.sqrt r
  linarith [Real.sqrt_nonneg r]

/-- The sum of preliminary grid sizes before stopping index `s` is `2 * 2^s - 2`. -/
private theorem costFinite_loop_sum (L s : ℕ) (hs : s ≤ L) :
    (∑ l : Fin L, if l.val < s then (2 * 2 ^ l.val : ℝ) else 0) = 2 * (2 : ℝ) ^ s - 2 := by
  have he : (∑ l : Fin L, if l.val < s then (2 * 2 ^ l.val : ℝ) else 0) =
      ∑ l ∈ Finset.range s, (2 * 2 ^ l : ℝ) := by
    change (∑ l : Fin L, (fun k : ℕ => if k < s then (2 * 2 ^ k : ℝ) else 0) l.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < s then (2 * 2 ^ k : ℝ) else 0) L,
      ← Finset.sum_filter]
    have hfilter : (Finset.range L).filter (fun l => l < s) = Finset.range s := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter]
  rw [he]
  have hgeom (m : ℕ) : (∑ l ∈ Finset.range m, (2 * 2 ^ l : ℝ)) = 2 * (2 : ℝ) ^ m - 2 := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [Finset.sum_range_succ, pow_succ, ih]; ring
  exact hgeom s

/-- For positive `ε`, bounds the total cost of each readout record above and below by explicit
multiples of two raised to its stopping index. -/
private theorem costPoint_bounds (N : ℕ) (ε : ℝ) (hε : 0 < ε) (ω : CostRecords N) :
    20 * Real.pi ^ 2 / ε * (2 : ℝ) ^ basicApproxCountStop N ω ≤ (basicApproxCountTotalCost N ε ω : ℝ) ∧
    (basicApproxCountTotalCost N ε ω : ℝ) ≤
      (2 + 20 * Real.pi ^ 2 / ε) * (2 : ℝ) ^ basicApproxCountStop N ω + 1 := by
  have he : (basicApproxCountTotalCost N ε ω : ℝ) =
      (2 * (2 : ℝ) ^ basicApproxCountStop N ω - 2) +
        (basicApproxCountFinalM ε (basicApproxCountStop N ω) : ℝ) := by
    unfold basicApproxCountTotalCost
    push_cast
    rw [costFinite_loop_sum _ _ (costStop_le_cap N ω)]
  have hl : 20 * Real.pi ^ 2 / ε * (2 : ℝ) ^ basicApproxCountStop N ω ≤
      (basicApproxCountFinalM ε (basicApproxCountStop N ω) : ℝ) := Nat.le_ceil _
  have hu : (basicApproxCountFinalM ε (basicApproxCountStop N ω) : ℝ) <
      20 * Real.pi ^ 2 / ε * (2 : ℝ) ^ basicApproxCountStop N ω + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hp : 1 ≤ (2 : ℝ) ^ basicApproxCountStop N ω := one_le_pow₀ (by norm_num)
  rw [he]
  constructor <;> nlinarith

/-- For positive `ε`, bounds the expected total cost above and below in terms of
`costPowerMean`. -/
private theorem costExpectation_bounds {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (ε : ℝ) (hε : 0 < ε) :
    20 * Real.pi ^ 2 / ε * costPowerMean hN S ≤
      (∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω * (basicApproxCountTotalCost N ε ω : ℝ)) ∧
    (∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω * (basicApproxCountTotalCost N ε ω : ℝ)) ≤
      (2 + 20 * Real.pi ^ 2 / ε) * costPowerMean hN S + 1 := by
  constructor
  · rw [costPowerMean, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    simpa only [mul_assoc, mul_left_comm] using! mul_le_mul_of_nonneg_left
      (costPoint_bounds N ε hε ω).1 (costWeight_nonneg hN S ω)
  · calc
      _ ≤ ∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω *
          ((2 + 20 * Real.pi ^ 2 / ε) * (2 : ℝ) ^ basicApproxCountStop N ω + 1) := by
        exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left
          (costPoint_bounds N ε hε ω).2 (costWeight_nonneg hN S ω))
      _ = _ := by
        have he (ω : CostRecords N) : basicApproxCountPrefixWeight hN S ω *
            ((2 + 20 * Real.pi ^ 2 / ε) * (2 : ℝ) ^ basicApproxCountStop N ω + 1) =
            (2 + 20 * Real.pi ^ 2 / ε) *
              (basicApproxCountPrefixWeight hN S ω * (2 : ℝ) ^ basicApproxCountStop N ω) +
              basicApproxCountPrefixWeight hN S ω := by ring
        rw [Finset.sum_congr rfl (fun ω _ => he ω), Finset.sum_add_distrib,
          ← Finset.mul_sum, basicApproxCountPrefixWeight_sum]
        rfl

/-- For an empty marked set, each preliminary loop law is concentrated at the zero label. -/
private theorem costZero_record {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0)
    (l : Fin (basicApproxCountLoopCap N)) (z : Fin (2 * 2 ^ l.val)) :
    (basicApproxCountLoopLaw hN S l).prob z = if z = ⟨0, by positivity⟩ then 1 else 0 := by
  have ha : MeasureProb (preparedAAState (QFTMatrix N) ⟨0, hN⟩) S = 0 := by
    rw [prepared_qft_mark_mass, hS, Nat.cast_zero, zero_div]
  have hm : 2 ≤ 2 * 2 ^ l.val := by
    have hp : 0 < 2 ^ l.val := by positivity
    omega
  change (aeLaw _ (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hm).prob z = _
  rw [aeLaw_zero_mass _ hm _ _ _ _ ha]
  have hk := (offgrid_phase_geometric_and_periodic (2 * 2 ^ l.val) 0 z (by positivity)).2.2
    (⟨0, by positivity⟩ : Fin (2 * 2 ^ l.val))
  norm_num at hk
  rw [hk]
  by_cases hz : z.val = 0 <;> simp [Ket, Fin.ext_iff, hz]

/-- For an empty marked set, every readout record of nonzero weight stops at the loop cap. -/
private theorem costZero_stop {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0)
    (ω : CostRecords N) (hw : basicApproxCountPrefixWeight hN S ω ≠ 0) :
    basicApproxCountStop N ω = basicApproxCountLoopCap N := by
  change (∏ l, (basicApproxCountLoopLaw hN S l).prob (ω l)) ≠ 0 at hw
  have hp := Finset.prod_ne_zero_iff.mp hw
  have hz (l : Fin (basicApproxCountLoopCap N)) : ω l = ⟨0, by positivity⟩ := by
    by_contra hl
    have h := costZero_record hN S hS l (ω l)
    rw [if_neg hl] at h
    exact hp l (Finset.mem_univ l) h
  have hobs (l : Fin (basicApproxCountLoopCap N)) : basicApproxCountObserved N ω l = 0 := by
    simp [basicApproxCountObserved, hz l, aeEstimate]
  unfold basicApproxCountStop
  have hn : Fin.find? (fun l : Fin (basicApproxCountLoopCap N) =>
      decide (basicApproxCountObserved N ω l ≠ 0)) = none :=
    Fin.find?_eq_none_iff.mpr (fun l => by simp [hobs l])
  rw [hn]

/-- For an empty marked set, `costPowerMean` equals two raised to the loop cap. -/
private theorem costMean_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0) :
    costPowerMean hN S = (2 : ℝ) ^ basicApproxCountLoopCap N := by
  calc
    _ = ∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω * (2 : ℝ) ^ basicApproxCountLoopCap N := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hw : basicApproxCountPrefixWeight hN S ω = 0
      · simp [hw]
      · rw [costZero_stop hN S hS ω hw]
    _ = _ := by rw [← Finset.sum_mul, basicApproxCountPrefixWeight_sum, one_mul]

/-- For an empty marked set, the expected cost equals the full preliminary-loop cost plus the
final grid size at the cap. -/
theorem bhmt_basic_approx_count_zero_cost {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0)
    (ε : ℝ) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω * (basicApproxCountTotalCost N ε ω : ℝ)) =
      2 * (2 : ℝ) ^ basicApproxCountLoopCap N - 2 +
        (basicApproxCountFinalM ε (basicApproxCountLoopCap N) : ℝ) := by
  let c := 2 * (2 : ℝ) ^ basicApproxCountLoopCap N - 2 +
    (basicApproxCountFinalM ε (basicApproxCountLoopCap N) : ℝ)
  calc
    _ = ∑ ω : CostRecords N, basicApproxCountPrefixWeight hN S ω * c := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hw : basicApproxCountPrefixWeight hN S ω = 0
      · simp [hw]
      · congr 1
        unfold basicApproxCountTotalCost
        rw [costZero_stop hN S hS ω hw]
        push_cast
        rw [costFinite_loop_sum _ _ le_rfl]
    _ = _ := by rw [← Finset.sum_mul, basicApproxCountPrefixWeight_sum, one_mul]

/-- Establishes the explicit expected-cost bounds for adaptive approximate counting with
relative error in `(0, 1]`, as formulated in `Theorem15ExpectedCostSpec.expected` [Brassard
et al., Theorem 15][BrassardEtAl2002]. -/
theorem bhmt_basic_approx_count_expected_cost :
    Theorem15ExpectedCostSpec.expected := by
  intro N S hN ε hε hε1
  have hK : 0 < 20 * Real.pi ^ 2 / ε := by positivity
  have hb := costExpectation_bounds hN S ε hε
  have hroot : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
  constructor
  · intro hS
    rw [costMean_zero hN S hS] at hb
    have hl := mul_le_mul_of_nonneg_left (basicApproxCountLoopCap_power N hN) hK.le
    have hu :=
        mul_le_mul_of_nonneg_left (costCap_upper N hN)
        (by positivity : 0 ≤ 2 + 20 * Real.pi ^ 2 / ε)
    simp only [div_eq_mul_inv] at hl hu hb ⊢
    constructor
    · nlinarith [hb.1]
    · nlinarith [hb.2]
  · intro hS
    have hl := mul_le_mul_of_nonneg_left (costMean_lower hN S hS) hK.le
    have he : (20 * Real.pi ^ 2 / ε) * (7 / (40 * Real.pi) * Real.sqrt ((N : ℝ) / S.card)) =
        7 * Real.pi / 2 * (1 / ε) * Real.sqrt ((N : ℝ) / S.card) := by field_simp; ring
    rw [he] at hl
    have hu := mul_le_mul_of_nonneg_left (costMean_upper hN S hS)
      (by positivity : 0 ≤ 2 + 20 * Real.pi ^ 2 / ε)
    have ht : (0 : ℝ) < S.card := by exact_mod_cast hS
    have htN : (S.card : ℝ) ≤ N := by exact_mod_cast
      (show S.card ≤ N by simpa using! S.card_le_univ)
    have hr : 1 ≤ Real.sqrt ((N : ℝ) / S.card) :=
      Real.one_le_sqrt.mpr ((le_div_iff₀ ht).mpr (by simpa using! htN))
    have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hc : (2 + 20 * Real.pi ^ 2 / ε) * 8 ≤ 1616 / ε := by
      apply (le_div_iff₀ hε).mpr
      have hec : ((2 + 20 * Real.pi ^ 2 / ε) * 8) * ε = (2 * ε + 20 * Real.pi ^ 2) * 8 := by
        field_simp
      rw [hec]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg ((N : ℝ) / S.card))
    have hi : 1 ≤ (1 / ε) * Real.sqrt ((N : ℝ) / S.card) := by
      have hεinv : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using! hε1)
      exact one_le_mul_of_one_le_of_one_le hεinv hr
    refine ⟨hl.trans hb.1, ?_⟩
    simp only [div_eq_mul_inv] at hu hmul hi hb ⊢
    nlinarith [hb.2]

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
