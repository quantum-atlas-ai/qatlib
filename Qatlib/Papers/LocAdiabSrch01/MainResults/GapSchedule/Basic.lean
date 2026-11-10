/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
noncomputable section

open Real
open MeasureTheory
open scoped Interval

namespace Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule

def gapSq (N s : ℝ) : ℝ := 1 - 4 * ((N - 1) / N) * (s * (1 - s))

def gap (N s : ℝ) : ℝ := sqrt (gapSq N s)

def localRate (ε N s : ℝ) : ℝ := ε * gapSq N s

def localAdiabaticIntegral (ε N : ℝ) : ℝ :=
  (1 / ε) * ∫ s in (0 : ℝ)..1, 1 / gapSq N s

def localAdiabaticTime (ε N : ℝ) : ℝ :=
  N / (ε * sqrt (N - 1)) * arctan (sqrt (N - 1))

theorem gapSq_pos {N s : ℝ} (hN : 1 < N) : 0 < gapSq N s := by
  have hNpos : 0 < N := by linarith
  have hfac : 0 ≤ 4 * ((N - 1) / N) := by
    have : 0 < (N - 1) / N := div_pos (by linarith) hNpos
    linarith
  have hs : s * (1 - s) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (s - 1 / 2)]
  have hb : 4 * ((N - 1) / N) * (s * (1 - s)) ≤ 4 * ((N - 1) / N) * (1 / 4) :=
    mul_le_mul_of_nonneg_left hs hfac
  have hkey : 4 * ((N - 1) / N) * (1 / 4) = (N - 1) / N := by ring
  have hlt : (N - 1) / N < 1 := by
    rw [div_lt_one hNpos]
    linarith
  unfold gapSq
  nlinarith [hb, hkey, hlt]

theorem gapSq_half {N : ℝ} (hN : 0 < N) : gapSq N (1 / 2) = 1 / N := by
  unfold gapSq
  field_simp
  ring

theorem gap_half {N : ℝ} (hN : 0 < N) : gap N (1 / 2) = 1 / sqrt N := by
  unfold gap
  rw [gapSq_half hN, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) N, Real.sqrt_one]

theorem gap_ge_half {N s : ℝ} (hN : 1 < N) :
    1 / sqrt N ≤ gap N s := by
  have hNpos : 0 < N := by linarith
  have hpos := gapSq_pos hN (s := s)
  rw [gap, Real.le_sqrt (by positivity) hpos.le]
  have hfac : 0 ≤ 4 * ((N - 1) / N) := by
    have : 0 < (N - 1) / N := div_pos (by linarith) hNpos
    linarith
  have hs : s * (1 - s) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (s - 1 / 2)]
  have hb : 4 * ((N - 1) / N) * (s * (1 - s)) ≤ 4 * ((N - 1) / N) * (1 / 4) :=
    mul_le_mul_of_nonneg_left hs hfac
  have hkey : 4 * ((N - 1) / N) * (1 / 4) = (N - 1) / N := by ring
  have hsplit : (N - 1) / N = 1 - 1 / N := by
    rw [sub_div, div_self (ne_of_gt hNpos)]
  have hsq : (1 / sqrt N) ^ 2 = 1 / N := by
    rw [div_pow, Real.sq_sqrt hNpos.le]
    norm_num
  rw [hsq]
  unfold gapSq
  nlinarith [hb, hkey, hsplit]

theorem gapSchedule_time_eq_integral {ε N : ℝ} (hε : 0 < ε) (hN : 1 < N) :
    localAdiabaticTime ε N = localAdiabaticIntegral ε N := by
  have hNpos : 0 < N := by linarith
  have hc : 0 < sqrt (N - 1) := sqrt_pos.mpr (by linarith)
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hcne : sqrt (N - 1) ≠ 0 := ne_of_gt hc
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1) * (2 * s - 1)))
        (1 / gapSq N s) s := by
    intro s _
    have hinner : HasDerivAt (fun s : ℝ => sqrt (N - 1) * (2 * s - 1))
        (sqrt (N - 1) * 2) s := by
      have h1 : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 s := by
        simpa using ((hasDerivAt_id s).const_mul 2).sub_const 1
      simpa using h1.const_mul (sqrt (N - 1))
    have h2 : HasDerivAt (fun s => arctan (sqrt (N - 1) * (2 * s - 1)))
        (1 / (1 + (sqrt (N - 1) * (2 * s - 1)) ^ 2) * (sqrt (N - 1) * 2)) s :=
      hinner.arctan
    have h3 := h2.const_mul (N / (2 * sqrt (N - 1)))
    convert! h3 using 1
    have hsq : (sqrt (N - 1)) ^ 2 = N - 1 := sq_sqrt (by linarith)
    unfold gapSq
    rw [show 1 + (sqrt (N - 1) * (2 * s - 1)) ^ 2 = N - 4 * (N - 1) * s * (1 - s) by
      rw [mul_pow, hsq]; ring]
    field_simp [hNne, hcne]
  have hcont : ContinuousOn
      (fun s => N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1) * (2 * s - 1)))
      (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hcont' : ContinuousOn (fun s : ℝ => 1 / gapSq N s) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const (by unfold gapSq; fun_prop) ?_
    intro s _
    exact ne_of_gt (gapSq_pos hN)
  have hint : IntervalIntegrable (fun s : ℝ => 1 / gapSq N s) volume (0 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont'
  have hFTC : ∫ s in (0 : ℝ)..1, 1 / gapSq N s
      = (N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1) * (2 * 1 - 1)))
        - (N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1) * (2 * 0 - 1))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (f := fun s => N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1) * (2 * s - 1)))
      (f' := fun s => 1 / gapSq N s) hderiv hint
  have h1v : N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1) * (2 * 1 - 1))
      = N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1)) := by norm_num
  have h0v : N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1) * (2 * 0 - 1))
      = -(N / (2 * sqrt (N - 1)) * arctan (sqrt (N - 1))) := by
    have : sqrt (N - 1) * (2 * 0 - 1) = -(sqrt (N - 1)) := by ring
    rw [this, arctan_neg]
    ring
  unfold localAdiabaticTime localAdiabaticIntegral
  rw [hFTC, h1v, h0v]
  field_simp [hε.ne', hcne, hNne]
  ring

theorem localAdiabaticTime_div_sqrt {ε N : ℝ} (hε : 0 < ε) (hN : 1 < N) :
    localAdiabaticTime ε N / sqrt N
      = sqrt (N / (N - 1)) * (arctan (sqrt (N - 1)) / ε) := by
  have hNpos : 0 < N := by linarith
  have hc : 0 < sqrt (N - 1) := sqrt_pos.mpr (by linarith)
  unfold localAdiabaticTime
  rw [Real.sqrt_div hNpos.le (N - 1)]
  field_simp
  nlinarith [sq_sqrt hNpos.le, sq_sqrt (show (0 : ℝ) ≤ N - 1 by linarith)]

end Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule
