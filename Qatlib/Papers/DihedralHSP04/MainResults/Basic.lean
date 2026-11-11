/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Qatlib.Papers.DihedralHSP04.MainResults.StatisticalAnalysis

/-!
# Subexponential pipeline schedules for the dihedral problem

This module chooses the integer block length `Nat.sqrt (n * (Nat.log2 n + 1))` and bounds the
resulting pipeline resources. It proves a subexponential time envelope, a polynomial space
envelope, and a uniform combination success probability of at least one half for the constructed
schedules.

These constructions accompany the results of [Regev2004a].

## Main statements

* `time_bound`: bounds the explicit time expression by `2 ^ (64 * sqrt (n * log n))`.
* `space_bound`: bounds the block-count times block-width expression quadratically.
* `dihedralHSPSubexponentialPolySpace`: constructs schedules meeting the resource and success
  predicates.

## References

* [Regev, 2004][Regev2004a]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihedralHSP04.MainResults

open scoped BigOperators

/-- The existence of a positive constant such that every input size at least two has a pipeline
schedule within the specified subexponential time and polynomial space envelopes, with
uniform combination success probability at least one half for every residue. -/
def DihedralHSPSubexponentialPolySpace : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n →
      ∃ P : PipelineSchedule,
        P.n = n ∧
        (P.time : ℝ) ≤ subexponentialEnvelope n C ∧
        (P.space : ℝ) ≤ polynomialSpaceEnvelope n ∧
        (∀ z : ZMod (2 ^ P.l),
          (1 : ℝ) / 2 ≤
            uniformProb (fun y : SampleSpace P.l => combinationSucceeds P.l y z))

/-- For `n ≥ 2`, the natural logarithm of `n` is at most `(Nat.log2 n + 1) * log 2`. -/
lemma b_lower (n : ℕ) (hn : 2 ≤ n) :
    Real.log n ≤ (Nat.log2 n + 1 : ℝ) * Real.log 2 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlt : (n : ℝ) < 2 ^ (Nat.log2 n + 1 : ℕ) := by
    have hN : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    exact_mod_cast hN
  have hlog := Real.log_lt_log hnpos hlt
  rw [Real.log_pow] at hlog
  push_cast at hlog
  exact le_of_lt hlog

/-- For `n ≥ 2`, `Nat.log2 n + 1` is at most `4 * log n`. -/
lemma b_upper (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log2 n + 1 : ℝ) ≤ 4 * Real.log n := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog2gt : (2/3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hle := Real.log2_le_logb n
  have hlogb : Real.logb 2 (n:ℝ) = Real.log n / Real.log 2 := by
    rw [← Real.log_div_log]
  rw [hlogb] at hle
  have hkey : Real.log n / Real.log 2 ≤ (3/2) * Real.log n := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [hlog2gt, hlogn]
  have hln2gt : (0.4 : ℝ) < Real.log n := by
    have hn2R : (2:ℝ) ≤ n := by exact_mod_cast hn
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2R
    linarith [Real.log_two_gt_d9]
  linarith

/-- For `n ≥ 2`, the chosen natural square-root block length, cast to the reals, is at most the
corresponding real square root. -/
lemma l_le_sqrt (n : ℕ) (hn : 2 ≤ n) :
    (Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) ≤
      Real.sqrt ((n : ℝ) * (Nat.log2 n + 1 : ℕ)) := by
  have h := Nat.sqrt_le' (n * (Nat.log2 n + 1))
  have h2 : ((Nat.sqrt (n * (Nat.log2 n + 1)) : ℕ) : ℝ) ^ 2 ≤
      ((n * (Nat.log2 n + 1) : ℕ) : ℝ) := by exact_mod_cast h
  have hcast : ((n * (Nat.log2 n + 1) : ℕ) : ℝ) = (n:ℝ) * (Nat.log2 n + 1 : ℕ) := by push_cast; ring
  rw [hcast] at h2
  have hnn : (0:ℝ) ≤ (Nat.sqrt (n * (Nat.log2 n + 1)) : ℕ) := by positivity
  exact (Real.le_sqrt hnn (by positivity)).mpr h2

/-- For `n ≥ 2`, `sqrt (n * log n)` is at most the real square root of `n * (Nat.log2 n + 1)`. -/
lemma sqrt_nb_ge_B (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt ((n:ℝ) * Real.log n) ≤
      Real.sqrt ((n:ℝ) * (Nat.log2 n + 1 : ℕ)) := by
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hlog2le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hb := b_lower n hn
  have hbnonneg : (0:ℝ) ≤ (Nat.log2 n + 1 : ℕ) := by positivity
  have hmul : ((Nat.log2 n : ℝ) + 1) * Real.log 2 ≤ ((Nat.log2 n : ℝ) + 1) := by
    have hbR : (0:ℝ) ≤ (Nat.log2 n : ℝ) + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hlog2le hbR
    simpa using this
  have hbge : Real.log n ≤ ((Nat.log2 n : ℝ) + 1) := le_trans hb hmul
  have hbge' : Real.log n ≤ (Nat.log2 n + 1 : ℕ) := by
    push_cast
    exact hbge
  exact Real.sqrt_le_sqrt (by nlinarith [hbge', hn0])

/-- For `n ≥ 2`, the chosen natural square-root block length is at least half the corresponding
real square root. -/
lemma l_ge_half (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt ((n:ℝ) * (Nat.log2 n + 1 : ℕ)) / 2 ≤
      (Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) := by
  set l := Nat.sqrt (n * (Nat.log2 n + 1)) with hl
  set P := (n:ℝ) * (Nat.log2 n + 1 : ℕ) with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hlt : P < ((l:ℝ)+1)^2 := by
    have h := Nat.lt_succ_sqrt' (n * (Nat.log2 n + 1))
    rw [← hl] at h
    have hcast : P = ((n * (Nat.log2 n + 1) : ℕ) : ℝ) := by rw [hP]; push_cast; ring
    rw [hcast]
    have h' : (n * (Nat.log2 n + 1) : ℕ) < (l + 1) ^ 2 := h
    have := (Nat.cast_lt (α := ℝ)).mpr h'
    push_cast at this ⊢
    exact this
  have hsqrt_lt : Real.sqrt P < (l:ℝ)+1 := by
    have hy : (0:ℝ) < (l:ℝ)+1 := by positivity
    exact (Real.sqrt_lt' hy).mpr hlt
  have hs : 2 ≤ Real.sqrt P := by
    rw [Real.le_sqrt (by norm_num) hP0]
    have h2 : (2:ℝ)^2 = 4 := by norm_num
    rw [h2]
    rw [hP]
    have hb2 : (2:ℝ) ≤ (Nat.log2 n + 1 : ℕ) := by
      have h1 : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simpa using hn)
      have : 2 ≤ Nat.log2 n + 1 := by omega
      exact_mod_cast this
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith [hb2, hn2]
  nlinarith [hsqrt_lt, hs]

/-- For `n ≥ 2`, the chosen natural square-root block length, cast to the reals, is at most `n`. -/
lemma l_le_n (n : ℕ) (hn : 2 ≤ n) :
    (Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) ≤ n := by
  have h1 := l_le_sqrt n hn
  have hb_le_n : (Nat.log2 n + 1 : ℕ) ≤ n := by
    have hn0 : n ≠ 0 := by omega
    have hlt : Nat.log2 n < n := (Nat.log2_lt hn0).mpr Nat.lt_two_pow_self
    omega
  have hbR : (Nat.log2 n + 1 : ℕ) ≤ (n:ℝ) := by exact_mod_cast hb_le_n
  have hn0R : (0:ℝ) ≤ n := by positivity
  have h2 : Real.sqrt ((n:ℝ) * (Nat.log2 n + 1 : ℕ)) ≤ n := by
    rw [Real.sqrt_le_left hn0R]
    calc (n:ℝ) * (Nat.log2 n + 1 : ℕ) ≤ (n:ℝ) * (n:ℝ) := by nlinarith [hbR, hn0R]
      _ = (n:ℝ)^2 := by ring
  linarith [h1, h2]

/-- For `n ≥ 2`, the logarithm of the chosen block length plus four is at most `4 * log n`. -/
lemma log_l4_le (n : ℕ) (hn : 2 ≤ n) :
    Real.log ((Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) + 4) ≤ 4 * Real.log n := by
  set P := (n:ℝ) * (Nat.log2 n + 1 : ℕ) with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hnb : (Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) + 4 ≤ 2 * P := by
    have h1 := l_le_sqrt n hn
    have hPb : (4:ℝ) ≤ P := by
      rw [hP]
      have hb2 : (2:ℝ) ≤ (Nat.log2 n + 1 : ℕ) := by
        have h1 : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simpa using hn)
        have : 2 ≤ Nat.log2 n + 1 := by omega
        exact_mod_cast this
      have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      nlinarith [hb2, hn2]
    have hsq_le : Real.sqrt P ≤ P := by
      rw [Real.sqrt_le_left hP0]
      nlinarith [hP0, hPb]
    nlinarith [h1, hsq_le, hPb]
  have hlt23 : 2 * P ≤ (n:ℝ)^3 := by
    have hb_le_n : (Nat.log2 n + 1 : ℕ) ≤ n := by
      have hn0 : n ≠ 0 := by omega
      have hlt : Nat.log2 n < n := (Nat.log2_lt hn0).mpr Nat.lt_two_pow_self
      omega
    have hbR : (Nat.log2 n + 1 : ℕ) ≤ (n:ℝ) := by exact_mod_cast hb_le_n
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0R : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hfac : (n:ℝ)^3 - 2*(n:ℝ)^2 = (n:ℝ)^2 * ((n:ℝ) - 2) := by ring
    have hnn : 0 ≤ (n:ℝ)^2 * ((n:ℝ) - 2) :=
      mul_nonneg (by positivity) (by linarith)
    rw [hP]
    nlinarith [hbR, hn0R, hn2, hfac, hnn]
  have hpos : (0:ℝ) < (Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) + 4 := by positivity
  have hlog1 : Real.log ((Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) + 4) ≤
      Real.log (2 * P) :=
    Real.log_le_log hpos hnb
  have hpos2 : (0:ℝ) < 2 * P := by rw [hP]; positivity
  have hlog2 : Real.log (2 * P) ≤ Real.log ((n:ℝ)^3) :=
    Real.log_le_log hpos2 hlt23
  have hpow : Real.log ((n:ℝ)^3) = 3 * Real.log n := by
    rw [Real.log_pow]; push_cast; ring
  linarith [hlog1, hlog2, hpow.le, Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1:ℝ) ≤ n)]

/-- For `n ≥ 2`, the real quantity `n * log n` is positive. -/
lemma pos_of_two_le (n : ℕ) (hn : 2 ≤ n) : (0:ℝ) < (n:ℝ) * Real.log n := by
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := by
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
    linarith [Real.log_two_gt_d9]
  positivity

/-- For `n ≥ 2`, `log n` is at most `sqrt (n * log n)`. -/
lemma ln_le_B (n : ℕ) (hn : 2 ≤ n) :
    Real.log n ≤ Real.sqrt ((n:ℝ) * Real.log n) := by
  have hprod : 0 < (n:ℝ) * Real.log n := pos_of_two_le n hn
  have hlogn : 0 ≤ Real.log n := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact Real.log_nonneg hn1
  rw [Real.le_sqrt hlogn hprod.le]
  have hln_le_n : Real.log n ≤ (n:ℝ) := by
    have hn1 : (0:ℝ) ≤ n := by positivity
    simpa using Real.log_le_self hn1
  nlinarith [hlogn, hln_le_n]

/-- For `n ≥ 2`, `sqrt (n * log n)` is at least one. -/
lemma B_ge_one (n : ℕ) (hn : 2 ≤ n) :
    (1:ℝ) ≤ Real.sqrt ((n:ℝ) * Real.log n) := by
  have hprod : 0 < (n:ℝ) * Real.log n := pos_of_two_le n hn
  rw [Real.le_sqrt (by norm_num) hprod.le]
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  norm_num
  nlinarith [Real.log_two_gt_d9, hn2, hlog]

/-- For `n ≥ 2`, the chosen block length plus four is at most `6 * sqrt (n * log n)`. -/
lemma l4_le_sixB (n : ℕ) (hn : 2 ≤ n) :
    (Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) + 4 ≤
      6 * Real.sqrt ((n:ℝ) * Real.log n) := by
  have hsqrt_le : Real.sqrt ((n:ℝ) * (Nat.log2 n + 1 : ℕ)) ≤
      2 * Real.sqrt ((n:ℝ) * Real.log n) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hb4 : (Nat.log2 n : ℝ) + 1 ≤ 4 * Real.log n := b_upper n hn
    have hB2 : (Real.sqrt ((n:ℝ) * Real.log n))^2 = (n:ℝ) * Real.log n :=
      Real.sq_sqrt (pos_of_two_le n hn).le
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    rw [mul_pow, hB2]
    have hb4R : ((Nat.log2 n + 1 : ℕ) : ℝ) ≤ 4 * Real.log n := by
      push_cast
      exact hb4
    nlinarith [hb4R, hn0]
  have hB1 := B_ge_one n hn
  have h1 := l_le_sqrt n hn
  linarith

/-- For `n ≥ 2`, the block count `(n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1`, cast to the
reals, is at most `4 * n / sqrt (n * log n)`. -/
lemma k_le (n : ℕ) (hn : 2 ≤ n) :
    (((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1 : ℕ) : ℝ) ≤
      4 * (n:ℝ) / Real.sqrt ((n:ℝ) * Real.log n) := by
  set l := Nat.sqrt (n * (Nat.log2 n + 1)) with hl
  set B := Real.sqrt ((n:ℝ) * Real.log n) with hB
  have hlpos : 0 < l := by
    rw [hl, Nat.sqrt_pos]
    have : 0 < n := by omega
    have : 0 < Nat.log2 n + 1 := by omega
    positivity
  have hlr : (0:ℝ) < (l:ℝ) := by exact_mod_cast hlpos
  have hBpos : 0 < B := Real.sqrt_pos.mpr (pos_of_two_le n hn)
  have hdiv : (((n - 1) / l : ℕ) : ℝ) ≤ ((n:ℝ) - 1) / (l:ℝ) := by
    have := Nat.cast_div_le (α := ℝ) (m := n - 1) (n := l)
    have hc : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hc] at this
    exact this
  have hmain : ((n:ℝ) - 1) / (l:ℝ) + 1 ≤ 2 * (n:ℝ) / (l:ℝ) := by
    have hp : ((n:ℝ) - 1) / (l:ℝ) + 1 = (((n:ℝ) - 1) + (l:ℝ)) / (l:ℝ) := by
      field_simp
    rw [hp]
    have hnum : ((n:ℝ) - 1) + (l:ℝ) ≤ 2 * (n:ℝ) := by
      have := l_le_n n hn
      linarith
    exact div_le_div_of_nonneg_right hnum hlr.le
  have hk2 : (((n - 1) / l + 1 : ℕ) : ℝ) ≤ 2 * (n:ℝ) / (l:ℝ) := by
    have h1 : (((n - 1) / l : ℕ) : ℝ) + 1 = (((n - 1) / l + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [← h1]
    linarith [hdiv, hmain]
  have hBle : B / 2 ≤ (l:ℝ) := by
    have h1 := sqrt_nb_ge_B n hn
    have h2 := l_ge_half n hn
    rw [hB]
    linarith
  have hstep : 2 * (n:ℝ) / (l:ℝ) ≤ 4 * (n:ℝ) / B := by
    have h1 : 2 * (n:ℝ) / (l:ℝ) ≤ 2 * (n:ℝ) / (B / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hBle
    have h2 : 2 * (n:ℝ) / (B / 2) = 4 * (n:ℝ) / B := by
      field_simp
      norm_num
    linarith [h1, h2.le, h2.ge]
  exact le_trans hk2 hstep

/-- For `n ≥ 2`, the chosen block count times the logarithm of the block length plus four is at
most `16 * sqrt (n * log n)`. -/
lemma k_log_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1 : ℕ) *
        Real.log ((Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) + 4) ≤
      16 * Real.sqrt ((n:ℝ) * Real.log n) := by
  set l := Nat.sqrt (n * (Nat.log2 n + 1)) with hl
  set B := Real.sqrt ((n:ℝ) * Real.log n) with hB
  have hBpos : 0 < B := Real.sqrt_pos.mpr (pos_of_two_le n hn)
  have hlogpos : 0 ≤ Real.log ((l:ℝ) + 4) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ (l:ℝ) := by positivity
    linarith
  have hk := k_le n hn
  have h1 : (((n - 1) / l + 1 : ℕ) : ℝ) * Real.log ((l:ℝ) + 4) ≤
      (4 * (n:ℝ) / B) * Real.log ((l:ℝ) + 4) :=
    mul_le_mul_of_nonneg_right hk hlogpos
  have h2 : (4 * (n:ℝ) / B) * Real.log ((l:ℝ) + 4) ≤
      (4 * (n:ℝ) / B) * (4 * Real.log n) :=
    mul_le_mul_of_nonneg_left (log_l4_le n hn) (by positivity)
  have hB2 : B^2 = (n:ℝ) * Real.log n := Real.sq_sqrt (pos_of_two_le n hn).le
  have h3 : (4 * (n:ℝ) / B) * (4 * Real.log n) = 16 * B := by
    field_simp
    nlinarith [hB2]
  linarith [h1, h2, h3.le, h3.ge]

/-- For `n ≥ 2`, the logarithm of the chosen block length plus four is at most `4 * sqrt (n *
log n)`. -/
lemma log_l4_le_B (n : ℕ) (hn : 2 ≤ n) :
    Real.log ((Nat.sqrt (n * (Nat.log2 n + 1)) : ℝ) + 4) ≤
      4 * Real.sqrt ((n:ℝ) * Real.log n) := by
  have h1 := log_l4_le n hn
  have h2 := ln_le_B n hn
  linarith

/-- For `n ≥ 2`, the explicit pipeline time expression for the chosen block length and block
count is at most `2 ^ (64 * sqrt (n * log n))`. See [Regev2004a]. -/
lemma time_bound (n : ℕ) (hn : 2 ≤ n) :
    (((Nat.sqrt (n * (Nat.log2 n + 1)) + 4) ^
        ((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1) *
      (2 ^ (Nat.sqrt (n * (Nat.log2 n + 1)) + 4) *
        (Nat.sqrt (n * (Nat.log2 n + 1)) + 4)) : ℕ) : ℝ) ≤
      Real.rpow 2 (64 * Real.sqrt ((n:ℝ) * Real.log n)) := by
  set l := Nat.sqrt (n * (Nat.log2 n + 1)) with hl
  set k := (n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1 with hk
  set B := Real.sqrt ((n:ℝ) * Real.log n) with hB
  have hBpos : 0 < B := Real.sqrt_pos.mpr (pos_of_two_le n hn)
  have hl0 : (0:ℝ) ≤ (l:ℝ) := by positivity
  have hLpos : (0:ℝ) < (l:ℝ) + 4 := by positivity
  have htime_pos : (0:ℝ) < (((l + 4) ^ k * (2 ^ (l + 4) * (l + 4)) : ℕ) : ℝ) := by
    have : 0 < (l + 4) ^ k := by positivity
    have : 0 < 2 ^ (l + 4) * (l + 4) := by positivity
    positivity
  have hcast : ((((l + 4) ^ k * (2 ^ (l + 4) * (l + 4)) : ℕ) : ℝ))
      = ((l:ℝ) + 4) ^ k * ((2:ℝ) ^ (l + 4) * ((l:ℝ) + 4)) := by
    push_cast
    ring
  have hlogeq : Real.log ((((l + 4) ^ k * (2 ^ (l + 4) * (l + 4)) : ℕ) : ℝ))
      = (k:ℝ) * Real.log ((l:ℝ) + 4) + ((l:ℝ) + 4) * Real.log 2 + Real.log ((l:ℝ) + 4) := by
    rw [hcast]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hklog : (k:ℝ) * Real.log ((l:ℝ) + 4) ≤ 16 * B := by
    simpa [hl, hk, hB] using k_log_bound n hn
  have hl4log : ((l:ℝ) + 4) * Real.log 2 ≤ 6 * B * Real.log 2 := by
    have hlog2 : 0 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h4 := l4_le_sixB n hn
    rw [← hl, ← hB] at h4
    exact mul_le_mul_of_nonneg_right h4 hlog2
  have hlog4 : Real.log ((l:ℝ) + 4) ≤ 4 * B := by
    simpa [hl, hB] using log_l4_le_B n hn
  have hlog2le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hconst : (20:ℝ) + 6 * Real.log 2 ≤ 64 * Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hsum : (k:ℝ) * Real.log ((l:ℝ) + 4) + ((l:ℝ) + 4) * Real.log 2 +
      Real.log ((l:ℝ) + 4) ≤ 64 * B * Real.log 2 := by
    have hsplit :
        (k:ℝ) * Real.log ((l:ℝ) + 4) + ((l:ℝ) + 4) * Real.log 2 +
          Real.log ((l:ℝ) + 4) ≤ 16 * B + 6 * B * Real.log 2 + 4 * B := by
      linarith [hklog, hl4log, hlog4]
    have hratio : 16 * B + 6 * B * Real.log 2 + 4 * B =
        B * (20 + 6 * Real.log 2) := by ring
    have hmono : B * (20 + 6 * Real.log 2) ≤ B * (64 * Real.log 2) :=
      mul_le_mul_of_nonneg_left hconst hBpos.le
    have hfin : B * (64 * Real.log 2) = 64 * B * Real.log 2 := by ring
    linarith [hsplit, hratio.le, hratio.ge, hmono, hfin.le, hfin.ge]
  have hle : Real.log ((((l + 4) ^ k * (2 ^ (l + 4) * (l + 4)) : ℕ) : ℝ))
      ≤ (64 * B) * Real.log 2 := by
    rw [hlogeq]
    exact hsum
  have hfinal := (Real.le_rpow_iff_log_le (x := ((((l + 4) ^ k * (2 ^ (l + 4) * (l + 4)) : ℕ) : ℝ)))
      (y := 2) (z := 64 * B) htime_pos (by norm_num)).mpr (by
        simpa [mul_comm] using hle)
  simpa [hl, hk, hB] using hfinal

/-- For `n ≥ 2`, the chosen natural square-root block length is at least two. -/
lemma sqrt_ge_two (n : ℕ) (hn : 2 ≤ n) : 2 ≤ Nat.sqrt (n * (Nat.log2 n + 1)) := by
  rw [Nat.le_sqrt]
  have hb2 : (2:ℕ) ≤ Nat.log2 n + 1 := by
    have h1 : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simpa using hn)
    omega
  exact Nat.mul_le_mul hn hb2

/-- For `n ≥ 2`, the chosen natural square-root block length is at most `n` as a natural-number
inequality. -/
lemma sqrt_le_n_nat (n : ℕ) (hn : 2 ≤ n) : Nat.sqrt (n * (Nat.log2 n + 1)) ≤ n := by
  exact_mod_cast l_le_n n hn

/-- For `n ≥ 2`, the chosen natural square-root block length is positive. -/
lemma sqrt_pos_two_le (n : ℕ) (hn : 2 ≤ n) : 0 < Nat.sqrt (n * (Nat.log2 n + 1)) := by
  have := sqrt_ge_two n hn
  omega

/-- For `n ≥ 2`, the chosen block count times the block length plus four is at most `(n + 1) ^
2`. See [Regev2004a]. -/
lemma space_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1) *
      (Nat.sqrt (n * (Nat.log2 n + 1)) + 4) ≤ (n + 1) ^ 2 := by
  set l := Nat.sqrt (n * (Nat.log2 n + 1)) with hl
  have hl2 : 2 ≤ l := by simpa [hl] using sqrt_ge_two n hn
  have hln : l ≤ n := by simpa [hl] using sqrt_le_n_nat n hn
  have hdiv : (n - 1) / l ≤ (n - 1) / 2 := Nat.div_le_div_left hl2 (by norm_num)
  have hkl : ((n - 1) / l + 1) * l ≤ (n - 1) + l := by
    have h := Nat.div_mul_le_self (n - 1) l
    rw [Nat.add_mul, one_mul]
    omega
  have hk4 : 4 * ((n - 1) / l + 1) ≤ 2 * n + 2 := by
    have hle : (n - 1) / l + 1 ≤ (n - 1) / 2 + 1 := by omega
    have h4 : 4 * ((n - 1) / l + 1) ≤ 4 * ((n - 1) / 2 + 1) := Nat.mul_le_mul_left 4 hle
    have hdm : 2 * ((n - 1) / 2) ≤ n - 1 := by
      have h0 := Nat.div_mul_le_self (n - 1) 2
      omega
    have hmid : 4 * ((n - 1) / 2 + 1) ≤ 2 * n + 2 := by omega
    omega
  have hkl4 : ((n - 1) / l + 1) * (l + 4) =
      ((n - 1) / l + 1) * l + 4 * ((n - 1) / l + 1) := by ring
  rw [hkl4]
  have hsum : ((n - 1) / l + 1) * l + 4 * ((n - 1) / l + 1) ≤ (n - 1) + l + (2 * n + 2) := by omega
  have hkey : 4 * n + 1 ≤ (n + 1) ^ 2 := by
    have hnZ : (2:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    have hfac : (0:ℤ) ≤ ((n:ℤ) - 2) * (n:ℤ) :=
      mul_nonneg (by omega) (by omega)
    have hZ : (4 * (n:ℤ) + 1) ≤ ((n:ℤ) + 1) ^ 2 := by nlinarith [hfac]
    exact_mod_cast hZ
  have hstep : n - 1 + l + (2 * n + 2) ≤ (n + 1) ^ 2 := by omega
  omega

/-- For `n ≥ 2`, one plus the product of the chosen block count and block length covers `n`. See
[Regev2004a]. -/
lemma covers_two_le (n : ℕ) (hn : 2 ≤ n) :
    n ≤ 1 + ((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1) *
      Nat.sqrt (n * (Nat.log2 n + 1)) := by
  set l := Nat.sqrt (n * (Nat.log2 n + 1)) with hl
  have hlpos : 0 < l := by
    rw [hl, Nat.sqrt_pos]
    have : 0 < n := by omega
    have : 0 < Nat.log2 n + 1 := by omega
    positivity
  have hkl : ((n - 1) / l + 1) * l = (n - 1) / l * l + l := by rw [Nat.add_mul, one_mul]
  set m := (n - 1) / l * l with hm
  set r := (n - 1) % l with hr
  have hdiv : l * ((n - 1) / l) + r = n - 1 := by
    rw [hr]; exact Nat.div_add_mod (n - 1) l
  have hmul : l * ((n - 1) / l) = m := by rw [hm]; ring
  have hmod : r < l := by rw [hr]; exact Nat.mod_lt _ hlpos
  rw [hkl]
  omega

/-- Constructs pipeline schedules satisfying the specified subexponential time and polynomial
space bounds, with uniform combination success probability at least one half for each
residue. See [Regev2004a]. -/
theorem dihedralHSPSubexponentialPolySpace :
    DihedralHSPSubexponentialPolySpace := by
  refine ⟨64, by norm_num, fun n hn => ?_⟩
  refine ⟨⟨n, Nat.sqrt (n * (Nat.log2 n + 1)),
      (n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1,
      covers_two_le n hn, sqrt_pos_two_le n hn, Nat.succ_pos _⟩, rfl, ?_, ?_, ?_⟩
  · exact time_bound n hn
  · show ((((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1) *
        (Nat.sqrt (n * (Nat.log2 n + 1)) + 4) * (n + 1) : ℕ) : ℝ) ≤
      polynomialSpaceEnvelope n
    have hsb := space_bound n hn
    have hle : ((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1) *
        (Nat.sqrt (n * (Nat.log2 n + 1)) + 4) * (n + 1) ≤ (n + 1) ^ 2 * (n + 1) :=
      Nat.mul_le_mul_right (n + 1) hsb
    have hcast : (((n + 1) ^ 2 * (n + 1) : ℕ) : ℝ) = polynomialSpaceEnvelope n := by
      simp [polynomialSpaceEnvelope]
      ring
    calc ((((n - 1) / Nat.sqrt (n * (Nat.log2 n + 1)) + 1) *
          (Nat.sqrt (n * (Nat.log2 n + 1)) + 4) * (n + 1) : ℕ) : ℝ)
        ≤ (((n + 1) ^ 2 * (n + 1) : ℕ) : ℝ) := by exact_mod_cast hle
      _ = polynomialSpaceEnvelope n := hcast
  · intro z
    exact combination_success_probability _ (sqrt_pos_two_le n hn) z

end Qatlib.Papers.DihedralHSP04.MainResults
