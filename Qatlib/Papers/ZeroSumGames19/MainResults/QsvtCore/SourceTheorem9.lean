/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false


/-!
# ZeroSumGames19 — Theorem 9 (dense quantum zero-sum solver)

Fixed source: arXiv:1904.03180v1, Theorem 9, p.9.

Paper statement: Algorithm 1 finds an `ε`-optimal pair with probability at least
`1−δ` in `(16/ε²) ln(nm/δ)` iterations. On a quantum computer with QCRAM the
`t`-th iteration can be implemented in `Õ((1+tε)√(n+m))` time and the same number
of quantum queries to the entries of `A`, for a total time and query complexity of
`Õ(√(n+m)/ε³)`.

Proof (p.9): Lemma 1 (iteration count and `ε`-optimality) combined with Lemma 8
(Gibbs sampling) at additive error `O(ε²δ/ln(nm/δ))`.

Boundary: cost contract only; the composition Lemma 1 + Lemma 8 is the paper's
argument and is not formalised beyond the two component statements. The round
count is tied to `fixedAccuracyRounds`, i.e. the Lemma 1 value.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.QsvtCore

open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel

/-! ## The total-cost arithmetic of `T` rounds -/

/-- Sum of the per-round cost factors `1 + t·ε` for `t = 1,…,T`:
    `Σ_{t=1}^{T} (1 + tε) = T + ε·T(T+1)/2`. -/
theorem sum_round_factors (T : ℕ) (ε : ℝ) :
    (∑ t ∈ Finset.range T, (1 + ((t : ℝ) + 1) * ε))
      = (T : ℝ) + ε * ((T : ℝ) * ((T : ℝ) + 1) / 2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Theorem 9, p.9 (total cost).**  With `T = ⌈16 ln(nm/δ)/ε²⌉` rounds and
    `L = ln(nm/δ)`, the summed dense per-round factor is at most
    `200·L²/ε³`: substituting `T ≤ 16L/ε² + 1` into `T + εT(T+1)/2` and
    comparing each term against `L²/ε³` (using `1 ≤ L`, `ε < 1`). -/
theorem total_cost_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {ε δ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3) :
    (fixedAccuracyRounds n m ε δ : ℝ)
        + ε * ((fixedAccuracyRounds n m ε δ : ℝ)
          * ((fixedAccuracyRounds n m ε δ : ℝ) + 1) / 2)
      ≤ 200 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnm : (3 : ℝ) < (n : ℝ) * m / δ := by
    rw [lt_div_iff₀ hδ0]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hm'), hn', hm', hδ1]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have hL : (1 : ℝ) ≤ Real.log ((n : ℝ) * m / δ) :=
    le_of_lt (lt_trans hlog3 (Real.log_lt_log (by norm_num) (by linarith : (3 : ℝ) < (n : ℝ) * m / δ)))
  have hTle : (fixedAccuracyRounds n m ε δ : ℝ)
      ≤ 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2)
    have : ((Nat.ceil (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2) : ℕ) : ℝ)
        < 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1 := by exact_mod_cast h
    exact le_of_lt this
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hε3 : (0 : ℝ) < ε ^ 3 := by positivity
  have hL2 : (1 : ℝ) ≤ (Real.log ((n : ℝ) * m / δ)) ^ 2 := by nlinarith
  have hTnn : (0 : ℝ) ≤ (fixedAccuracyRounds n m ε δ : ℝ) := by positivity
  have hXnn : (0 : ℝ) ≤ 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1 := by positivity
  have hquad : (fixedAccuracyRounds n m ε δ : ℝ)
        + ε * ((fixedAccuracyRounds n m ε δ : ℝ)
          * ((fixedAccuracyRounds n m ε δ : ℝ) + 1) / 2)
      ≤ (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
        + ε * ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
          * ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1) + 1) / 2) := by
    have hprod : (0 : ℝ) ≤ ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
        - (fixedAccuracyRounds n m ε δ : ℝ)) := by linarith
    nlinarith [hTle, hTnn, hXnn, hε0, mul_nonneg hprod (by positivity :
      (0 : ℝ) ≤ 1 + ε * ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
        + (fixedAccuracyRounds n m ε δ : ℝ) + 1) / 2)]
  have hexpand : (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
        + ε * ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
          * ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1) + 1) / 2)
      = 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1
        + 128 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3
        + 24 * Real.log ((n : ℝ) * m / δ) / ε + ε := by
    field_simp
    ring
  have h1 : 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2
      ≤ 16 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 := by
    rw [div_le_div_iff₀ hε2 hε3]
    have hprod : (0 : ℝ) ≤ Real.log ((n : ℝ) * m / δ)
        * (Real.log ((n : ℝ) * m / δ) - ε) :=
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL) (sub_nonneg.mpr (le_trans hε1.le hL))
    nlinarith [hprod, hε0.le]
  have h2 : 24 * Real.log ((n : ℝ) * m / δ) / ε
      ≤ 24 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 := by
    rw [div_le_div_iff₀ hε0 hε3]
    have hprod : (0 : ℝ) ≤ Real.log ((n : ℝ) * m / δ)
        * (Real.log ((n : ℝ) * m / δ) - ε ^ 2) :=
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL)
        (sub_nonneg.mpr (le_trans (by nlinarith [hε1, hε0] : ε ^ 2 ≤ 1) hL))
    nlinarith [hprod, hε0.le]
  have h3 : (1 : ℝ) ≤ (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 := by
    rw [le_div_iff₀ hε3]
    nlinarith [hL2, hε1]
  have h4 : ε ≤ (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 := by
    rw [le_div_iff₀ hε3]
    nlinarith [hL2, hε0.le, hε1]
  have hsum : 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1
        + 128 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3
        + 24 * Real.log ((n : ℝ) * m / δ) / ε + ε
      ≤ 200 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 := by
    have hp1 : 16 * Real.log ((n : ℝ) * m / δ) * ε
        ≤ 16 * (Real.log ((n : ℝ) * m / δ)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h1 (le_of_lt hε3)
      field_simp at h
      nlinarith [mul_le_mul_of_nonneg_left h
        (by linarith : (0 : ℝ) ≤ 16 * Real.log ((n : ℝ) * m / δ))]
    have hp2 : 24 * Real.log ((n : ℝ) * m / δ) * ε ^ 2
        ≤ 24 * (Real.log ((n : ℝ) * m / δ)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h2 (le_of_lt hε3)
      field_simp at h
      nlinarith [mul_le_mul_of_nonneg_left h
        (by linarith : (0 : ℝ) ≤ 24 * Real.log ((n : ℝ) * m / δ))]
    have hp3 : ε ^ 3 ≤ (Real.log ((n : ℝ) * m / δ)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h3 (le_of_lt hε3)
      field_simp at h
      linarith
    have hp4 : ε ^ 4 ≤ (Real.log ((n : ℝ) * m / δ)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h4 (le_of_lt hε3)
      field_simp at h
      linarith
    have hgoal : 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1
          + 128 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3
          + 24 * Real.log ((n : ℝ) * m / δ) / ε + ε
        = (16 * Real.log ((n : ℝ) * m / δ) * ε + ε ^ 3
            + 128 * (Real.log ((n : ℝ) * m / δ)) ^ 2
            + 24 * Real.log ((n : ℝ) * m / δ) * ε ^ 2 + ε ^ 4) / ε ^ 3 := by
      field_simp
    rw [hgoal, div_le_iff₀ hε3]
    have hR : 200 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 * ε ^ 3
        = 200 * (Real.log ((n : ℝ) * m / δ)) ^ 2 := by field_simp
    rw [hR]
    linarith [hp1, hp2, hp3, hp4]
  have hsum' : (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
        + ε * ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1)
          * ((16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1) + 1) / 2)
      ≤ 200 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3 := by
    rw [hexpand]
    exact hsum
  linarith [hquad, hsum']

/-- **Theorem 9, p.9 (cost contract composition).**  Given any implementation
    whose per-round time obeys the dense Lemma-8 contract `C₀·(1+tε)·√(n+m)`,
    the total time over the paper's `T = ⌈16 ln(nm/δ)/ε²⌉` rounds is
    `Õ(√(n+m)/ε³)`.  The Algorithm-1 correctness certificate is
    `source_lemma1_fixed_accuracy`; the per-round contract itself is Lemma
    8's content and enters here as the explicit hypothesis `hper`. -/
theorem source_theorem9_cost
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : PayoffMatrix n m) {ε δ C₀ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3) (hC₀ : 0 < C₀)
    (impl : QuantumImplementation n m)
    (hrounds : impl.rounds = fixedAccuracyRounds n m ε δ)
    (htime : impl.totalTime
      = ∑ t ∈ Finset.range impl.rounds,
          C₀ * (1 + ((t : ℝ) + 1) * ε) * Real.sqrt ((n : ℝ) + m)) :
    SoftOIn ((n : ℝ) * m / (δ * ε)) (Real.sqrt ((n : ℝ) + m) / ε ^ 3)
      impl.totalTime := by
  refine ⟨2, 200 * C₀, by positivity, ?_⟩
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have hL : (1 : ℝ) ≤ Real.log ((n : ℝ) * m / δ) := by
    have hnm : (3 : ℝ) < (n : ℝ) * m / δ := by
      rw [lt_div_iff₀ hδ0]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hm'), hn', hm', hδ1]
    exact le_of_lt (lt_trans hlog3 (Real.log_lt_log (by norm_num) hnm))
  have hcost := total_cost_bound hn hm hε0 hε1 hδ0 hδ1
  have hsq : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + m) := Real.sqrt_nonneg _
  have hsum_eq : (∑ t ∈ Finset.range impl.rounds,
        C₀ * (1 + ((t : ℝ) + 1) * ε) * Real.sqrt ((n : ℝ) + m))
      = C₀ * Real.sqrt ((n : ℝ) + m)
        * ∑ t ∈ Finset.range impl.rounds, (1 + ((t : ℝ) + 1) * ε) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [htime, hsum_eq, hrounds, sum_round_factors]
  calc C₀ * Real.sqrt ((n : ℝ) + m)
        * ((fixedAccuracyRounds n m ε δ : ℝ)
          + ε * ((fixedAccuracyRounds n m ε δ : ℝ)
            * ((fixedAccuracyRounds n m ε δ : ℝ) + 1) / 2))
      ≤ C₀ * Real.sqrt ((n : ℝ) + m)
          * (200 * (Real.log ((n : ℝ) * m / δ)) ^ 2 / ε ^ 3) := by
        gcongr
    _ = 200 * C₀ * (Real.sqrt ((n : ℝ) + m) / ε ^ 3)
          * (Real.log ((n : ℝ) * m / δ)) ^ 2 := by ring
    _ ≤ 200 * C₀ * (Real.sqrt ((n : ℝ) + m) / ε ^ 3)
          * (Real.log (2 + (n : ℝ) * m / (δ * ε))) ^ 2 := by
        gcongr
        have hδε : (0 : ℝ) < δ * ε := by positivity
        have hle : (n : ℝ) * m / δ ≤ (n : ℝ) * m / (δ * ε) := by
          rw [div_le_div_iff₀ hδ0 hδε]
          have h' : (n : ℝ) * m * δ * ε ≤ (n : ℝ) * m * δ * 1 :=
            mul_le_mul_of_nonneg_left hε1.le (by positivity)
          nlinarith [h']
        linarith

end Qatlib.Papers.ZeroSumGames19.MainResults.QsvtCore
