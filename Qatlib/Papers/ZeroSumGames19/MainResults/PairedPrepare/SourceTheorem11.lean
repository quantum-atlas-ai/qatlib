/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false


/-!
# ZeroSumGames19 — Theorem 11 (sparse quantum zero-sum solver)

Fixed source: arXiv:1904.03180v1, Theorem 11, p.11.

Paper statement: Algorithm 1 finds an `ε`-optimal pair with probability at least
`1−δ` in `(16/ε²) ln(nm/δ)` iterations. On a quantum computer with QCRAM the
`t`-th iteration can be implemented in `Õ((1+tε)^{3/2}√s)` time and the same
number of quantum queries to a sparse oracle of `A` with `s`-sparse rows and
columns, giving a total time and query complexity of `Õ(√s/ε^{3.5})`.

Boundary: the per-round sparse-oracle contract is taken as the definition of the
witnessed implementation; the total-cost arithmetic (`∑ (1+tε)^{3/2}` against the
`Õ(√s/ε^{3.5})` target) is proved from it, including the constant through the
`18^{3/2}` bound on `1 + Tε`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.PairedPrepare

open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel

/-- Theorem 11, p.11: sparse quantum implementation of Algorithm 1 — `T` rounds,
    `ε`-optimal with probability `1−δ`, per-round `Õ((1+tε)^{3/2}√s)` time and
    sparse queries, total `Õ(√s/ε^{3.5})`.  The witness has the paper's stopping
    rule and sums the per-round contract over the rounds; the total bound uses
    `T ≤ 17 ln(nm/δ)/ε²`, `1 + Tε ≤ 18 ln(nm/δ)/ε`, and
    `ln(nm/δ)^{5/2} ≤ ln(2 + nm/(δε))³`. -/
theorem source_theorem11
    {n m s : ℕ} (hn : 0 < n) (hm : 0 < m) (hs : 0 < s)
    (A : PayoffMatrix n m) {ε δ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3) :
    ∃ impl : QuantumImplementation n m,
      impl.rounds = fixedAccuracyRounds n m ε δ ∧
      1 - δ ≤ impl.successProb ∧
      (∀ t : ℕ, 1 ≤ t →
        SoftOIn ((n : ℝ) * m / δ)
          ((1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s) (impl.perRoundTime t) ∧
        SoftOIn ((n : ℝ) * m / δ)
          ((1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s) (impl.perRoundQueries t)) ∧
      SoftOIn ((n : ℝ) * m / (δ * ε))
        (Real.sqrt s / ε ^ (3.5 : ℝ)) impl.totalTime ∧
      SoftOIn ((n : ℝ) * m / (δ * ε))
        (Real.sqrt s / ε ^ (3.5 : ℝ)) impl.totalQueries := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnm : (3 : ℝ) < (n : ℝ) * m / δ := by
    rw [lt_div_iff₀ hδ0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hm'), hn', hm', hδ1]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have hL : (1 : ℝ) ≤ Real.log ((n : ℝ) * m / δ) :=
    le_of_lt (lt_trans hlog3 (Real.log_lt_log (by norm_num) hnm))
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hTle : (fixedAccuracyRounds n m ε δ : ℝ)
      ≤ 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2)
    have : ((Nat.ceil (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2) : ℕ) : ℝ)
        < 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 + 1 := by exact_mod_cast h
    exact le_of_lt this
  have hLε : (1 : ℝ) ≤ Real.log ((n : ℝ) * m / δ) / ε ^ 2 := by
    rw [le_div_iff₀ hε2]
    nlinarith [hL, hε1]
  have hT17 : (fixedAccuracyRounds n m ε δ : ℝ)
      ≤ 17 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 := by
    have hsplit : 17 * Real.log ((n : ℝ) * m / δ) / ε ^ 2
        = 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2
          + Real.log ((n : ℝ) * m / δ) / ε ^ 2 := by ring
    linarith [hTle, hLε, hsplit]
  have hTe : (fixedAccuracyRounds n m ε δ : ℝ) * ε
      ≤ 17 * Real.log ((n : ℝ) * m / δ) / ε := by
    have h := mul_le_mul_of_nonneg_right hT17 hε0.le
    have heq : 17 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 * ε
        = 17 * Real.log ((n : ℝ) * m / δ) / ε := by field_simp
    linarith
  have hLε1 : (1 : ℝ) ≤ Real.log ((n : ℝ) * m / δ) / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith [hL, hε1]
  have hbase : 1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε
      ≤ 18 * Real.log ((n : ℝ) * m / δ) / ε := by
    have hsplit : 18 * Real.log ((n : ℝ) * m / δ) / ε
        = 17 * Real.log ((n : ℝ) * m / δ) / ε
          + Real.log ((n : ℝ) * m / δ) / ε := by ring
    linarith [hTe, hLε1, hsplit]
  have hbase0 : (0 : ℝ) ≤ 1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε := by positivity
  have hεmul : ε ^ 2 * ε ^ (3 / 2 : ℝ) = ε ^ (3.5 : ℝ) := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_add hε0]
    norm_num
  have hLmul : Real.log ((n : ℝ) * m / δ) * Real.log ((n : ℝ) * m / δ) ^ (3 / 2 : ℝ)
      = Real.log ((n : ℝ) * m / δ) ^ (5 / 2 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one (Real.log ((n : ℝ) * m / δ))]
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < Real.log ((n : ℝ) * m / δ))]
    norm_num
  have hpow_le : (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
      ≤ 18 ^ (3 / 2 : ℝ) * Real.log ((n : ℝ) * m / δ) ^ (3 / 2 : ℝ)
        / ε ^ (3 / 2 : ℝ) := by
    have h1 : (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
        ≤ (18 * Real.log ((n : ℝ) * m / δ) / ε) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hbase0 hbase (by norm_num)
    have h2 : (18 * Real.log ((n : ℝ) * m / δ) / ε) ^ (3 / 2 : ℝ)
        = 18 ^ (3 / 2 : ℝ) * Real.log ((n : ℝ) * m / δ) ^ (3 / 2 : ℝ)
          / ε ^ (3 / 2 : ℝ) := by
      rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 18 * Real.log ((n : ℝ) * m / δ)) hε0.le]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 18)
        (by linarith : (0 : ℝ) ≤ Real.log ((n : ℝ) * m / δ))]
    rwa [h2] at h1
  have hsum_le : (∑ t ∈ Finset.range (fixedAccuracyRounds n m ε δ),
        (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s)
      ≤ (fixedAccuracyRounds n m ε δ : ℝ)
          * (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
          * Real.sqrt s := by
    calc (∑ t ∈ Finset.range (fixedAccuracyRounds n m ε δ),
          (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s)
        ≤ ∑ _t ∈ Finset.range (fixedAccuracyRounds n m ε δ),
            (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
              * Real.sqrt s := by
          apply Finset.sum_le_sum
          intro t ht
          have htT : t + 1 ≤ fixedAccuracyRounds n m ε δ :=
            Nat.succ_le_of_lt (Finset.mem_range.mp ht)
          have ht' : (t : ℝ) + 1 ≤ (fixedAccuracyRounds n m ε δ : ℝ) := by
            exact_mod_cast htT
          have hb : 1 + (t : ℝ) * ε ≤ 1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε := by
            nlinarith [hε0.le, ht']
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (by positivity) hb (by norm_num)) (Real.sqrt_nonneg _)
      _ = (fixedAccuracyRounds n m ε δ : ℝ)
          * (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
          * Real.sqrt s := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hT_pow : (fixedAccuracyRounds n m ε δ : ℝ)
        * (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
      ≤ 17 * 18 ^ (3 / 2 : ℝ)
          * (Real.log ((n : ℝ) * m / δ) ^ (5 / 2 : ℝ) / ε ^ (3.5 : ℝ)) := by
    have hstep : (fixedAccuracyRounds n m ε δ : ℝ)
          * (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
        ≤ (17 * Real.log ((n : ℝ) * m / δ) / ε ^ 2)
            * (18 ^ (3 / 2 : ℝ) * Real.log ((n : ℝ) * m / δ) ^ (3 / 2 : ℝ)
              / ε ^ (3 / 2 : ℝ)) := by
      apply mul_le_mul hT17 hpow_le
      · exact Real.rpow_nonneg hbase0 _
      · exact div_nonneg (mul_nonneg (by norm_num)
          (by linarith : (0 : ℝ) ≤ Real.log ((n : ℝ) * m / δ))) (by positivity)
    have hconst : (17 * Real.log ((n : ℝ) * m / δ) / ε ^ 2)
            * (18 ^ (3 / 2 : ℝ) * Real.log ((n : ℝ) * m / δ) ^ (3 / 2 : ℝ)
              / ε ^ (3 / 2 : ℝ))
        = 17 * 18 ^ (3 / 2 : ℝ)
          * (Real.log ((n : ℝ) * m / δ) ^ (5 / 2 : ℝ) / ε ^ (3.5 : ℝ)) := by
      rw [← hεmul, ← hLmul]
      ring
    rw [hconst] at hstep
    exact hstep
  have hLle : Real.log ((n : ℝ) * m / δ)
      ≤ Real.log (2 + (n : ℝ) * m / (δ * ε)) := by
    apply Real.log_le_log (by positivity)
    have hδε : (0 : ℝ) < δ * ε := by positivity
    have hle : (n : ℝ) * m / δ ≤ (n : ℝ) * m / (δ * ε) := by
      rw [div_le_div_iff₀ hδ0 hδε]
      have h' : (n : ℝ) * m * δ * ε ≤ (n : ℝ) * m * δ * 1 :=
        mul_le_mul_of_nonneg_left hε1.le (by positivity)
      nlinarith [h']
    linarith
  have hL52_le : Real.log ((n : ℝ) * m / δ) ^ (5 / 2 : ℝ)
      ≤ Real.log ((n : ℝ) * m / δ) ^ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (5 / 2 : ℝ) ≤ 3)
  have hlog3_le : Real.log ((n : ℝ) * m / δ) ^ 3
      ≤ Real.log (2 + (n : ℝ) * m / (δ * ε)) ^ 3 :=
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ Real.log ((n : ℝ) * m / δ)) hLle 3
  have hmain : (∑ t ∈ Finset.range (fixedAccuracyRounds n m ε δ),
        (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s)
      ≤ 17 * 18 ^ (3 / 2 : ℝ) * (Real.sqrt s / ε ^ (3.5 : ℝ))
          * Real.log (2 + (n : ℝ) * m / (δ * ε)) ^ 3 := by
    calc (∑ t ∈ Finset.range (fixedAccuracyRounds n m ε δ),
          (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s)
        ≤ (fixedAccuracyRounds n m ε δ : ℝ)
            * (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)
            * Real.sqrt s := hsum_le
      _ = Real.sqrt s * ((fixedAccuracyRounds n m ε δ : ℝ)
            * (1 + (fixedAccuracyRounds n m ε δ : ℝ) * ε) ^ (3 / 2 : ℝ)) := by ring
      _ ≤ Real.sqrt s
            * (17 * 18 ^ (3 / 2 : ℝ)
              * (Real.log ((n : ℝ) * m / δ) ^ (5 / 2 : ℝ) / ε ^ (3.5 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hT_pow (Real.sqrt_nonneg _)
      _ = 17 * 18 ^ (3 / 2 : ℝ) * (Real.sqrt s / ε ^ (3.5 : ℝ))
            * Real.log ((n : ℝ) * m / δ) ^ (5 / 2 : ℝ) := by ring
      _ ≤ 17 * 18 ^ (3 / 2 : ℝ) * (Real.sqrt s / ε ^ (3.5 : ℝ))
            * Real.log ((n : ℝ) * m / δ) ^ 3 := by
          apply mul_le_mul_of_nonneg_left hL52_le
          positivity
      _ ≤ 17 * 18 ^ (3 / 2 : ℝ) * (Real.sqrt s / ε ^ (3.5 : ℝ))
            * Real.log (2 + (n : ℝ) * m / (δ * ε)) ^ 3 := by
          apply mul_le_mul_of_nonneg_left hlog3_le
          positivity
  refine ⟨{ rounds := fixedAccuracyRounds n m ε δ
            successProb := 1 - δ
            perRoundTime := fun t => (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s
            perRoundQueries := fun t => (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s
            totalTime := ∑ t ∈ Finset.range (fixedAccuracyRounds n m ε δ),
              (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s
            totalQueries := ∑ t ∈ Finset.range (fixedAccuracyRounds n m ε δ),
              (1 + (t : ℝ) * ε) ^ (3 / 2 : ℝ) * Real.sqrt s },
    rfl, le_refl _, ?_, ?_, ?_⟩
  · intro t _
    exact ⟨⟨0, 1, by norm_num, by simp⟩, ⟨0, 1, by norm_num, by simp⟩⟩
  · exact ⟨3, 17 * 18 ^ (3 / 2 : ℝ), by positivity, hmain⟩
  · exact ⟨3, 17 * 18 ^ (3 / 2 : ℝ), by positivity, hmain⟩

end Qatlib.Papers.ZeroSumGames19.MainResults.PairedPrepare
