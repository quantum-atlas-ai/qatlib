/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearchRefined
import Qatlib.Papers.OrderedList07.MainResults.Theorem11
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Multiway Bayesian updates for ordered search

Establishes normalization and nonnegativity facts for cyclic likelihoods and generalized
Bayesian updates in the ordered-search model of [BenOrHassidim2007]. Further lemmas specialize
the information expression to binary noise and control the prior threshold and stage-count
parameters.

## Main statements

* `generalizedUpdate_sum_one`: normalizes the posterior when its denominator is nonzero.
* `source_theorem2_10_stage_count`: bounds the stage count at the chosen multiway threshold.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open scoped BigOperators

namespace Qatlib.Papers.OrderedList07.MainResults

/-- Cyclically shifting a likelihood vector preserves its sum of one [BenOrHassidim2007]. -/
lemma cyclicLikelihood_sum_one {k : ℕ} (p : Fin (k + 1) → ℝ) (iv : Fin (k + 1))
    (hs : (∑ h, p h) = 1) :
    (∑ h, cyclicLikelihood p iv h) = 1 := by
  calc
    (∑ h, cyclicLikelihood p iv h) = ∑ h, p (h - iv) := rfl
    _ = ∑ h, p h := (Equiv.subRight iv).sum_comp p
    _ = 1 := hs

/-- Nonnegative prior weights and cyclic likelihoods give a pointwise nonnegative generalized
update [BenOrHassidim2007]. -/
lemma generalizedUpdate_nonneg {k n : ℕ} (p : Fin (k + 1) → ℝ) (cuts : Fin k → Fin n)
    (a : Fin n → ℝ) (h : Fin (k + 1)) (ha : ∀ m, 0 ≤ a m)
    (hl : ∀ m, 0 ≤ cyclicLikelihood p (intervalOf cuts m) h) :
    ∀ m, 0 ≤ generalizedUpdate p cuts a h m := by
  intro m
  unfold generalizedUpdate
  exact div_nonneg (mul_nonneg (ha m) (hl m))
    (Finset.sum_nonneg fun m' _ => mul_nonneg (ha m') (hl m'))

/-- The generalized update sums to one when its normalizing denominator is nonzero
[BenOrHassidim2007]. -/
lemma generalizedUpdate_sum_one {k n : ℕ} (p : Fin (k + 1) → ℝ) (cuts : Fin k → Fin n)
    (a : Fin n → ℝ) (h : Fin (k + 1))
    (hS : (∑ m, a m * cyclicLikelihood p (intervalOf cuts m) h) ≠ 0) :
    (∑ m, generalizedUpdate p cuts a h m) = 1 := by
  unfold generalizedUpdate
  rw [← Finset.sum_div]
  exact div_self hS

/-- The interval index determined by the cuts is monotone in the queried position
[BenOrHassidim2007]. -/
lemma intervalOf_mono {k n : ℕ} (cuts : Fin k → Fin n) {m m' : Fin n} (h : m ≤ m') :
    intervalOf cuts m ≤ intervalOf cuts m' := by
  unfold intervalOf
  simp only [Fin.le_def]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact le_trans hi h

/-- For the binary likelihood vector `(p, 1 − p)`, multiway information equals `queryInfo p`
[BenOrHassidim2007]. -/
lemma source_theorem2_10_binary_reduction (p : ℝ) :
    multiInfo (fun h : Fin 2 => if h.val = 0 then p else 1 - p) = queryInfo p :=
  multiInfo_bin_pair p

/-- If a normalized prior on a nonempty `Fin n` is strictly below `ε` at every point, then `1 <
n * ε`. -/
lemma prior_lt_threshold_forces (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (ε : ℝ)
    (hsum : (∑ m, a m) = 1) (hcap : ∀ m, a m < ε) :
    1 < (n : ℝ) * ε := by
  have hlt : (∑ m, a m) < ∑ _m : Fin n, ε := by
    refine Finset.sum_lt_sum (fun m _ => (hcap m).le) ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
    exact hcap ⟨0, hn⟩
  rw [hsum, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hlt
  exact hlt

/-- For positive `n ≤ k` and `L ≥ 4`, the product of `n` with the chosen prior threshold is at
most one [BenOrHassidim2007]. -/
lemma source_theorem2_10_param_infeasible (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hkn : (n : ℝ) ≤ (k : ℝ)) (L : ℝ) (hL : 4 ≤ L) :
    (n : ℝ) * ((1 / (k : ℝ)) * Real.sqrt (1 / (24 * L))) ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h24 : (0 : ℝ) < 24 * L := by positivity
  have hsqrt : Real.sqrt (1 / (24 * L)) ≤ 1 := by
    rw [Real.sqrt_le_one, div_le_one h24]
    linarith
  have hεle : (1 / (k : ℝ)) * Real.sqrt (1 / (24 * L)) ≤ 1 / (k : ℝ) :=
    mul_le_of_le_one_right (by positivity) hsqrt
  have hnk : (n : ℝ) * (1 / (k : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hkpos]
    exact hkn
  calc
    (n : ℝ) * ((1 / (k : ℝ)) * Real.sqrt (1 / (24 * L)))
        ≤ (n : ℝ) * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_left hεle hnpos.le
    _ ≤ 1 := hnk

/-- For positive `k`, `I > 0`, and the stated lower bounds on `L`, the stage count at threshold
`(1 / k) * √(1 / (24 * L))` is at most `L / I + 2 / (3 * I)` [BenOrHassidim2007]. -/
lemma source_theorem2_10_stage_count (k : ℕ) (hk : 0 < k) (L I : ℝ)
    (hL : 2 / 3 ≤ L) (hL4 : 4 ≤ L) (hI : 0 < I) :
    (L - Real.log (1 / ((1 / (k : ℝ)) * Real.sqrt (1 / (24 * L)))) / Real.log 2)
        / (I * (1 - 1 / (3 * L))) ≤ L / I + 2 / (3 * I) := by
  have hnpos : (0 : ℝ) < 24 * L := by positivity
  have hsqrt1 : Real.sqrt (1 / (24 * L)) ≤ 1 := by
    rw [Real.sqrt_le_one, div_le_one hnpos]
    linarith
  have hε0 : 0 < (1 / (k : ℝ)) * Real.sqrt (1 / (24 * L)) := by positivity
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hone : (1 : ℝ) / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkpos]
    exact hk1
  have hε1 : (1 / (k : ℝ)) * Real.sqrt (1 / (24 * L)) ≤ 1 := by
    calc
      (1 / (k : ℝ)) * Real.sqrt (1 / (24 * L)) ≤ 1 * 1 :=
        mul_le_mul hone hsqrt1 (Real.sqrt_nonneg _) (by norm_num)
      _ = 1 := by ring
  exact stage_count_entropy_gap L I _ hL hI hε0 hε1

end Qatlib.Papers.OrderedList07.MainResults
