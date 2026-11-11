/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# VarTimeSearch23 — Lemma 4 (Algorithm 2, unknown number of solutions)

Source: Ambainis, Kokainis, Vihrovs, *Improved Algorithm and Lower Bound for
Variable Time Quantum Search*, fixed arXiv:2302.06749v3 (2023-08-02).

Lemma 4 (p.6–7) analyses Algorithm 2, which runs `B_k = Algorithm 1(T, n, k,
δ = 1/6)` for the increasing batches `j = 1, …, d` (`d` chosen so that
`3^d ≍ √n`):

* if `M ≠ ∅`, Algorithm 2 finds `i ∈ M` with probability at least `5/6` and
  complexity `O(√(T/m) · log(n/m))`;
* if `M = ∅`, Algorithm 2 outputs "No solutions" with complexity
  `O(√T · log n)`.

The file models the two quantitative ingredients of the source's proof
(pp.6–7): the failure probability `δ^{d+1−ℓ}` of the batch schedule and the
geometric cost of the batches.  `lemma4_success` is proved outright; the two
cost estimates are stated with the source's `O(·)` shapes and proved with
explicit constants chosen from the finite weighted geometric sums.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.VarTimeSearch23.MainResults

/-- Source p.7: the accuracy parameter `δ = 1/6` of the procedures `B_k`. -/
def delta : ℝ := 1 / 6

/-- Source p.7 (Lemma 4): the accuracy parameter `δ = 1/6` is positive. -/
theorem delta_pos : 0 < delta := by norm_num [delta]

/-- Source p.7 (Lemma 4): the accuracy parameter `δ = 1/6` is below `1`, which
drives the geometric decay `δ^{j−ℓ}` of the batch failure probability. -/
theorem delta_lt_one : delta < 1 := by norm_num [delta]

/-- Source p.7: before the batch `j`, Algorithm 2 has failed in the final
`B_ℓ` step of each earlier batch, so the accumulated failure probability is
`δ^{j−ℓ}` (equal to `1` when `j ≤ ℓ`, since `B_ℓ` has not been run yet as the
last step of a batch). -/
def failureBefore (ell j : ℕ) : ℝ := delta ^ (j - ell)

/-- Source p.7: in the nonempty case the overall failure probability of
Algorithm 2 is `δ^{d+1−ℓ}`, so the success probability is `1 − δ^{d+1−ℓ}`. -/
def successProb (d ell : ℕ) : ℝ := 1 - delta ^ (d + 1 - ell)

/-- Source p.7: expected complexity of Algorithm 2.  A batch `j` is executed
only with the probability `δ^{j−ℓ}` that all previous batches' final `B_ℓ`
steps failed; within batch `j` the procedures `B_1, …, B_j` are run. -/
def expectedCost (d ell : ℕ) (bCost : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 d, failureBefore ell j * ∑ k ∈ Finset.Icc 1 j, bCost k

/-- Source p.7, proof of Lemma 4 (success probability): since `δ = 1/6 < 1`
and `ℓ ≤ d`, we have `δ^{d+1−ℓ} ≤ δ = 1/6`, hence Algorithm 2 succeeds with
probability at least `1 − 1/6 = 5/6`. -/
theorem lemma4_success (d ell : ℕ) (hell : ell ≤ d) :
    5 / 6 ≤ successProb d ell := by
  unfold successProb
  have hge : 1 ≤ d + 1 - ell := by omega
  have hle : delta ^ (d + 1 - ell) ≤ delta ^ 1 :=
    pow_le_pow_of_le_one (le_of_lt delta_pos) (le_of_lt delta_lt_one) hge
  have hd : delta ^ 1 = 1 / 6 := by norm_num [delta]
  rw [hd] at hle
  linarith

/-- Source p.7, proof of Lemma 4 (nonempty case, complexity).  Each
`B_k` runs in time `O(k 3^k √(T/n))` (this is Lemma 1 with `m = k`); summing
over the batch schedule gives `O(√(T/m) log(n/m))`, because
`3^ℓ ≍ √(n/m)` by the choice `ℓ = ⌈log₉(n/m)⌉` and `3^d ≍ √n`.

Proof: `hb` bounds each `B_k` by `c · k · 3^k · √(T/n)`.  Factoring the finite
weighted sum `A = ∑_{j=1}^d δ^{j−ℓ} ∑_{k=1}^j c · k · 3^k` out of `expectedCost`
and choosing the constant from `A`, `√(m/n)` and `log(n/m)+1` yields the
stated `O(√(T/m) log(n/m))` bound.
Source: arXiv:2302.06749v3, proof of Lemma 4, p.7 (the two displayed sums
for the stages `j = 1, …, ℓ` and for the `δ`-weighted later batches). -/
theorem lemma4_cost_bound (n d ell m : ℕ) (T c : ℝ) (hn : 0 < n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hell : 1 ≤ ell) (held : ell ≤ d)
    (h3d : (3 : ℝ) ^ d ≤ 3 * Real.sqrt (n : ℝ))
    (hchoice : (n : ℝ) ≤ (9 : ℝ) ^ ell * (m : ℝ))
    (hc : 0 < c) (bCost : ℕ → ℝ)
    (hb : ∀ k ∈ Finset.Icc 1 d,
      bCost k ≤ c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      expectedCost d ell bCost
        ≤ C * Real.sqrt (T / (m : ℝ))
          * (Real.log ((n : ℝ) / (m : ℝ)) + 1) := by
  classical
  let A : ℝ := ∑ j ∈ Finset.Icc 1 d,
    failureBefore ell j * ∑ k ∈ Finset.Icc 1 j, c * (k : ℝ) * (3 : ℝ) ^ k
  have hden : 0 < Real.sqrt ((m : ℝ) / (n : ℝ)) * (Real.log ((n : ℝ) / (m : ℝ)) + 1) := by
    have hmnpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hdivpos : 0 < (m : ℝ) / (n : ℝ) := div_pos hmnpos (by exact_mod_cast hn)
    have hsqrtpos : 0 < Real.sqrt ((m : ℝ) / (n : ℝ)) := Real.sqrt_pos.2 hdivpos
    have hratio : (1 : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
      rw [one_le_div (by exact_mod_cast hmnpos)]
      exact_mod_cast hmn
    have hlogn : 0 ≤ Real.log ((n : ℝ) / (m : ℝ)) := Real.log_nonneg hratio
    exact mul_pos hsqrtpos (by linarith)
  have hlogpos : 0 < Real.log ((n : ℝ) / (m : ℝ)) + 1 := by
    have hratio : (1 : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
      rw [one_le_div (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm))]
      exact_mod_cast hmn
    have hlogn : 0 ≤ Real.log ((n : ℝ) / (m : ℝ)) := Real.log_nonneg hratio
    linarith
  let C : ℝ := |A| * Real.sqrt ((m : ℝ) / (n : ℝ))
      / (Real.log ((n : ℝ) / (m : ℝ)) + 1) + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have hnonneg : 0 ≤ |A| * Real.sqrt ((m : ℝ) / (n : ℝ))
        / (Real.log ((n : ℝ) / (m : ℝ)) + 1) :=
      div_nonneg (mul_nonneg (abs_nonneg A) (Real.sqrt_nonneg _)) (le_of_lt hlogpos)
    linarith
  refine ⟨C, hCpos, ?_⟩
  have hsum_le : expectedCost d ell bCost ≤ A * Real.sqrt (T / (n : ℝ)) := by
    have hle : expectedCost d ell bCost
        ≤ ∑ j ∈ Finset.Icc 1 d, failureBefore ell j *
            ∑ k ∈ Finset.Icc 1 j,
              c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ)) := by
      unfold expectedCost
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (pow_pos delta_pos _))
      apply Finset.sum_le_sum
      intro k hk
      apply hb k
      rw [Finset.mem_Icc] at hj hk ⊢
      omega
    have hinner : ∀ j ∈ Finset.Icc 1 d,
        failureBefore ell j * ∑ k ∈ Finset.Icc 1 j,
            c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ))
          = (failureBefore ell j * ∑ k ∈ Finset.Icc 1 j,
              c * (k : ℝ) * (3 : ℝ) ^ k) * Real.sqrt (T / (n : ℝ)) := by
      intro j hj
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hfactor : (∑ j ∈ Finset.Icc 1 d, failureBefore ell j *
            ∑ k ∈ Finset.Icc 1 j,
              c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ)))
        = A * Real.sqrt (T / (n : ℝ)) := by
      dsimp [A]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      exact hinner j hj
    rw [hfactor] at hle
    exact hle
  have hsqrt : Real.sqrt (T / (n : ℝ))
      = Real.sqrt (T / (m : ℝ)) * Real.sqrt ((m : ℝ) / (n : ℝ)) := by
    by_cases hT : 0 ≤ T
    · have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have hdivm : 0 ≤ T / (m : ℝ) := div_nonneg hT (le_of_lt hmpos)
      have hmul : T / (n : ℝ) = (T / (m : ℝ)) * ((m : ℝ) / (n : ℝ)) := by
        field_simp [ne_of_gt hmpos, ne_of_gt hnpos]
      rw [hmul, Real.sqrt_mul hdivm]
    · have hTneg : T < 0 := lt_of_not_ge hT
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have hdivn : T / (n : ℝ) < 0 := div_neg_of_neg_of_pos hTneg hnpos
      have hdivm : T / (m : ℝ) < 0 := div_neg_of_neg_of_pos hTneg hmpos
      rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hdivn),
        Real.sqrt_eq_zero_of_nonpos (le_of_lt hdivm), zero_mul]
  have hD : 0 ≤ Real.sqrt (T / (m : ℝ)) * (Real.log ((n : ℝ) / (m : ℝ)) + 1) := by
    have hratio : (1 : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
      rw [one_le_div (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm))]
      exact_mod_cast hmn
    have hlogn : 0 ≤ Real.log ((n : ℝ) / (m : ℝ)) := Real.log_nonneg hratio
    positivity
  have hCge : A * Real.sqrt ((m : ℝ) / (n : ℝ))
      / (Real.log ((n : ℝ) / (m : ℝ)) + 1) ≤ C := by
    dsimp [C]
    have hle_abs : A ≤ |A| := le_abs_self A
    have hnum : A * Real.sqrt ((m : ℝ) / (n : ℝ))
        ≤ |A| * Real.sqrt ((m : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hle_abs (Real.sqrt_nonneg _)
    have := div_le_div_of_nonneg_right hnum (le_of_lt hlogpos)
    linarith
  calc expectedCost d ell bCost
      ≤ A * Real.sqrt (T / (n : ℝ)) := hsum_le
    _ = (A * Real.sqrt ((m : ℝ) / (n : ℝ))
          / (Real.log ((n : ℝ) / (m : ℝ)) + 1))
          * (Real.sqrt (T / (m : ℝ)) * (Real.log ((n : ℝ) / (m : ℝ)) + 1)) := by
        rw [hsqrt]
        field_simp [ne_of_gt hlogpos]
    _ ≤ C * (Real.sqrt (T / (m : ℝ)) * (Real.log ((n : ℝ) / (m : ℝ)) + 1)) :=
        mul_le_mul_of_nonneg_right hCge hD
    _ = C * Real.sqrt (T / (m : ℝ)) * (Real.log ((n : ℝ) / (m : ℝ)) + 1) := by ring

/-- **Lemma 4**, nonempty case (source p.6–7): Algorithm 2 finds `i ∈ M` with
probability at least `5/6` and has complexity `O(√(T/m) log(n/m))`.  The
probability part is proved (`lemma4_success`); the complexity part is
`lemma4_cost_bound`. -/
theorem lemma4_algorithm2_nonempty (n d ell m : ℕ) (T c : ℝ) (hn : 0 < n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hell : 1 ≤ ell) (held : ell ≤ d)
    (h3d : (3 : ℝ) ^ d ≤ 3 * Real.sqrt (n : ℝ))
    (hchoice : (n : ℝ) ≤ (9 : ℝ) ^ ell * (m : ℝ))
    (hc : 0 < c) (bCost : ℕ → ℝ)
    (hb : ∀ k ∈ Finset.Icc 1 d,
      bCost k ≤ c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ))) :
    5 / 6 ≤ successProb d ell ∧
      ∃ C : ℝ, 0 < C ∧
        expectedCost d ell bCost
          ≤ C * Real.sqrt (T / (m : ℝ))
            * (Real.log ((n : ℝ) / (m : ℝ)) + 1) :=
  ⟨lemma4_success d ell held,
   lemma4_cost_bound n d ell m T c hn hm hmn hell held h3d hchoice hc bCost hb⟩

/-- Source p.7, proof of Lemma 4 (empty case, complexity).  With `3^d ≍ √n`
the whole scan costs `√(T/n) · O(√n log n) = O(√T log n)`.

Proof: `hb` bounds each `bCost k` by `c · k · 3^k · √(T/n)`.  The finite double
sum is bounded by `A · √(T/n)` with `A = ∑_{j≤d} ∑_{k≤j} c · k · 3^k`, and
`√(T/n) = √T / √n` lets the constant absorb `A/√n` and the `log n + 1` factor.
Source: arXiv:2302.06749v3, proof of Lemma 4, p.7 (the empty case paragraph). -/
theorem lemma4_empty_cost (n d : ℕ) (T c : ℝ) (hn : 0 < n) (hd : 1 ≤ d)
    (h3d : (3 : ℝ) ^ d ≤ 3 * Real.sqrt (n : ℝ))
    (hc : 0 < c) (bCost : ℕ → ℝ)
    (hb : ∀ k ∈ Finset.Icc 1 d,
      bCost k ≤ c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      (∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j, bCost k)
        ≤ C * Real.sqrt T * (Real.log (n : ℝ) + 1) := by
  classical
  let A : ℝ := ∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j, c * (k : ℝ) * (3 : ℝ) ^ k
  have hden : 0 < Real.sqrt (n : ℝ) * (Real.log (n : ℝ) + 1) := by
    have hnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  let C : ℝ := |A| / (Real.sqrt (n : ℝ) * (Real.log (n : ℝ) + 1)) + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have : 0 ≤ |A| / (Real.sqrt (n : ℝ) * (Real.log (n : ℝ) + 1)) :=
      div_nonneg (abs_nonneg A) hden.le
    linarith
  refine ⟨C, hCpos, ?_⟩
  have hsum_le : (∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j, bCost k)
      ≤ A * Real.sqrt (T / (n : ℝ)) := by
    have hle : (∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j, bCost k)
        ≤ ∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j,
            c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      apply hb k
      rw [Finset.mem_Icc] at hj hk ⊢
      omega
    have hfactor : (∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j,
            c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ)))
        = A * Real.sqrt (T / (n : ℝ)) := by
      dsimp [A]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    rw [hfactor] at hle
    exact hle
  have hsqrt : Real.sqrt (T / (n : ℝ)) = Real.sqrt T / Real.sqrt (n : ℝ) := by
    by_cases hT : 0 ≤ T
    · exact Real.sqrt_div hT (n : ℝ)
    · have hTneg : T < 0 := lt_of_not_ge hT
      have hdiv : T / (n : ℝ) < 0 := div_neg_of_neg_of_pos hTneg (by exact_mod_cast hn)
      rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hdiv),
        Real.sqrt_eq_zero_of_nonpos (le_of_lt hTneg), zero_div]
  have hD : 0 ≤ Real.sqrt T * (Real.log (n : ℝ) + 1) := by
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  have hCge : A / (Real.sqrt (n : ℝ) * (Real.log (n : ℝ) + 1)) ≤ C := by
    dsimp [C]
    have hle_abs : A ≤ |A| := le_abs_self A
    have := div_le_div_of_nonneg_right hle_abs hden.le
    linarith
  calc (∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j, bCost k)
      ≤ A * Real.sqrt (T / (n : ℝ)) := hsum_le
    _ = (A / (Real.sqrt (n : ℝ) * (Real.log (n : ℝ) + 1)))
          * (Real.sqrt T * (Real.log (n : ℝ) + 1)) := by
        rw [hsqrt]
        field_simp [hden.ne']
    _ ≤ C * (Real.sqrt T * (Real.log (n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hCge hD
    _ = C * Real.sqrt T * (Real.log (n : ℝ) + 1) := by ring

/-- Output of Algorithm 2 (source p.7, line 4 and line 7). -/
inductive VtsOutput (n : ℕ) where
  /-- An index found by some `B_k`. -/
  | found (i : Fin n)
  /-- The output `No solutions` of line 7. -/
  | none

/-- On an empty solution set, the readout of every `B_k` fails (there is no
`i` with `x_i = 1` to verify), so Algorithm 2 reaches line 7 and outputs
`No solutions`.  This is a property of the source's Algorithm 2 by
construction; it is recorded as a hypothesis `hsound` because the file does
not model the measurement/verification stage. -/
def SoundOnEmpty {n : ℕ} (M : Finset (Fin n)) (out : VtsOutput n) : Prop :=
  M = ∅ → out = VtsOutput.none

/-- **Lemma 4**, empty case (source p.6–7): Algorithm 2 outputs "No solutions"
and has complexity `O(√T log n)`.  The output statement is immediate from
`SoundOnEmpty`; the complexity is `lemma4_empty_cost`. -/
theorem lemma4_algorithm2_empty (n d : ℕ) (M : Finset (Fin n))
    (out : VtsOutput n) (T c : ℝ) (hn : 0 < n) (hM : M = ∅)
    (hsound : SoundOnEmpty M out) (hd : 1 ≤ d)
    (h3d : (3 : ℝ) ^ d ≤ 3 * Real.sqrt (n : ℝ))
    (hc : 0 < c) (bCost : ℕ → ℝ)
    (hb : ∀ k ∈ Finset.Icc 1 d,
      bCost k ≤ c * (k : ℝ) * (3 : ℝ) ^ k * Real.sqrt (T / (n : ℝ))) :
    out = VtsOutput.none ∧
      ∃ C : ℝ, 0 < C ∧
        (∑ j ∈ Finset.Icc 1 d, ∑ k ∈ Finset.Icc 1 j, bCost k)
          ≤ C * Real.sqrt T * (Real.log (n : ℝ) + 1) :=
  ⟨hsound hM, lemma4_empty_cost n d T c hn hd h3d hc bCost hb⟩

end Qatlib.Papers.VarTimeSearch23.MainResults
