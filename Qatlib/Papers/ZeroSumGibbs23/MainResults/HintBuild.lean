/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel

@[expose] public section


/-!
# HintBuild deterministic core

This module preserves closed algebraic and finite-dimensional source results
from arXiv:2301.03763v1. It does not assert a circuit implementation, concentration
bound, or end-to-end algorithmic complexity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.HintBuild
open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model
variable {m n N : ℕ}

/-- The set `B = {i ∈ [n] | q̃_i ≥ 1/(2k)}` of Lemma 3 (p.12). -/
def hintSet (k N : ℕ) (ω : Fin N → Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => 1 / (2 * (k : ℝ)) ≤ empiricalDist N ω j

/-- The overestimating vector `q` of Lemma 3 (p.12):
`q_j = 18 q̃_j` on `B`, `q_j = 18/k` off `B`. -/
def empiricalHint (k N : ℕ) (ω : Fin N → Fin n) : Fin n → ℝ :=
  fun j => if 1 / (2 * (k : ℝ)) ≤ empiricalDist N ω j then 18 * empiricalDist N ω j
           else 18 / (k : ℝ)

/-- Membership in `hintSet` is exactly the defining inequality. -/
theorem mem_hintSet {k N : ℕ} {ω : Fin N → Fin n} {j : Fin n} :
    j ∈ hintSet k N ω ↔ 1 / (2 * (k : ℝ)) ≤ empiricalDist N ω j := by
  simp [hintSet]

/-- The hint is nonnegative when `k > 0`. -/
theorem hint_nonneg {k N : ℕ} (hk : 0 < k) (ω : Fin N → Fin n) (j : Fin n) :
    0 ≤ empiricalHint k N ω j := by
  unfold empiricalHint
  split_ifs with h
  · have := empiricalDist_nonneg ω j
    linarith
  · have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    positivity

/-- `‖q‖₁ ≤ 18 ‖q̃‖₁ + 18n/k`, the first inequality of the proof of Lemma 3. -/
theorem hint_l1_le {n k N : ℕ} (hk : 0 < k) (ω : Fin N → Fin n) :
    l1Norm (empiricalHint k N ω) ≤
      18 * l1Norm (empiricalDist N ω) + 18 * (n : ℝ) / (k : ℝ) := by
  unfold l1Norm
  calc
    ∑ j, |empiricalHint k N ω j| = ∑ j, empiricalHint k N ω j := by
      refine Finset.sum_congr rfl fun j _ => abs_of_nonneg ?_
      exact hint_nonneg hk ω j
    _ ≤ ∑ j, (18 * empiricalDist N ω j + 18 / (k : ℝ)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      unfold empiricalHint
      split_ifs with h
      · have hp : (0 : ℝ) ≤ 18 / (k : ℝ) := by positivity
        linarith
      · have hp : (0 : ℝ) ≤ 18 * empiricalDist N ω j := by
          have := empiricalDist_nonneg ω j
          linarith
        linarith
    _ = 18 * l1Norm (empiricalDist N ω) + 18 * (n : ℝ) / (k : ℝ) := by
      have habs : l1Norm (empiricalDist N ω) = ∑ j, empiricalDist N ω j :=
        Finset.sum_congr rfl fun j _ => abs_of_nonneg (empiricalDist_nonneg ω j)
      rw [habs, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hconst : (∑ _j : Fin n, 18 / (k : ℝ)) = 18 * (n : ℝ) / (k : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      rw [hconst]

/-- The first conclusion of Lemma 3: `‖q‖₁ = O(n/k)`, with the explicit
constant `36`: `‖q‖₁ ≤ 36 n/k` whenever `k ≤ n`. -/
theorem hint_l1_bound {n k N : ℕ} (hk : 0 < k) (hkn : k ≤ n) (ω : Fin N → Fin n) :
    l1Norm (empiricalHint k N ω) ≤ 36 * (n : ℝ) / (k : ℝ) := by
  have h1 := hint_l1_le (N := N) hk ω
  have h2 : l1Norm (empiricalDist N ω) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      unfold l1Norm empiricalDist
      simp
    · rw [l1Norm_eq_one_of_isDist (empiricalDist_isDist hN ω)]
  have hnk : (1 : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hk)]
    simpa using (show (k : ℝ) ≤ (n : ℝ) from by exact_mod_cast hkn)
  have hnk18 : (18 : ℝ) ≤ 18 * (n : ℝ) / (k : ℝ) := by
    calc (18 : ℝ) = 18 * 1 := by ring
      _ ≤ 18 * ((n : ℝ) / (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hnk (by norm_num)
      _ = 18 * (n : ℝ) / (k : ℝ) := by ring
  have h18 : 18 * l1Norm (empiricalDist N ω) ≤ 18 := by
    have h := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 18)
    linarith
  calc l1Norm (empiricalHint k N ω) ≤
      18 * l1Norm (empiricalDist N ω) + 18 * (n : ℝ) / (k : ℝ) := h1
    _ ≤ 18 + 18 * (n : ℝ) / (k : ℝ) := by linarith
    _ ≤ 18 * (n : ℝ) / (k : ℝ) + 18 * (n : ℝ) / (k : ℝ) := by linarith
    _ = 36 * (n : ℝ) / (k : ℝ) := by ring

/-- Given the two Chernoff events of Lemma 3's proof, the hint dominates any
`p_{τ+s}` with `p_{τ+s} ≤ 9 p_τ` (Lemma 2). This is the deterministic reduction
`(2)`, `(3)` on p.12. -/
theorem hint_dominates {n k N : ℕ} {pτ ps : Fin n → ℝ}
    (hps : ∀ j, ps j ≤ 9 * pτ j) (ω : Fin N → Fin n)
    (hB : ∀ j, 1 / (2 * (k : ℝ)) ≤ empiricalDist N ω j → pτ j ≤ 2 * empiricalDist N ω j)
    (hnB : ∀ j, ¬ (1 / (2 * (k : ℝ)) ≤ empiricalDist N ω j) → pτ j ≤ 2 / (k : ℝ)) :
    ∀ j, ps j ≤ empiricalHint k N ω j := by
  intro j
  unfold empiricalHint
  split_ifs with h
  · have h1 := hB j h
    have h2 := hps j
    calc ps j ≤ 9 * pτ j := h2
      _ ≤ 9 * (2 * empiricalDist N ω j) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 18 * empiricalDist N ω j := by ring
  · have h1 := hnB j h
    have h2 := hps j
    calc ps j ≤ 9 * pτ j := h2
      _ ≤ 9 * (2 / (k : ℝ)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 18 / (k : ℝ) := by ring

end Qatlib.Papers.ZeroSumGibbs23.MainResults.HintBuild
