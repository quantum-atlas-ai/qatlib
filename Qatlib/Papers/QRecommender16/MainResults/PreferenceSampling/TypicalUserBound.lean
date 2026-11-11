/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3.3 — the typical-user bound on bad recommendations

Source: Iordanis Kerenidis, Anupam Prakash, *Quantum Recommendation Systems*,
fixed version arXiv:1603.08675v3 (22 Sep 2016), Theorem 3.3, printed p. 9
(Section 3.2).

The paper's Theorem 3.3 refines Lemma 3.2 from a global average to a
*typical-user* statement. Writing `p i` for the probability that a pair sampled
from user `i`'s row is a bad recommendation, and assuming the row-norm
condition (4) of the paper, the theorem asserts that there is a set `S'` of at
least `(1 − δ − ζ) · m` users such that the *average* bad-recommendation
probability over `S'` is bounded by

  `[ε(1+ε)/(1−ε)]² / ( (1/√(1+γ) − ε/√δ)² · (1−δ−ζ) )`.

This file formalises the finite combinatorial core: from the fact that a
`(1−δ)`-fraction `G` of users have individual bad probability at most
`B = [ε(1+ε)/(1−ε)]² / (1/√(1+γ) − ε/√δ)²`, it produces a user set `S'` with
`|S'| ≥ (1−δ−ζ)·m` users and average bad probability at most `B/(1−δ−ζ)`.

Boundary / modelling. The full theorem is a probabilistic statement about the
sampling procedure of Section 3, whose analysis (the concentration of
`‖T̃ − T‖_F` and the row-mass estimates behind condition (4)) is not modelled
here. We state the conclusion conditional on the per-good-user bound on `G`,
which is exactly what condition (4) and Lemma 3.2 supply, and do not re-derive
the concentration.
-/

namespace Qatlib.Papers.QRecommender16.MainResults.PreferenceSampling

set_option autoImplicit false

noncomputable section

variable {m : ℕ}

/-- The average of a per-user real quantity `p` over a finite user set `S`. -/
def avgOver (S : Finset (Fin m)) (p : Fin m → ℝ) : ℝ :=
  (S.sum p) / (S.card : ℝ)

/-- Theorem 3.3 (fixed arXiv:1603.08675v3, p. 9). Let `G` be the "good" set of
users supplied by the row-norm condition (4), with `|G| ≥ (1−δ)·m` and every
`i ∈ G` having bad-recommendation probability at most
`B = [ε(1+ε)/(1−ε)]² / (1/√(1+γ) − ε/√δ)²`. Then there is a set `S'` of at
least `(1−δ−ζ)·m` users whose average bad probability is at most
`B / (1−δ−ζ)`.

The combinatorial step takes `S' = G` and averages the per-user bound over `G`;
the probabilistic derivation of `G` from the Frobenius concentration of
Section 3.2 is not modelled. -/
theorem source_theorem_3_3
    (p : Fin m → ℝ) (G : Finset (Fin m)) (ε δ γ ζ : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 < δ) (hγ : 0 ≤ γ)
    (hζ0 : 0 ≤ ζ) (hδζ : δ + ζ < 1)
    (hGcard : ((1 - δ) * m : ℝ) ≤ (G.card : ℝ))
    (hGbound : ∀ i ∈ G, p i ≤
      (ε * (1 + ε) / (1 - ε)) ^ 2 / (1 / Real.sqrt (1 + γ) - ε / Real.sqrt δ) ^ 2) :
    ∃ S : Finset (Fin m),
      ((1 - δ - ζ) * m : ℝ) ≤ (S.card : ℝ) ∧
      avgOver S p ≤ (ε * (1 + ε) / (1 - ε)) ^ 2 /
        ((1 / Real.sqrt (1 + γ) - ε / Real.sqrt δ) ^ 2 * (1 - δ - ζ)) := by
  refine ⟨G, ?_, ?_⟩
  · have h1 : (1 - δ - ζ) * (m : ℝ) ≤ (1 - δ) * (m : ℝ) := by
      have hle : 1 - δ - ζ ≤ 1 - δ := by linarith
      exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg m)
    exact le_trans h1 hGcard
  · set B : ℝ := (ε * (1 + ε) / (1 - ε)) ^ 2 /
        (1 / Real.sqrt (1 + γ) - ε / Real.sqrt δ) ^ 2 with hB
    have hB0 : 0 ≤ B := by
      rw [hB]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hcpos : 0 < 1 - δ - ζ := by linarith
    have hsum : G.sum p ≤ (G.card : ℝ) * B := by
      calc
        G.sum p ≤ G.sum (fun _ => B) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hB]
          exact hGbound i hi
        _ = (G.card : ℝ) * B := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
    have hleB : avgOver G p ≤ B := by
      by_cases hc : G.card = 0
      · rw [avgOver, hc]
        simp only [Nat.cast_zero, div_zero]
        exact hB0
      · have hcpos' : 0 < (G.card : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hc
        have hstep : G.sum p / (G.card : ℝ) ≤ ((G.card : ℝ) * B) / (G.card : ℝ) :=
          div_le_div_of_nonneg_right hsum hcpos'.le
        have heq : ((G.card : ℝ) * B) / (G.card : ℝ) = B :=
          mul_div_cancel_left₀ B hcpos'.ne'
        change G.sum p / (G.card : ℝ) ≤ B
        linarith
    have hle : B ≤ B / (1 - δ - ζ) := by
      rw [le_div_iff₀ hcpos]
      have hstep : B * (1 - δ - ζ) ≤ B * 1 :=
        mul_le_mul_of_nonneg_left (by linarith : 1 - δ - ζ ≤ 1) hB0
      linarith
    have hdiv : B / (1 - δ - ζ) =
        (ε * (1 + ε) / (1 - ε)) ^ 2 /
          ((1 / Real.sqrt (1 + γ) - ε / Real.sqrt δ) ^ 2 * (1 - δ - ζ)) := by
      rw [hB, div_div]
    rw [← hdiv]
    exact le_trans hleB hle

end

end Qatlib.Papers.QRecommender16.MainResults.PreferenceSampling
