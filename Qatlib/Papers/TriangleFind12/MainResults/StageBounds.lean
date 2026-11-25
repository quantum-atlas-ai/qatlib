/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TriangleFind12.MainResults.PairPermutationRatio
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Edge conditioning and the triangle learning-graph exponents

The permutation hit event is monotone under adding edges, so the probability of a
regular subgraph bounds the larger edge set from below. For the proposed stage
sizes, the first and last scalar costs have the same exponent.
-/

set_option autoImplicit false

open Qatlib.Papers.TriangleFind12.MainResults
open scoped Classical

namespace Qatlib.Papers.TriangleFind12.MainResults

/-- Adding edges to the regular-type subgraph can only increase the source
conditional probability of an edge hit, yielding the factor of Lemma 9. -/
theorem lemma9_pair_ratio_lower {n : ℕ} (Y1 Y2 : Finset (Fin n))
    (K E : Finset (Fin n × Fin n)) (y1 y2 : Fin n) (d e : ℕ)
    (hy1 : y1 ∈ Y1) (hy2 : y2 ∈ Y2) (hne : y1 ≠ y2) (hdisj : Disjoint Y1 Y2)
    (hKE : K ⊆ E) (hE : ∀ p ∈ E, p.1 ∈ Y1 ∧ p.2 ∈ Y2)
    (htype : IsType K Y1 Y2 d e) :
    (d : ℚ) / (max Y1.card Y2.card : ℚ) ≤
      ((permEdgeHit E Y1 Y2 y1 y2).card : ℚ) / ((permFiberAll Y1 Y2 y1 y2).card : ℚ) := by
  have hsub : permEdgeHit K Y1 Y2 y1 y2 ⊆ permEdgeHit E Y1 Y2 y1 y2 := by
    intro σ hσ
    unfold permEdgeHit at hσ ⊢
    obtain ⟨hfiber, p, hp, happly⟩ := Finset.mem_filter.mp hσ
    exact Finset.mem_filter.mpr ⟨hfiber, p, hKE hp, happly⟩
  have hprob := lemma10_pair_probability_of_type Y1 Y2 K y1 y2 d e
    hy1 hy2 hne hdisj (fun p hp => hE p (hKE hp)) htype
  have hden : (0 : ℚ) < Y2.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨y2, hy2⟩
  calc
    _ ≤ (d : ℚ) / (Y2.card : ℚ) :=
      div_le_div_of_nonneg_left (by positivity) hden (by exact_mod_cast le_max_right Y1.card Y2.card)
    _ = _ := hprob.symm
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)

/-- Substitution of the source parameters gives the common exponent for stages one and six. -/
theorem triangle_setup_and_last_cost (n : ℝ) (hn : 0 < n) :
    n ^ (4 / 7 : ℝ) * n ^ (5 / 7 : ℝ) = n ^ (9 / 7 : ℝ) ∧
      n ^ (3 / 2 : ℝ) / Real.sqrt (n ^ (3 / 7 : ℝ)) = n ^ (9 / 7 : ℝ) := by
  constructor
  · rw [← Real.rpow_add hn]
    norm_num
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, ← Real.rpow_sub hn]
    norm_num

end Qatlib.Papers.TriangleFind12.MainResults
