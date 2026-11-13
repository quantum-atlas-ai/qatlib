/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch06.MainResults.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Transcript counting for ordered-search lower bounds

Defines exact recovery from binary transcripts and derives the counting bound `N ≤ 2 ^ k`. This
yields the classical logarithmic query lower bound, alongside a comparison of the quantum and
classical lower-bound expressions used in [ChildsLandahlParrilo2007].

## Main statements

* `classicalLowerBound_le_queries`: converts transcript counting into a real logarithmic lower
  bound.

## References

* [Childs et al., 2007][ChildsLandahlParrilo2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch06.MainResults

/-- A binary transcript of length `k`. -/
abbrev Transcript (k : ℕ) := Fin k → Bool

/-- Existence of a transcript assignment and decoder that recover every element of `Fin N`
exactly. -/
def ExactComparisonAlgorithm (N k : ℕ) : Prop :=
  ∃ transcript : Fin N → Transcript k, ∃ decoder : Transcript k → Fin N,
    ∀ j : Fin N, decoder (transcript j) = j

/-- There are `2 ^ k` binary transcripts of length `k`. -/
theorem card_transcript (k : ℕ) : Fintype.card (Transcript k) = 2 ^ k := by
  simp [Transcript]

/-- Exact recovery of `N` alternatives from `k` binary transcript entries implies `N ≤ 2 ^ k`
[ChildsLandahlParrilo2007]. -/
theorem exactComparisonAlgorithm_card_le {N k : ℕ}
    (h : ExactComparisonAlgorithm N k) : N ≤ 2 ^ k := by
  obtain ⟨transcript, decoder, hdec⟩ := h
  have hinj : Function.Injective transcript := by
    intro a b hab
    have ha := hdec a
    rw [hab, hdec b] at ha
    exact ha.symm
  have hcard := Fintype.card_le_of_injective transcript hinj
  rwa [card_transcript, Fintype.card_fin] at hcard

/-- For positive `N`, exact recovery from length-`k` binary transcripts requires at least
`classicalLowerBound N` transcript entries [ChildsLandahlParrilo2007]. -/
theorem classicalLowerBound_le_queries {N k : ℕ} (hN : 0 < N)
    (h : ExactComparisonAlgorithm N k) :
    classicalLowerBound (N : ℝ) ≤ (k : ℝ) := by
  have hcard : (N : ℝ) ≤ (2 : ℝ) ^ k := by
    have hnat : ((N : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast exactComparisonAlgorithm_card_le h
    push_cast at hnat
    exact hnat
  have hlog : Real.log (N : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1 := Real.log_le_log hNpos hcard
    rwa [Real.log_pow] at h1
  unfold classicalLowerBound
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ h2]
  linarith

/-- For `N ≥ 1`, the quantum lower-bound expression is strictly smaller than the classical
logarithmic expression [ChildsLandahlParrilo2007]. -/
theorem quantumLowerBound_lt_classicalBound {N : ℝ} (hN : 1 ≤ N) :
    quantumLowerBound N < classicalLowerBound N := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : Real.log 2 < Real.pi := by
    have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    linarith [Real.pi_gt_three]
  have hkey : (Real.log N - 1) * Real.log 2 < Real.log N * Real.pi := by
    have hd : 0 ≤ Real.log N * (Real.pi - Real.log 2) :=
      mul_nonneg hlogN (by linarith)
    nlinarith
  unfold quantumLowerBound classicalLowerBound
  rw [div_lt_div_iff₀ hpi h2]
  exact hkey

end Qatlib.Papers.OrderedSearch06.MainResults
