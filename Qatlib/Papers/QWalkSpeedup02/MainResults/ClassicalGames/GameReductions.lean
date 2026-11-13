/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpeedup02.MainResults.Common.FiniteProbability
import Mathlib.Tactic

/-!
# Probability identities for classical game reductions

This module gives finite probability versions of the game comparisons in Lemmas 4–7 of
[ChildsEtAl2003]. `lemma4_game1_le_game2` controls disagreement outside a bad event, while the
remaining results express invariance under an auxiliary coloring, monotonicity of winning
events, and transfer to a tree-valued pushforward distribution.

## Main statements

* `lemma4_game1_le_game2`: the comparison bound from an assumed bad-event estimate.
* `lemma5_coloring_average`: averaging an event independent of the coloring.
* `lemma7_tree_pushforward`: equality of winning probabilities under the tree pushforward.

## References

* [Childs et al., 2003][ChildsEtAl2003]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.GameReductions

open Qatlib.Papers.QWalkSpeedup02.MainResults.Common.FiniteProbability

/-- For natural `t` and `n`, bounds `t * (2^(n+2) - 2) / 2^(2*n)` by `4*t / 2^n`. See [Childs et
al., Lemma 4][ChildsEtAl2003]. -/
lemma forgery_arithmetic (t n : ℕ) :
    (t : ℝ) * ((2 : ℝ) ^ (n + 2) - 2) / (2 : ℝ) ^ (2 * n) ≤
      4 * (t : ℝ) / (2 : ℝ) ^ n := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have h2n2 : (0 : ℝ) < (2 : ℝ) ^ (2 * n) := pow_pos (by norm_num) _
  have ht : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hpow : (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show 2 * n = n + n by ring, pow_add]
  have h4 : (2 : ℝ) ^ (n + 2) = 4 * (2 : ℝ) ^ n := by
    rw [pow_add]
    ring
  rw [div_le_div_iff₀ h2n2 h2n, h4, hpow]
  nlinarith [h2n, ht, mul_pos h2n h2n]

/-- If the two winning events agree outside a bad event satisfying the stated estimate, the
first winning probability is at most the second plus `4*t / 2^n`. See [Childs et al., Lemma
4][ChildsEtAl2003]. -/
theorem lemma4_game1_le_game2 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (t n : ℕ)
    (win1 win2 bad : Ω → Prop) [DecidablePred win1] [DecidablePred win2]
    [DecidablePred bad]
    (hagree : ∀ ω, ¬ bad ω → (win1 ω ↔ win2 ω))
    (hbad : P.eventMass bad ≤
      (t : ℝ) * ((2 : ℝ) ^ (n + 2) - 2) / (2 : ℝ) ^ (2 * n)) :
    P.eventMass win1 ≤ P.eventMass win2 + 4 * (t : ℝ) / (2 : ℝ) ^ n := by
  have h1 : P.eventMass win1 ≤ P.eventMass (fun ω => win2 ω ∨ bad ω) := by
    refine P.eventMass_mono ?_
    intro ω hω
    by_cases hb : bad ω
    · exact Or.inr hb
    · exact Or.inl ((hagree ω hb).mp hω)
  have h2 : P.eventMass (fun ω => win2 ω ∨ bad ω) ≤
      P.eventMass win2 + P.eventMass bad := P.eventMass_union_le _ _
  have h3 : P.eventMass bad ≤ 4 * (t : ℝ) / (2 : ℝ) ^ n :=
    hbad.trans (forgery_arithmetic t n)
  linarith

/-- If every coloring gives the same winning event as `win3`, averaging its probability against
the distribution `Q` equals the probability of `win3`. See [Childs et al., Lemma
5][ChildsEtAl2003]. -/
theorem lemma5_coloring_average {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : FinProb Ω) (Q : FinProb Γ) (win2 : Γ → Ω → Prop) [DecidableRel win2]
    (win3 : Ω → Prop) [DecidablePred win3]
    (hwin : ∀ C ω, win2 C ω ↔ win3 ω) :
    (∑ C, Q.prob C * P.eventMass (win2 C)) = P.eventMass win3 := by
  have h : ∀ C, P.eventMass (win2 C) = P.eventMass win3 :=
    fun C => P.eventMass_congr (hwin C)
  simp only [h]
  rw [← Finset.sum_mul, Q.sum_one, one_mul]

/-- Pointwise implication from `win3` to `win4` gives the corresponding inequality between their
winning probabilities. See [Childs et al., Lemma 6][ChildsEtAl2003]. -/
theorem lemma6_game3_le_game4 {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (win3 win4 : Ω → Prop) [DecidablePred win3] [DecidablePred win4]
    (hwin : ∀ ω, win3 ω → win4 ω) :
    P.eventMass win3 ≤ P.eventMass win4 :=
  P.eventMass_mono hwin

/-- If `win4` is equivalent to `win5` of the sampled tree, its probability equals the
probability of `win5` under the tree pushforward distribution. See [Childs et al., Lemma
7][ChildsEtAl2003]. -/
theorem lemma7_tree_pushforward {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
    (P : FinProb Ω) (tree : Ω → T) (win4 : Ω → Prop) [DecidablePred win4]
    (win5 : T → Prop) [DecidablePred win5]
    (hwin : ∀ ω, win4 ω ↔ win5 (tree ω)) :
    P.eventMass win4 = (P.pushforward tree).eventMass win5 := by
  have h : P.eventMass win4 = P.eventMass (fun ω => win5 (tree ω)) :=
    P.eventMass_congr hwin
  rw [h]
  exact P.eventMass_pushforward tree win5

end Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.GameReductions
