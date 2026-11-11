/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceComplexityInterface

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 analytic and probabilistic vocabulary

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3 (18 Dec 2019).

This module adds the vocabulary shared by the gradient-estimation, sampling and
discretization claims:

* `IsBetaSmoothOn` is Definition 2.10 / equation (2.3) (`β`-smoothness on a set, with an
  explicit gradient field);
* `uniformProb`/`uniformExpect` are the uniform probabilities/expectations on a finite
  sample space, used for the paper's `Pr[·]`/`𝔼[·]` statements (the paper's randomness is
  always over a finite uniform set, e.g. the grid `G_{B∞(x,r₁),l}`);
* `sameOrdering` is the ordering relation of Algorithm 5's `Ord` (Section C.2.1), and
  `gridPoint` from the model file is `χ(a,π)` of (3.35).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Definition 2.10 / equation (2.3): `f` is `β`-smooth on `S` if it admits a gradient
field `gradf` and the second-order bound `|f(y) - f(x) - ⟨∇f(x), y-x⟩| ≤ (β/2)‖y-x‖²`
holds for `x, y ∈ S`. -/
def IsBetaSmoothOn {n : ℕ} (f : Pt n → ℝ) (S : Set (Pt n)) (β : ℝ) : Prop :=
  ∃ gradf : Pt n → Pt n,
    (∀ x ∈ S, HasGradientAt f x (gradf x)) ∧
      ∀ x ∈ S, ∀ y ∈ S, |f y - f x - dot (gradf x) (y - x)| ≤ β / 2 * norm2Sq (y - x)

/-- Definition 2.9 (second form): `L`-Lipschitz continuity on a set, with the `ℓ∞` norm as
in (2.2).  This duplicates `IsLipschitzOn` for convenience of local use. -/
lemma lipschitz_of_abs_le {n : ℕ} {f : Pt n → ℝ} {S : Set (Pt n)} {L : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, |f y - f x| ≤ L * normInf (y - x)) :
    IsLipschitzOn f S L := h

/-- Uniform probability on the finite sample space `Fin N`: fraction of outcomes satisfying
`P`.  The paper's probability statements are all over finite uniform spaces. -/
def uniformProb {N : ℕ} (P : Fin N → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (N : ℝ)

/-- The `uniformProb_nonneg` result for the ConvexOpt18 paper model. -/
lemma uniformProb_nonneg {N : ℕ} (P : Fin N → Prop) [DecidablePred P] :
    0 ≤ uniformProb P := by
  unfold uniformProb; positivity

/-- The `uniformProb_le_one` result for the ConvexOpt18 paper model. -/
lemma uniformProb_le_one {N : ℕ} (hN : 0 < N) (P : Fin N → Prop) [DecidablePred P] :
    uniformProb P ≤ 1 := by
  unfold uniformProb
  rw [div_le_one (by exact_mod_cast hN)]
  have h := Finset.card_le_univ (Finset.univ.filter P)
  simpa using h

/-- Uniform probability of a finite *set* of bad outcomes: fraction of outcomes in `bad`.
This form is used when the event is an arbitrary `Prop` (no decidable instance needed). -/
def uniformProbOf {N : ℕ} (bad : Finset (Fin N)) : ℝ := (bad.card : ℝ) / (N : ℝ)

/-- Uniform expectation on the finite sample space `Fin N`. -/
def uniformExpect {N : ℕ} (X : Fin N → ℝ) : ℝ := (∑ ω, X ω) / (N : ℝ)

/-- `Ord(y) = Ord(z)`: the relative order of the `2n` numbers `y₁,…,yₙ,1-y₁,…,1-yₙ` agrees
with that of `z₁,…,zₙ,1-z₁,…,1-zₙ` (Section C.2.1, equation (3.38)). -/
def sameOrdering {n : ℕ} (y z : Pt n) : Prop :=
  ∀ i j : Fin n,
    (y i ≤ y j ↔ z i ≤ z j) ∧ (y i ≤ 1 - y j ↔ z i ≤ 1 - z j)

end Qatlib.Papers.ConvexOpt18.MainResults
