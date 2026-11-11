/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model: 3-Distinctness outer walk and its coin-dependent data

Fixed source: arXiv:1302.7316v1 (2013-02-28), Childs--Jeffery--Kothari--
Magniez, *A Time-Efficient Quantum Walk for 3-Distinctness Using Nested
Updates*.  All section/theorem references below are to that fixed version
(PDF pages of the local copy).

This file fixes the combinatorial vocabulary of Section 4:

* `TwoCollisions χ A B` is the paper's `P(A,B) = {(i,j) ∈ A×B : i≠j, χi=χj}`
  (Section 4, p.9);
* `PairIndices` is `I(S₂) = ⋃_{(i,j)∈S₂}{i,j}` (p.9);
* `InnerCollisions` is `P(S₁)` (p.9);
* `MarkedVertex` is the markedness predicate of Section 4.1 (p.9);
* `Adjacent`/`Neighbors` model the generalised Johnson graph `J(n₂,s₂,m)`
  (Section 4.1, p.10);
* `BumpCount` is the cardinality `|M^{S₂}|` used in the proof of Lemma 4.4
  (p.12-13, displayed counting formula);
* `GarbageSupport` / `PsiAmplitude` / `PsiState` are the superposition
  `|ψ(S₂,S₂')⟩` of equation (1), p.10, and of Lemma 4.4, p.12.

The counting lemma `card_pairIndices` and the symmetry lemma `lemma_4_4_psi`
are proved from the paper's structural hypothesis that all 2-collisions in
`A₁ × A₂` are disjoint (Section 2.2, p.4; used in the proof of Lemma 4.4).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel

open Classical
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-! ## Collision structure (Section 4, p.9) -/

/-- `P(A,B) = {(i,j) ∈ A × B : i ≠ j ∧ χ i = χ j}`: the set of 2-collisions
between `A` and `B` (Section 4, p.9). -/
def TwoCollisions (χ : ι → ℕ) (A B : Finset ι) : Finset (ι × ι) :=
  (A ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ χ p.1 = χ p.2)

/-- `I(S₂) = ⋃_{(i,j) ∈ S₂} {i,j}`: the indices occurring in the pairs of `S₂`
(Section 4, p.9). -/
def PairIndices (S : Finset (ι × ι)) : Finset ι :=
  S.biUnion (fun p => ({p.1, p.2} : Finset ι))

/-- `P(S₁)`: the collision pairs of `P(A₁,A₂)` that lie inside `S₁`
(Section 4, p.9). -/
def InnerCollisions (χ : ι → ℕ) (A B : Finset ι) (S1 : Finset ι) : Finset (ι × ι) :=
  (TwoCollisions χ A B).filter (fun p => p.1 ∈ S1 ∧ p.2 ∈ S1)

/-- `{i,j,k}` is a 3-collision (Section 2.2, p.4): three distinct indices with
equal values. -/
def IsThreeCollision (χ : ι → ℕ) (i j k : ι) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ χ i = χ j ∧ χ j = χ k

/-- A vertex `S₂` of the outer walk is marked if it contains a pair `(i,j)` that
is part of a 3-collision with an index `k ∈ A₃` (Section 4.1, p.9). -/
def MarkedVertex (χ : ι → ℕ) (A3 : Finset ι) (S2 : Finset (ι × ι)) : Prop :=
  ∃ p ∈ S2, ∃ k ∈ A3, IsThreeCollision χ p.1 p.2 k

/-- Vertices of the outer walk: `s₂`-element subsets of the collision set `P`
(Section 4.1, p.10). -/
def WalkVertices (P : Finset (ι × ι)) (s2 : ℕ) : Finset (Finset (ι × ι)) :=
  P.powersetCard s2

/-- The generalised Johnson graph `J(n₂,s₂,m)`: `S₂'` is adjacent to `S₂` when it
is obtained by replacing `m` elements of `S₂` by `m` distinct elements of
`P \ S₂` (Section 4.1, p.10). -/
def Adjacent (P : Finset (ι × ι)) (m : ℕ) (S2 S2' : Finset (ι × ι)) : Prop :=
  ∃ I ⊆ S2, ∃ J ⊆ P \ S2, I.card = m ∧ J.card = m ∧ S2' = (S2 \ I) ∪ J

/-- The neighbourhood `Γ(S₂)` of `S₂` in the generalised Johnson graph
(Section 4.1, p.10). -/
def Neighbors (P : Finset (ι × ι)) (m s2 : ℕ) (S2 : Finset (ι × ι)) :
    Finset (Finset (ι × ι)) :=
  (WalkVertices P s2).filter (Adjacent P m S2)

/-- All 2-collisions in `P` are pairwise disjoint.  This is the structural
assumption of Section 2.2 (p.4), used in the proof of Lemma 4.4 (p.13):
"all collisions in `A₁ × A₂` are disjoint". -/
def TwoCollisionsDisjoint (P : Finset (ι × ι)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint ({p.1, p.2} : Finset ι) {q.1, q.2}

/-- Every pair of `P` is an ordered pair of distinct indices inside
`A₁ × A₂` (the definition of `P(A₁,A₂)`). -/
def PairsWithin (P : Finset (ι × ι)) (A1 A2 : Finset ι) : Prop :=
  ∀ p ∈ P, p.1 ≠ p.2 ∧ p.1 ∈ A1 ∪ A2 ∧ p.2 ∈ A1 ∪ A2

/-! ## The counting `|M^{S₂}|` (proof of Lemma 4.4, p.12-13) -/

/-- The paper's cardinality formula for `M^{S₂}` (proof of Lemma 4.4,
p.13): `|M^{S₂}| = C(|P \ S₂|, m) · C(|(A₁∪A₂) \ I(S₂)| - 2m, s₁ - 2m)`. -/
def BumpCount (P : Finset (ι × ι)) (A1 A2 : Finset ι) (S2 : Finset (ι × ι))
    (s1 m : ℕ) : ℕ :=
  (P \ S2).card.choose m *
    ((((A1 ∪ A2) \ PairIndices S2).card - 2 * m).choose (s1 - 2 * m))

/-- Under the disjointness assumption, `|I(S₂)| = 2 |S₂|` (proof of Lemma 4.4,
p.13: "since all collisions in `S₂` are disjoint, we have `|I(S₂)| = 2 s₂`"). -/
theorem card_pairIndices (P S : Finset (ι × ι)) (hS : S ⊆ P)
    (hne : ∀ p ∈ P, p.1 ≠ p.2) (hdisj : TwoCollisionsDisjoint P) :
    (PairIndices S).card = 2 * S.card := by
  unfold PairIndices
  rw [Finset.card_biUnion]
  · calc ∑ p ∈ S, ({p.1, p.2} : Finset ι).card
        = ∑ _p ∈ S, 2 := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            rw [Finset.card_pair]
            exact hne p (hS hp)
      _ = 2 * S.card := by
            rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  · intro p hp q hq hpq
    exact hdisj p (hS hp) q (hS hq) hpq

/-- The counting `|M^{S₂}|` is independent of the vertex `S₂` among `s₂`-element
subsets of `P`: both factors depend only on `|P \ S₂| = n₂ - s₂` and on
`|I(S₂)| = 2s₂` (proof of Lemma 4.4, p.13). -/
theorem bumpCount_eq (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (S2 S2' : Finset (ι × ι)) (s1 m : ℕ)
    (hS2 : S2 ⊆ P) (hS2' : S2' ⊆ P) (hs : S2.card = S2'.card)
    (hsub : PairIndices S2 ⊆ A1 ∪ A2) (hsub' : PairIndices S2' ⊆ A1 ∪ A2)
    (hne : ∀ p ∈ P, p.1 ≠ p.2) (hdisj : TwoCollisionsDisjoint P) :
    BumpCount P A1 A2 S2 s1 m = BumpCount P A1 A2 S2' s1 m := by
  unfold BumpCount
  have hdiff : (P \ S2).card = (P \ S2').card := by
    have e1 : S2 ∩ P = S2 := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, hS2 h⟩
    have e2 : S2' ∩ P = S2' := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, hS2' h⟩
    rw [Finset.card_sdiff, Finset.card_sdiff, e1, e2, hs]
  have hI : (PairIndices S2).card = (PairIndices S2').card := by
    rw [card_pairIndices P S2 hS2 hne hdisj,
      card_pairIndices P S2' hS2' hne hdisj, hs]
  have hIc : ((A1 ∪ A2) \ PairIndices S2).card =
      ((A1 ∪ A2) \ PairIndices S2').card := by
    have e1 : PairIndices S2 ∩ (A1 ∪ A2) = PairIndices S2 := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, hsub h⟩
    have e2 : PairIndices S2' ∩ (A1 ∪ A2) = PairIndices S2' := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, hsub' h⟩
    rw [Finset.card_sdiff, Finset.card_sdiff, e1, e2, hI]
  rw [hdiff, hIc]

/-! ## The garbage state `|ψ(S₂,S₂')⟩`, equation (1), p.10 -/

/-- Support of the garbage superposition: the `(s₁ - 2m)`-subsets of
`(A₁∪A₂) \ I(S₂ ∪ S₂')` (equation (1), p.10). -/
def GarbageSupport (A1 A2 : Finset ι) (S2 S2' : Finset (ι × ι)) (s1 m : ℕ) :
    Finset (Finset ι) :=
  ((A1 ∪ A2) \ PairIndices (S2 ∪ S2')).powersetCard (s1 - 2 * m)

/-- Amplitude of `|Q(S̃₁)⟩` in `|ψ(S₂,S₂')⟩` (equation (1), p.10):
`√( C(n₂-s₂, m) / ( C(|P(S̃₁)|+m, m) · |M^{S₂}| ) )` on the support and `0`
elsewhere. -/
def PsiAmplitude (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (S2 S2' : Finset (ι × ι)) (s1 m : ℕ) (S1 : Finset ι) : ℝ :=
  if S1 ∈ GarbageSupport A1 A2 S2 S2' s1 m then
    Real.sqrt (((P \ S2).card.choose m : ℝ) /
      ((((InnerCollisions χ A1 A2 S1).card + m).choose m : ℝ) *
        (BumpCount P A1 A2 S2 s1 m : ℝ)))
  else 0

/-- The garbage state `|ψ(S₂,S₂')⟩` as a complex-valued function on the
`S̃₁`-basis (equation (1), p.10). -/
def PsiState (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (S2 S2' : Finset (ι × ι)) (s1 m : ℕ) : Finset ι → ℂ :=
  fun S1 => ((PsiAmplitude χ P A1 A2 S2 S2' s1 m S1 : ℝ) : ℂ)

/-- The support is symmetric in `(S₂,S₂')` (Lemma 4.4, p.10; used again in the
Garbage Swap analysis of Theorem 4.5, p.11). -/
theorem garbageSupport_comm (A1 A2 : Finset ι) (S2 S2' : Finset (ι × ι))
    (s1 m : ℕ) :
    GarbageSupport A1 A2 S2 S2' s1 m = GarbageSupport A1 A2 S2' S2 s1 m := by
  unfold GarbageSupport
  rw [Finset.union_comm S2 S2']

/-- **Lemma 4.4** (fixed arXiv:1302.7316v1, p.12-13).  For all edges
`(S₂,S₂')` of the outer walk, `|ψ(S₂,S₂')⟩ = |ψ(S₂',S₂)⟩`.  The proof is the
paper's: the support is symmetric (`garbageSupport_comm`), and `|M^{S₂}|` is
independent of `S₂` by the counting formula (`bumpCount_eq`). -/
theorem lemma_4_4_psi (χ : ι → ℕ) (P : Finset (ι × ι)) (A1 A2 : Finset ι)
    (S2 S2' : Finset (ι × ι)) (s1 m : ℕ)
    (hS2 : S2 ⊆ P) (hS2' : S2' ⊆ P) (hs : S2.card = S2'.card)
    (hsub : PairIndices S2 ⊆ A1 ∪ A2) (hsub' : PairIndices S2' ⊆ A1 ∪ A2)
    (hne : ∀ p ∈ P, p.1 ≠ p.2) (hdisj : TwoCollisionsDisjoint P) :
    PsiState χ P A1 A2 S2 S2' s1 m = PsiState χ P A1 A2 S2' S2 s1 m := by
  funext S1
  unfold PsiState PsiAmplitude
  rw [garbageSupport_comm A1 A2 S2 S2' s1 m]
  split_ifs with h
  · rw [bumpCount_eq P A1 A2 S2 S2' s1 m hS2 hS2' hs hsub hsub' hne hdisj]
    have e1 : S2 ∩ P = S2 := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · intro hh; exact hh.1
      · intro hh; exact ⟨hh, hS2 hh⟩
    have e2 : S2' ∩ P = S2' := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · intro hh; exact hh.1
      · intro hh; exact ⟨hh, hS2' hh⟩
    rw [Finset.card_sdiff, Finset.card_sdiff, e1, e2, hs]
  · rfl

end Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel
