/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects
public import Qatlib.Papers.MinorClosed10.MainResults.ForestModel
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

/-! # Forest-adversary model of Theorem 3.4

Childs--Kothari, arXiv:1011.1443v2, Section 3.2, pp. 7--8.

This module fixes the two graph families and the four-vertex switch relation used
in the proof of Theorem 3.4.  The family `X` consists of the labelled paths, the
family `Y` of graphs that are a disjoint union of a path and a cycle, both with
more than `n/3` vertices.  The relation records the four-vertex switch of
Figure 2.  The module contains the model only; the adversary lower bound and the
counts `m, m' = Ω(n²)` and `l_max = O(n)` are not asserted here.
-/

set_option autoImplicit false
namespace Qatlib.Papers.MinorClosed10.MainResults.ForestAdversaryModel

open Qatlib.Papers.MinorClosed10.MainResults

/-- The family `X_n`: labelled paths on `n` vertices. -/
def PathFamily (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // Nonempty (G ≃g PathGraph (n - 1))}

/-- The family `Y_n`: graphs whose edges are a path on `A` together with a cycle
on a disjoint `B`, with `|A|, |B| > n/3`. -/
def PathCycleFamily (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) //
    ∃ A B : Finset (Fin n),
      Disjoint A B ∧
      n / 3 < A.card ∧ n / 3 < B.card ∧
      Nonempty ((G.induce (A : Set (Fin n))) ≃g PathGraph (A.card - 1)) ∧
      Nonempty ((G.induce (B : Set (Fin n))) ≃g CycleGraph B.card) ∧
      (∀ ⦃u v⦄, G.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))}

/-- The four-vertex switch of Figure 2 on a fixed vertex set: two graphs agree
off the four vertices and have the two perfect matchings `(a,b),(c,d)` and
`(a,c),(b,d)` respectively on them. -/
def FourVertexSwitch {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    (∀ u v,
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (G.Adj u v ↔
        (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        (u = c ∧ v = d) ∨ (u = d ∧ v = c))) ∧
    (∀ u v,
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (H.Adj u v ↔
        (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
        (u = b ∧ v = d) ∨ (u = d ∧ v = b)))

/-- The adversary relation `R` of Theorem 3.4: an `X`-graph and a `Y`-graph
related when they differ by a four-vertex switch. -/
def forestAdversaryRelation {n : ℕ} (x : PathFamily n) (y : PathCycleFamily n) :
    Prop :=
  FourVertexSwitch x.1 y.1

/-- The switch relation is symmetric in its two graph arguments. -/
theorem fourVertexSwitch_comm {n : ℕ} {G H : SimpleGraph (Fin n)} :
    FourVertexSwitch G H ↔ FourVertexSwitch H G := by
  constructor <;>
    rintro ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, hG, hH⟩
  · refine ⟨a, c, b, d, h2, h1, h3, h4.symm, h6, h5, ?_, ?_⟩
    · intro u v hu hv
      exact hH u v (by tauto) (by tauto)
    · intro u v hu hv
      exact hG u v (by tauto) (by tauto)
  · refine ⟨a, c, b, d, h2, h1, h3, h4.symm, h6, h5, ?_, ?_⟩
    · intro u v hu hv
      exact hH u v (by tauto) (by tauto)
    · intro u v hu hv
      exact hG u v (by tauto) (by tauto)

end Qatlib.Papers.MinorClosed10.MainResults.ForestAdversaryModel
