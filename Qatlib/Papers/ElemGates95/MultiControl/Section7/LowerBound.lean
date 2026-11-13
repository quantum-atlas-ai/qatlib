/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.MultiControl.Section7.GrayOrdering
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Graph cuts and controlled-gate tensor obstruction

This module proves two ingredients of the lower-bound argument in Lemma 7.7 of
[BarencoEtAl1995]. `IsWireCut` describes a nontrivial vertex partition with no crossing edges,
and `exists_cut_of_sparse` obtains such a partition from a graph on `n >= 1` wires with fewer
than `n - 1` edges.

On the algebraic side, `oneCtrlGate` is the two-wire controlled matrix and `IsScalar` means a
scalar multiple of the identity. `controlled_not_tensor` shows that a controlled nonscalar
matrix cannot be a single Kronecker product. `lemma77_core` packages the graph and matrix facts;
the bridge to a lower bound for concrete gate lists is developed separately.

## Main statements

* `exists_cut_of_sparse` gives a nontrivial cut for a sufficiently sparse wire graph.
* `controlled_not_tensor` rules out tensor factorization of a controlled nonscalar matrix.
* `lemma77_core` combines these two ingredients.

## References

* [Barenco et al., 1995][BarencoEtAl1995], Section 7, Lemma 7.7.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.ElemGates95.MultiControl.Section7

/-- A nontrivial partition of the wire vertices into `A` and its complement such that every
graph edge has both endpoints on the same side. -/
def IsWireCut {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ Aᶜ.Nonempty ∧ ∀ a b : Fin n, G.Adj a b → (a ∈ A ↔ b ∈ A)

/-- A graph on `n >= 1` wire vertices with fewer than `n - 1` edges has a nontrivial wire cut. -/
theorem exists_cut_of_sparse {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 1 ≤ n)
    (hcard : Nat.card ↑G.edgeSet < n - 1) :
    ∃ A : Finset (Fin n), IsWireCut G A := by
  classical

  have hnc : ¬ G.Connected := by
    intro hc
    have hle := hc.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin] at hle
    omega

  have hnp : ¬ G.Preconnected := by
    intro hp
    exact hnc ((SimpleGraph.connected_iff G).mpr ⟨hp, ⟨⟨0, by omega⟩⟩⟩)

  rw [SimpleGraph.Preconnected, not_forall] at hnp
  obtain ⟨u, hnp⟩ := hnp
  rw [not_forall] at hnp
  obtain ⟨v, huv⟩ := hnp

  refine ⟨Finset.univ.filter (fun w => G.Reachable u w), ?_, ?_, ?_⟩
  · exact ⟨u, by simp⟩
  · refine ⟨v, Finset.mem_compl.mpr ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact huv
  · intro a b hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      exact ha.trans hab.reachable
    · intro hb
      exact hb.trans (SimpleGraph.adj_comm G a b |>.mp hab).reachable

/-- The two-wire controlled matrix that applies `U` to the second bit when the first bit is true
and acts as the identity when it is false. -/
def oneCtrlGate (U : Matrix Bool Bool ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (if p.1 = true then U p.2 q.2 else (1 : Matrix Bool Bool ℂ) p.2 q.2)
    else 0

/-- The property that a two-dimensional complex matrix is a scalar multiple of the identity. -/
def IsScalar (U : Matrix Bool Bool ℂ) : Prop := ∃ c : ℂ, U = c • (1 : Matrix Bool Bool ℂ)

/-- If `U` is not a scalar multiple of the identity, its one-control matrix cannot equal a
Kronecker product of two single-wire matrices. -/
theorem controlled_not_tensor (U : Matrix Bool Bool ℂ) (hU : ¬ IsScalar U) :
    ¬ ∃ A B : Matrix Bool Bool ℂ,
      Matrix.kroneckerMap (fun a b => a * b) A B = oneCtrlGate U := by
  rintro ⟨A, B, hAB⟩

  have h00 : ∀ j l, A false false * B j l = (1 : Matrix Bool Bool ℂ) j l := by
    intro j l
    have := congrFun (congrFun hAB (false, j)) (false, l)
    simpa [Matrix.kroneckerMap_apply, oneCtrlGate] using! this
  have h11 : ∀ j l, A true true * B j l = U j l := by
    intro j l
    have := congrFun (congrFun hAB (true, j)) (true, l)
    simpa [Matrix.kroneckerMap_apply, oneCtrlGate] using! this
  show False

  have hAsmul : A false false • B = (1 : Matrix Bool Bool ℂ) := by
    ext j l
    rw [Matrix.smul_apply, smul_eq_mul]
    exact h00 j l
  have hone_ne : (1 : Matrix Bool Bool ℂ) ≠ 0 := by
    intro hc
    have hz := congrFun (congrFun hc false) false
    simp at hz
  have hA_ne : A false false ≠ 0 := by
    intro h0
    have : (0 : ℂ) • B = (1 : Matrix Bool Bool ℂ) := by rw [← h0]; exact hAsmul
    rw [zero_smul] at this
    exact hone_ne this.symm
  have hB : B = (A false false)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
    have := congrArg (fun M => (A false false)⁻¹ • M) hAsmul
    simp only [smul_smul, inv_mul_cancel₀ hA_ne, one_smul] at this
    exact this

  apply hU
  refine ⟨A true true * (A false false)⁻¹, ?_⟩
  have hUm : U = A true true • B := by
    ext j l
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (h11 j l).symm
  rw [hUm, hB, smul_smul]

/-- Packages the sparse-graph cut theorem together with the tensor-factorization obstruction for
a controlled nonscalar matrix. These are two ingredients of the lower-bound argument in
Lemma 7.7 of [BarencoEtAl1995]. -/
theorem lemma77_core {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 1 ≤ n)
    (hcard : Nat.card ↑G.edgeSet < n - 1) :
    (∃ A : Finset (Fin n), IsWireCut G A) ∧
      ∀ U : Matrix Bool Bool ℂ, ¬ IsScalar U →
        ¬ ∃ A B : Matrix Bool Bool ℂ,
          Matrix.kroneckerMap (fun a b => a * b) A B = oneCtrlGate U :=
  ⟨exists_cut_of_sparse G hn hcard, fun U hU => controlled_not_tensor U hU⟩

end Qatlib.Papers.ElemGates95.MultiControl.Section7
