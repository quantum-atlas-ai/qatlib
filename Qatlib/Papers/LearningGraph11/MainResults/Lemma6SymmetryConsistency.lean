/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Perm
import Qatlib.Papers.LearningGraph11.MainResults.SourceLearningGraphModel

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Lemma 6: symmetry gives consistency

Fixed source: arXiv:1109.5135v1, Lemma 6 and its proof (p. 7).

The symmetric group `S_n` acts on the `L`-vertices of a learning graph (permuting the
labels), hence on the `L`-edges. If `S_n` acts transitively on the flows, i.e.

`∀ y y', ∃ τ : Equiv.Perm V, ∀ e, p_y(e) = p_{y'}(τ e)`,

then the flows are consistent (Definition 5) with the edge sets `{[u]^+ : u ∈ V}`
consisting of all edges leaving the orbit class `[u]`, and likewise with the edge sets
`{[u]^- : u ∈ V}` of all edges entering `[u]`.

The edge action is an explicit hypothesis `edgePerm`, since the source model keeps the
edge set abstract; `hsrc`/`htgt` say that it permutes the endpoints as `τ` does. The
class-preserving property used in the proof is `part (τ e) = part e`, which holds for
`part e = [src e]` and `part e = [tgt e]` by `orbitOf_perm`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

/-- The equivalence class `[u] = {σ(u) : σ ∈ S_n}` of an `L`-vertex (p. 7). -/
def orbitOf {V : Type*} [Fintype V] [DecidableEq V] (u : V) : Finset V :=
  Finset.univ.image (fun σ : Equiv.Perm V => σ u)

/-- Membership in the orbit class: `v ∈ [u]` iff `v = σ(u)` for some permutation. -/
theorem mem_orbitOf {V : Type*} [Fintype V] [DecidableEq V] {u v : V} :
    v ∈ orbitOf u ↔ ∃ σ : Equiv.Perm V, σ u = v := by
  simp [orbitOf]

/-- The orbit class depends only on the orbit: `[σ(u)] = [u]`. -/
theorem orbitOf_perm {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) (u : V) :
    orbitOf (σ u) = orbitOf u := by
  ext v
  simp only [mem_orbitOf]
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨τ * σ, by simpa using hτ⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨τ * σ⁻¹, by simpa using hτ⟩

section Lemma6

variable {V E Y ι : Type*} [Fintype V] [Fintype E] [Fintype Y] [Fintype ι]
  [DecidableEq ι] [DecidableEq V]

/-- Reindexing a class sum along a class-preserving edge permutation: if the flows are
related by a symmetry that preserves the classes, the flow mass of every class agrees. -/
theorem class_sum_invariant
    (p : Y → E → ℝ) (part : E → ι) (edgePerm : Equiv.Perm V → E ≃ E)
    (hpart : ∀ (τ : Equiv.Perm V) (e : E), part (edgePerm τ e) = part e)
    (htrans : ∀ y y', ∃ τ : Equiv.Perm V, ∀ e : E, p y e = p y' (edgePerm τ e)) :
    ∀ y y' i, ∑ e ∈ piece part i, p y e = ∑ e ∈ piece part i, p y' e := by
  intro y y' i
  obtain ⟨τ, hτ⟩ := htrans y y'
  apply Finset.sum_bij (fun e _ => edgePerm τ e)
  · intro e he
    simp only [piece, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [hpart, he]
  · intro e₁ _ e₂ _ h
    exact (edgePerm τ).injective h
  · intro b hb
    refine ⟨(edgePerm τ).symm b, ?_, ?_⟩
    · simp only [piece, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [← hpart τ ((edgePerm τ).symm b)]
      simpa using hb
    · simp
  · intro e _
    exact hτ e

/-- Fixed source arXiv:1109.5135v1, Lemma 6 (p. 7): if `S_n` acts transitively on the
flows, then the flows are consistent with the outgoing class edge sets `{[u]^+}` and with
the incoming class edge sets `{[u]^-}`. -/
theorem source_lemma_6
    (G : LearningGraph V E Y) (edgePerm : Equiv.Perm V → E ≃ E)
    (hsrc : ∀ (τ : Equiv.Perm V) (e : E), G.src (edgePerm τ e) = τ (G.src e))
    (htgt : ∀ (τ : Equiv.Perm V) (e : E), G.tgt (edgePerm τ e) = τ (G.tgt e))
    (htrans : ∀ y y' : Y, ∃ τ : Equiv.Perm V, ∀ e : E, G.flow y e = G.flow y' (edgePerm τ e)) :
    (∀ (y y' : Y) (u : V),
      (∑ e ∈ piece (fun e => orbitOf (G.src e)) (orbitOf u), G.flow y e) =
      (∑ e ∈ piece (fun e => orbitOf (G.src e)) (orbitOf u), G.flow y' e)) ∧
    (∀ (y y' : Y) (u : V),
      (∑ e ∈ piece (fun e => orbitOf (G.tgt e)) (orbitOf u), G.flow y e) =
      (∑ e ∈ piece (fun e => orbitOf (G.tgt e)) (orbitOf u), G.flow y' e)) := by
  constructor
  · intro y y' u
    exact class_sum_invariant G.flow (fun e => orbitOf (G.src e)) edgePerm
      (fun τ e => by
        change orbitOf (G.src ((edgePerm τ) e)) = orbitOf (G.src e)
        rw [hsrc, orbitOf_perm]) htrans y y' (orbitOf u)
  · intro y y' u
    exact class_sum_invariant G.flow (fun e => orbitOf (G.tgt e)) edgePerm
      (fun τ e => by
        change orbitOf (G.tgt ((edgePerm τ) e)) = orbitOf (G.tgt e)
        rw [htgt, orbitOf_perm]) htrans y y' (orbitOf u)

end Lemma6

end Qatlib.Papers.LearningGraph11.MainResults
