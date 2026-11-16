/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LearningGraph11.MainResults.Lemma6SymmetryConsistency
public import Mathlib.Tactic.NormNum

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Lemma 7: uniformity of the incoming flow on a class

Fixed source: arXiv:1109.5135v3, Lemma 7 and its proof (p. 8), including
Equations (3) and (4).
PDF SHA-256: `75dceb2759e10a2fd22f4d63e69af9e9327f01afbf8e06c69c73c6ff894f0574`.
The originally cited v1 has no Lemma 7; the matching statement is in v3.

Let `S_n` act transitively on the flows and suppose that (1) for every `L`-vertex `u`
with positive incoming flow the flow leaves `u` uniformly along `g⁺([u])` outgoing
edges, and (2) for every `w` the number of incoming edges from `[w]` to `u` is
`g⁻([w],[u])`. Then for every `u` the flow entering `[u]` is uniformly distributed over
`W_{y,[u]} ⊆ [u]`, and `|W_{y,[u]}|` is independent of `y`.

The auxiliary results isolate the paper's uniformity endgame. The source model does
not encode rooted acyclicity or flow conservation, so outgoing-degree conditions
alone do not imply uniform incoming flow. The final theorem therefore requires
invariance of each edge flow under the given permutation action.

The imported `orbitOf` uses all permutations of the abstract vertex set.  The
results here concern that finite symmetry model; they do not construct the
paper's action on labelled graph vertices or its rooted-DAG level induction.
In particular, the repaired theorem's per-flow invariance is stronger than the
source's transitivity between different flows.  No full Lemma 7 coverage is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults
open Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

variable {V E Y : Type*} [Fintype V] [Fintype E] [Fintype Y] [DecidableEq V]

/-- The incoming edge set `u⁻ = {e : tgt e = u}` of an `L`-vertex (p. 7). -/
def incoming (G : LearningGraph V E Y) (u : V) : Finset E :=
  Finset.univ.filter (fun e => G.tgt e = u)

/-- The outgoing edge set `u⁺ = {e : src e = u}` of an `L`-vertex (p. 7). -/
def outgoing (G : LearningGraph V E Y) (u : V) : Finset E :=
  Finset.univ.filter (fun e => G.src e = u)

/-- The incoming flow `p_y(u⁻) = ∑_{e : tgt e = u} p_y(e)`. -/
def inflowAt (G : LearningGraph V E Y) (p : E → ℝ) (u : V) : ℝ :=
  ∑ e ∈ incoming G u, p e

/-- The `mem_incoming` result for the LearningGraph11 paper model. -/
theorem mem_incoming {G : LearningGraph V E Y} {u : V} {e : E} :
    e ∈ incoming G u ↔ G.tgt e = u := by
  simp [incoming]

/-- The `mem_outgoing` result for the LearningGraph11 paper model. -/
theorem mem_outgoing {G : LearningGraph V E Y} {u : V} {e : E} :
    e ∈ outgoing G u ↔ G.src e = u := by
  simp [outgoing]

/-- The incoming flow is nonnegative for a nonnegative flow. -/
theorem inflowAt_nonneg (G : LearningGraph V E Y) {p : E → ℝ} (hp : ∀ e, 0 ≤ p e)
    (u : V) : 0 ≤ inflowAt G p u := by
  apply Finset.sum_nonneg
  intro e _
  exact hp e

/-- Transitivity of the flows rewrites an incoming flow at `v` as the incoming flow at
`τ v`. -/
theorem inflowAt_transitive
    (G : LearningGraph V E Y) (edgePerm : Equiv.Perm V → E ≃ E)
    (htgt : ∀ (τ : Equiv.Perm V) (e : E), G.tgt (edgePerm τ e) = τ (G.tgt e))
    {p q : E → ℝ} {τ : Equiv.Perm V} (hτ : ∀ e, p e = q (edgePerm τ e)) (v : V) :
    inflowAt G p v = inflowAt G q (τ v) := by
  unfold inflowAt incoming
  apply Finset.sum_bij (fun e _ => edgePerm τ e)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [htgt, he]
  · intro a _ b _ h
    exact (edgePerm τ).injective h
  · intro b hb
    refine ⟨(edgePerm τ).symm b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      have h : G.tgt b = τ (G.tgt ((edgePerm τ).symm b)) := by
        have := htgt τ ((edgePerm τ).symm b)
        simpa using this
      exact τ.injective (by rw [← h, hb])
    · simp
  · intro e _
    exact hτ e

/-- `v ∈ [u]` iff `v` has the same orbit class as `u`. -/
theorem orbitOf_eq_iff {u v : V} : orbitOf v = orbitOf u ↔ v ∈ orbitOf u := by
  constructor
  · intro h
    rw [← h]
    exact mem_orbitOf.mpr ⟨Equiv.refl V, rfl⟩
  · intro h
    obtain ⟨σ, hσ⟩ := mem_orbitOf.mp h
    rw [← hσ]
    exact orbitOf_perm σ u

/-- The number of vertices of a class carrying positive incoming flow does not depend on
the flow (transitivity of the flows moves `W_y` bijectively onto `W_{y'}`). -/
theorem card_positive_inflow_class_indep
    (G : LearningGraph V E Y) (edgePerm : Equiv.Perm V → E ≃ E)
    (htgt : ∀ (τ : Equiv.Perm V) (e : E), G.tgt (edgePerm τ e) = τ (G.tgt e))
    (htrans : ∀ y y' : Y, ∃ τ : Equiv.Perm V, ∀ e : E, G.flow y e = G.flow y' (edgePerm τ e))
    (y y' : Y) (u : V) :
    (Finset.univ.filter (fun v : V => v ∈ orbitOf u ∧ 0 < inflowAt G (G.flow y) v)).card =
      (Finset.univ.filter (fun v : V => v ∈ orbitOf u ∧ 0 < inflowAt G (G.flow y') v)).card := by
  set s : Finset V := Finset.univ.filter (fun v => v ∈ orbitOf u ∧ 0 < inflowAt G (G.flow y) v)
  set t : Finset V := Finset.univ.filter (fun v => v ∈ orbitOf u ∧ 0 < inflowAt G (G.flow y') v)
  have hle : s.card ≤ t.card := by
    obtain ⟨τ, hτ⟩ := htrans y y'
    have hsub : s.image (fun v => τ v) ⊆ t := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [← orbitOf_eq_iff] at ha ⊢
        rw [orbitOf_perm]
        exact ha.1
      · rw [← inflowAt_transitive G edgePerm htgt hτ a]
        exact ha.2
    calc s.card = (s.image (fun v => τ v)).card :=
          (Finset.card_image_of_injective s τ.injective).symm
      _ ≤ t.card := Finset.card_le_card hsub
  have hle' : t.card ≤ s.card := by
    obtain ⟨σ, hσ⟩ := htrans y' y
    have hsub : t.image (fun v => σ v) ⊆ s := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [← orbitOf_eq_iff] at ha ⊢
        rw [orbitOf_perm]
        exact ha.1
      · rw [← inflowAt_transitive G edgePerm htgt hσ a]
        exact ha.2
    calc t.card = (t.image (fun v => σ v)).card :=
          (Finset.card_image_of_injective t σ.injective).symm
      _ ≤ s.card := Finset.card_le_card hsub
  exact le_antisymm hle hle'

/-- Endgame of Lemma 7 (arXiv:1109.5135v3, p. 8): once the incoming flow at a vertex is
known to depend only on its class, transitivity makes the class's positive-inflow set
`W_{y,[u]}` flow-independent in size, and the flow is uniform on it. -/
theorem uniform_inflow_of_class_constant
    (G : LearningGraph V E Y) (edgePerm : Equiv.Perm V → E ≃ E)
    (htgt : ∀ (τ : Equiv.Perm V) (e : E), G.tgt (edgePerm τ e) = τ (G.tgt e))
    (htrans : ∀ y y' : Y, ∃ τ : Equiv.Perm V, ∀ e : E, G.flow y e = G.flow y' (edgePerm τ e))
    (hconst : ∀ (y : Y) (u u' : V), orbitOf u' = orbitOf u →
      inflowAt G (G.flow y) u' = inflowAt G (G.flow y) u)
    (y0 : Y) :
    ∃ c : Finset V → ℕ, ∀ (y : Y) (u : V), 0 < inflowAt G (G.flow y) u →
      ∃ W : Finset V, W ⊆ orbitOf u ∧ W.card = c (orbitOf u) ∧ 0 < c (orbitOf u) ∧
        (∀ v ∈ W, inflowAt G (G.flow y) v = inflowAt G (G.flow y) u) ∧
        (∀ v ∈ orbitOf u, v ∉ W → inflowAt G (G.flow y) v = 0) := by
  refine ⟨fun i => (Finset.univ.filter
    (fun v : V => v ∈ i ∧ 0 < inflowAt G (G.flow y0) v)).card, ?_⟩
  intro y u hu
  have hpos0 : 0 < inflowAt G (G.flow y0) u := by
    obtain ⟨τ, hτ⟩ := htrans y y0
    have h1 : inflowAt G (G.flow y) u = inflowAt G (G.flow y0) (τ u) :=
      inflowAt_transitive G edgePerm htgt hτ u
    have h2 : inflowAt G (G.flow y0) (τ u) = inflowAt G (G.flow y0) u :=
      hconst y0 u (τ u) (orbitOf_perm τ u)
    rw [h1, h2] at hu
    exact hu
  refine ⟨Finset.univ.filter (fun v : V => v ∈ orbitOf u ∧ 0 < inflowAt G (G.flow y) v),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hv.1
  · exact card_positive_inflow_class_indep G edgePerm htgt htrans y y0 u
  · refine Finset.card_pos.mpr ⟨u, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨mem_orbitOf.mpr ⟨Equiv.refl V, rfl⟩, hpos0⟩
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hconst y u v (orbitOf_eq_iff.mpr hv.1)
  · intro v hv hvW
    have hnot : ¬ (0 < inflowAt G (G.flow y) v) := by
      intro hpos
      exact hvW (by simp [hv, hpos])
    have hnonneg := inflowAt_nonneg G (fun e => G.flow_nonneg y e) v
    have hzero : inflowAt G (G.flow y) v ≤ 0 := not_lt.mp hnot
    exact le_antisymm hzero hnonneg

/-- Uniformity endgame related to arXiv:1109.5135v3, Lemma 7 (p. 8).
Each flow is invariant under the edge action, and target equivariance transfers this
invariance to incoming flow. This explicit symmetry premise replaces the insufficient
outgoing-degree conditions of the ungraded, nonconservative source model. -/
theorem source_lemma_7
    (G : LearningGraph V E Y) (edgePerm : Equiv.Perm V → E ≃ E)
    (htgt : ∀ (τ : Equiv.Perm V) (e : E), G.tgt (edgePerm τ e) = τ (G.tgt e))
    (hinvariant : ∀ (y : Y) (τ : Equiv.Perm V) (e : E),
      G.flow y e = G.flow y (edgePerm τ e)) :
    ∃ c : Finset V → ℕ, ∀ (y : Y) (u : V), 0 < inflowAt G (G.flow y) u →
      ∃ W : Finset V, W ⊆ orbitOf u ∧ W.card = c (orbitOf u) ∧ 0 < c (orbitOf u) ∧
        (∀ v ∈ W, inflowAt G (G.flow y) v = inflowAt G (G.flow y) u) ∧
        (∀ v ∈ orbitOf u, v ∉ W → inflowAt G (G.flow y) v = 0) := by
  classical
  have hconst : ∀ (y : Y) (u u' : V), orbitOf u' = orbitOf u →
      inflowAt G (G.flow y) u' = inflowAt G (G.flow y) u := by
    intro y u u' hu
    obtain ⟨τ, hτ⟩ := mem_orbitOf.mp (orbitOf_eq_iff.mp hu)
    rw [← hτ]
    exact (inflowAt_transitive G edgePerm htgt (hinvariant y τ) u).symm
  refine ⟨Finset.card, ?_⟩
  intro y u hu
  let W := Finset.univ.filter
    (fun v : V => v ∈ orbitOf u ∧ 0 < inflowAt G (G.flow y) v)
  have hW : W = orbitOf u := by
    ext v
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.left
    · intro hv
      refine ⟨hv, ?_⟩
      rw [hconst y u v (orbitOf_eq_iff.mpr hv)]
      exact hu
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW]
  · rw [hW]
  · rw [← hW]
    exact Finset.card_pos.mpr ⟨u, by
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨mem_orbitOf.mpr ⟨Equiv.refl V, rfl⟩, hu⟩⟩
  · intro v hv
    rw [hW] at hv
    exact hconst y u v (orbitOf_eq_iff.mpr hv)
  · intro v hv hnot
    rw [hW] at hnot
    exact False.elim (hnot hv)

/-- Two self-loops with equal positive flow satisfy the repaired symmetry premises.
This witnesses satisfiability of the finite model, without asserting a rooted DAG. -/
theorem uniform_loop_example :
    ∃ G : LearningGraph Bool Bool Unit,
      (∀ (τ : Equiv.Perm Bool) (e : Bool), G.tgt (τ e) = τ (G.tgt e)) ∧
      (∀ (y : Unit) (τ : Equiv.Perm Bool) (e : Bool),
        G.flow y e = G.flow y (τ e)) ∧
      inflowAt G (G.flow ()) false = (1 / 2 : ℝ) ∧
      inflowAt G (G.flow ()) true = (1 / 2 : ℝ) := by
  let G : LearningGraph Bool Bool Unit := {
    src := id
    tgt := id
    level := fun _ => 0
    weight := fun _ => 1
    len := fun _ => 1
    flow := fun _ _ => 1 / 2
    weight_pos := fun _ => by norm_num
    flow_nonneg := fun _ _ => by norm_num
    stage_flow := by intro y; norm_num [Fintype.sum_bool]
  }
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro τ e
    rfl
  · intro y τ e
    rfl
  · norm_num [inflowAt, incoming, G, Finset.sum_filter, Fintype.sum_bool]
    decide
  · norm_num [inflowAt, incoming, G, Finset.sum_filter, Fintype.sum_bool]
    decide

end Qatlib.Papers.LearningGraph11.MainResults
