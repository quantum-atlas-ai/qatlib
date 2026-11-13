/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Card

/-!
# Ramsey Threshold Detection via Problem Hamiltonian Ground-State Energy

This module formalizes the clique-plus-independent-set cost function $h(G) = C(G) + I(G)$,
the ground-state energy $E_{\mathrm{gs}}(N, m, n)$ of the diagonal Ramsey problem Hamiltonian,
and the sharp ground-state energy threshold at the classical two-color Ramsey number $R(m, n)$,
including a self-contained proof of Ramsey's theorem (`ramseyNumber_exists`).

## Main statements

* `ramseyProp_iff_groundStateEnergy_pos`: Every $N$-vertex graph contains an $m$-clique or an
  $n$-independent set if and only if $E_{\mathrm{gs}}(N, m, n) > 0$.
* `ramseyNumber_exists`: Existence of finite two-color Ramsey numbers (Erdos-Szekeres recursion).
* `increment_algorithm_gives_ramseyNumber`: $E_{\mathrm{gs}}(N, m, n) = 0$ for all $N < R(m, n)$
  and $E_{\mathrm{gs}}(R(m, n), m, n) > 0$.

## References

* [Gaitan and Clark, 2012][GaitanClark2012]
-/

set_option autoImplicit false

namespace Qatlib.Papers.RamseyAdiab11.MainResults.Threshold

open Finset

/-! ## The cost `h(G) = C(G) + I(G)` -/

variable {V : Type*}

/-- `C(G)`: the number of `m`-cliques in `G` [GaitanClark2012]. -/
noncomputable def cliqueCount [Fintype V] (G : SimpleGraph V) (m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : Finset V => G.IsNClique m S)).card

/-- `I(G)`: the number of `n`-independent sets in `G` [GaitanClark2012]. -/
noncomputable def indepCount [Fintype V] (G : SimpleGraph V) (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun T : Finset V => G.IsNIndepSet n T)).card

/-- Total Ramsey cost `h(G) = C(G) + I(G)` [GaitanClark2012]. -/
noncomputable def h [Fintype V] (G : SimpleGraph V) (m n : ℕ) : ℕ :=
  cliqueCount G m + indepCount G n

/-- `C(G) = 0` iff `G` has no `m`-clique. -/
theorem cliqueCount_eq_zero_iff [Fintype V] (G : SimpleGraph V) (m : ℕ) :
    cliqueCount G m = 0 ↔ ∀ S : Finset V, ¬ G.IsNClique m S := by
  classical
  simp [cliqueCount]

/-- `I(G) = 0` iff `G` has no `n`-independent set. -/
theorem indepCount_eq_zero_iff [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    indepCount G n = 0 ↔ ∀ T : Finset V, ¬ G.IsNIndepSet n T := by
  classical
  simp [indepCount]

/-- `h(G) = 0` iff `G` contains neither an `m`-clique nor an `n`-independent set. -/
theorem h_eq_zero_iff [Fintype V] (G : SimpleGraph V) (m n : ℕ) :
    h G m n = 0 ↔
      (∀ S : Finset V, ¬ G.IsNClique m S) ∧
        (∀ T : Finset V, ¬ G.IsNIndepSet n T) := by
  rw [h, Nat.add_eq_zero_iff, cliqueCount_eq_zero_iff, indepCount_eq_zero_iff]

/-- `0 < h(G)` iff `G` contains an `m`-clique or an `n`-independent set. -/
theorem h_pos_iff [Fintype V] (G : SimpleGraph V) (m n : ℕ) :
    0 < h G m n ↔
      (∃ S : Finset V, G.IsNClique m S) ∨ (∃ T : Finset V, G.IsNIndepSet n T) := by
  constructor
  · intro hp
    by_contra hcon
    rw [not_or, not_exists, not_exists] at hcon
    exact absurd ((h_eq_zero_iff G m n).mpr hcon) (Nat.pos_iff_ne_zero.mp hp)
  · rintro (⟨S, hS⟩ | ⟨T, hT⟩)
    · exact Nat.pos_of_ne_zero fun hz => ((h_eq_zero_iff G m n).mp hz).1 S hS
    · exact Nat.pos_of_ne_zero fun hz => ((h_eq_zero_iff G m n).mp hz).2 T hT

/-! ## Ground-state energy of the problem Hamiltonian -/

section GroundState

variable [Fintype V]

/-- The ground-state energy `E_gs` of the Ramsey problem Hamiltonian: the minimum of `h(G)`
over all graphs on `V` [GaitanClark2012]. -/
noncomputable def groundStateEnergy (m n : ℕ) : ℕ := by
  classical
  haveI : Nonempty (SimpleGraph V) := ⟨⊥⟩
  exact (Finset.univ.image (fun G : SimpleGraph V => h G m n)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- `E_gs = 0` iff some graph has `h(G) = 0`. -/
theorem groundStateEnergy_eq_zero_iff (m n : ℕ) :
    groundStateEnergy (V := V) m n = 0 ↔ ∃ G : SimpleGraph V, h G m n = 0 := by
  classical
  have : Nonempty (SimpleGraph V) := ⟨⊥⟩
  unfold groundStateEnergy
  rw [Finset.min'_eq_iff]
  constructor
  · rintro ⟨hmem, _⟩
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hmem
  · rintro ⟨G, hG⟩
    refine ⟨Finset.mem_image.mpr ⟨G, Finset.mem_univ G, hG⟩, ?_⟩
    intro b hb
    obtain ⟨G', -, rfl⟩ := Finset.mem_image.1 hb
    exact Nat.zero_le _

/-- `0 < E_gs` iff every graph has positive cost. -/
theorem groundStateEnergy_pos_iff (m n : ℕ) :
    0 < groundStateEnergy (V := V) m n ↔ ∀ G : SimpleGraph V, 0 < h G m n := by
  classical
  have : Nonempty (SimpleGraph V) := ⟨⊥⟩
  unfold groundStateEnergy
  rw [Finset.lt_min'_iff]
  constructor
  · intro H G
    exact H (h G m n) (Finset.mem_image.mpr ⟨G, Finset.mem_univ G, rfl⟩)
  · intro H b hb
    obtain ⟨G, -, rfl⟩ := Finset.mem_image.1 hb
    exact H G

end GroundState

/-! ## The Ramsey predicate and the threshold -/

/-- Every `N`-vertex graph contains an `m`-clique or an `n`-independent set. -/
def RamseyProp (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ S : Finset (Fin N), G.IsNClique m S) ∨
      (∃ T : Finset (Fin N), G.IsNIndepSet n T)

/-- An `m`-clique of a pulled-back graph maps to an `m`-clique of the ambient graph. -/
theorem isNClique_map_of_comap {α β : Type*} {G : SimpleGraph β} {f : α ↪ β}
    {m : ℕ} {S : Finset α} (h : (G.comap f).IsNClique m S) :
    G.IsNClique m (S.map f) := by
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun hh => hxy (by rw [hh])
    have hcl := h.isClique
    rw [SimpleGraph.isClique_iff] at hcl
    have := hcl hx' hy' hne
    simpa [SimpleGraph.comap_adj] using this
  · rw [Finset.card_map, h.card_eq]

/-- An `n`-independent set of a pulled-back graph maps to an `n`-independent set of the ambient
graph. -/
theorem isNIndepSet_map_of_comap {α β : Type*} {G : SimpleGraph β} {f : α ↪ β}
    {n : ℕ} {T : Finset α} (h : (G.comap f).IsNIndepSet n T) :
    G.IsNIndepSet n (T.map f) := by
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun hh => hxy (by rw [hh])
    have hind := h.isIndepSet
    rw [SimpleGraph.isIndepSet_iff] at hind
    have := hind hx' hy' hne
    simpa [SimpleGraph.comap_adj] using this
  · rw [Finset.card_map, h.card_eq]

/-- Monotonicity step: if `N` is Ramsey for `(m, n)` then so is `N + 1`. -/
theorem ramseyProp_succ {m n N : ℕ} (h : RamseyProp m n N) : RamseyProp m n (N + 1) := by
  intro G
  have hH := h (G.comap (Fin.castSuccEmb (n := N)))
  rcases hH with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact Or.inl ⟨S.map (Fin.castSuccEmb (n := N)),
      isNClique_map_of_comap (m := m) hS⟩
  · exact Or.inr ⟨T.map (Fin.castSuccEmb (n := N)),
      isNIndepSet_map_of_comap (n := n) hT⟩

/-- `RamseyProp m n` is monotone in `N`. -/
theorem ramseyProp_mono {m n : ℕ} {N M : ℕ} (hNM : N ≤ M) (h : RamseyProp m n N) :
    RamseyProp m n M := by
  induction M, hNM using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact ramseyProp_succ ih

/-- Core dichotomy [GaitanClark2012]: `N` satisfies `RamseyProp m n N` iff the ground-state
energy of `H_P` on `Fin N` is strictly positive. -/
theorem ramseyProp_iff_groundStateEnergy_pos (m n N : ℕ) :
    RamseyProp m n N ↔ 0 < groundStateEnergy (V := Fin N) m n := by
  rw [groundStateEnergy_pos_iff]
  unfold RamseyProp
  constructor
  · intro h G
    rcases h G with ⟨S, hS⟩ | ⟨T, hT⟩
    · exact (h_pos_iff G m n).mpr (Or.inl ⟨S, hS⟩)
    · exact (h_pos_iff G m n).mpr (Or.inr ⟨T, hT⟩)
  · intro h G
    rcases (h_pos_iff G m n).mp (h G) with ⟨S, hS⟩ | ⟨T, hT⟩
    · exact Or.inl ⟨S, hS⟩
    · exact Or.inr ⟨T, hT⟩

private theorem ramseyNumber_exists_aux :
    ∀ s m n : ℕ, m + n = s → ∃ N : ℕ, RamseyProp m n N
  | 0, m, n, hs => by
    have hm : m = 0 := by omega
    subst hm
    exact ⟨0, fun _ => Or.inl ⟨∅, by simp [SimpleGraph.isNClique_iff]⟩⟩
  | _ + 1, 0, _, _ =>
    ⟨0, fun _ => Or.inl ⟨∅, by simp [SimpleGraph.isNClique_iff]⟩⟩
  | _ + 1, _ + 1, 0, _ =>
    ⟨0, fun _ => Or.inr ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
  | s + 1, m + 1, n + 1, hs => by
    classical
    obtain ⟨N₁, hN₁⟩ := ramseyNumber_exists_aux s m (n + 1) (by omega)
    obtain ⟨N₂, hN₂⟩ := ramseyNumber_exists_aux s (m + 1) n (by omega)
    refine ⟨N₁ + N₂ + 1, ?_⟩
    intro G
    let v₀ : Fin (N₁ + N₂ + 1) := ⟨0, by omega⟩
    let U : Finset (Fin (N₁ + N₂ + 1)) := Finset.univ.erase v₀
    have hUcard : U.card = N₁ + N₂ := by
      simp [U, Finset.card_erase_of_mem (Finset.mem_univ v₀)]
    let A : Finset (Fin (N₁ + N₂ + 1)) := U.filter (fun u => G.Adj v₀ u)
    let B : Finset (Fin (N₁ + N₂ + 1)) := U.filter (fun u => ¬ G.Adj v₀ u)
    have hAB : A.card + B.card = N₁ + N₂ := by
      have hpart := Finset.card_filter_add_card_filter_not (s := U) (p := fun u => G.Adj v₀ u)
      simpa [A, B, hUcard] using hpart
    rcases (by omega : N₁ ≤ A.card ∨ N₂ ≤ B.card) with hA | hB
    · have hRA : RamseyProp m (n + 1) A.card := ramseyProp_mono hA hN₁
      let fA : Fin A.card ↪ Fin (N₁ + N₂ + 1) :=
        (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm.toEmbedding.trans
          (Function.Embedding.subtype _)
      have hfA_mem : ∀ x : Fin A.card, fA x ∈ A := fun x =>
        ((Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm x).2
      rcases hRA (G.comap fA) with ⟨S, hS⟩ | ⟨T, hT⟩
      · refine Or.inl ⟨insert v₀ (S.map fA), ?_⟩
        have hS' : G.IsNClique m (S.map fA) := isNClique_map_of_comap hS
        have hv₀_not : v₀ ∉ S.map fA := by
          intro hv
          obtain ⟨x, -, hx⟩ := Finset.mem_map.mp hv
          have hxA := (Finset.mem_filter.mp (hfA_mem x)).1
          exact (Finset.mem_erase.mp hxA).1 hx
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.isClique_iff]
          intro x hx y hy hxy
          rw [Finset.mem_coe, Finset.mem_insert] at hx hy
          rcases hx with rfl | hxS
          · rcases hy with rfl | hyS
            · exact (hxy rfl).elim
            · obtain ⟨y', -, rfl⟩ := Finset.mem_map.mp hyS
              exact (Finset.mem_filter.mp (hfA_mem y')).2
          · rcases hy with rfl | hyS
            · obtain ⟨x', -, rfl⟩ := Finset.mem_map.mp hxS
              exact ((Finset.mem_filter.mp (hfA_mem x')).2).symm
            · exact hS'.isClique hxS hyS hxy
        · rw [Finset.card_insert_of_notMem hv₀_not, hS'.card_eq]
      · exact Or.inr ⟨T.map fA, isNIndepSet_map_of_comap hT⟩
    · have hRB : RamseyProp (m + 1) n B.card := ramseyProp_mono hB hN₂
      let fB : Fin B.card ↪ Fin (N₁ + N₂ + 1) :=
        (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm.toEmbedding.trans
          (Function.Embedding.subtype _)
      have hfB_mem : ∀ x : Fin B.card, fB x ∈ B := fun x =>
        ((Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm x).2
      rcases hRB (G.comap fB) with ⟨S, hS⟩ | ⟨T, hT⟩
      · exact Or.inl ⟨S.map fB, isNClique_map_of_comap hS⟩
      · refine Or.inr ⟨insert v₀ (T.map fB), ?_⟩
        have hT' : G.IsNIndepSet n (T.map fB) := isNIndepSet_map_of_comap hT
        have hv₀_not : v₀ ∉ T.map fB := by
          intro hv
          obtain ⟨x, -, hx⟩ := Finset.mem_map.mp hv
          have hxB := (Finset.mem_filter.mp (hfB_mem x)).1
          exact (Finset.mem_erase.mp hxB).1 hx
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.isIndepSet_iff]
          intro x hx y hy hxy
          rw [Finset.mem_coe, Finset.mem_insert] at hx hy
          rcases hx with rfl | hxT
          · rcases hy with rfl | hyT
            · exact (hxy rfl).elim
            · obtain ⟨y', -, rfl⟩ := Finset.mem_map.mp hyT
              exact (Finset.mem_filter.mp (hfB_mem y')).2
          · rcases hy with rfl | hyT
            · obtain ⟨x', -, rfl⟩ := Finset.mem_map.mp hxT
              exact fun hadj => (Finset.mem_filter.mp (hfB_mem x')).2 hadj.symm
            · exact hT'.isIndepSet hxT hyT hxy
        · rw [Finset.card_insert_of_notMem hv₀_not, hT'.card_eq]

/-- Existence of finite two-color Ramsey numbers (Erdos-Szekeres theorem). -/
theorem ramseyNumber_exists (m n : ℕ) : ∃ N : ℕ, RamseyProp m n N :=
  ramseyNumber_exists_aux (m + n) m n rfl

/-- `R(m, n)`, the Ramsey number, defined as the least `N` satisfying `RamseyProp m n N`
[GaitanClark2012]. -/
noncomputable def ramseyNumber (m n : ℕ) : ℕ := by
  classical
  exact Nat.find (ramseyNumber_exists m n)

/-- `ramseyNumber m n` satisfies `RamseyProp m n`. -/
theorem ramseyNumber_spec (m n : ℕ) : RamseyProp m n (ramseyNumber m n) := by
  classical
  exact Nat.find_spec (ramseyNumber_exists m n)

/-- Minimality: no `N < R(m, n)` satisfies `RamseyProp m n N`. -/
theorem ramseyNumber_min (m n : ℕ) {N : ℕ} (hN : N < ramseyNumber m n) :
    ¬ RamseyProp m n N := by
  classical
  exact Nat.find_min (ramseyNumber_exists m n) hN

/-- `N < R(m, n)` iff `N` is not Ramsey for `(m, n)`. -/
theorem lt_ramseyNumber_iff (m n N : ℕ) :
    N < ramseyNumber m n ↔ ¬ RamseyProp m n N := by
  constructor
  · exact ramseyNumber_min m n
  · intro h
    by_contra hge
    rw [not_lt] at hge
    exact h (ramseyProp_mono hge (ramseyNumber_spec m n))

/-- `R(m, n) ≤ N` iff `N` is Ramsey for `(m, n)`. -/
theorem ramseyNumber_le_iff (m n N : ℕ) :
    ramseyNumber m n ≤ N ↔ RamseyProp m n N := by
  constructor
  · intro hh
    exact ramseyProp_mono hh (ramseyNumber_spec m n)
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    exact (lt_ramseyNumber_iff m n N).mp hlt h

/-- Below threshold `N < R(m, n)`, the ground-state energy vanishes [GaitanClark2012]. -/
theorem below_threshold_energy_zero (m n N : ℕ) (h : N < ramseyNumber m n) :
    groundStateEnergy (V := Fin N) m n = 0 := by
  have hnot : ¬ RamseyProp m n N := (lt_ramseyNumber_iff m n N).mp h
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact hnot ((ramseyProp_iff_groundStateEnergy_pos m n N).mpr hpos)

/-- At or above threshold `R(m, n) ≤ N`, the ground-state energy is strictly positive
[GaitanClark2012]. -/
theorem at_or_above_threshold_energy_pos (m n N : ℕ) (h : ramseyNumber m n ≤ N) :
    0 < groundStateEnergy (V := Fin N) m n :=
  (ramseyProp_iff_groundStateEnergy_pos m n N).mp
    ((ramseyNumber_le_iff m n N).mp h)

/-- Increment threshold detection [GaitanClark2012]: the ground-state energy is zero for every
`N < R(m, n)` and strictly positive at `N = R(m, n)`. -/
theorem increment_algorithm_gives_ramseyNumber (m n : ℕ) :
    (∀ N : ℕ, N < ramseyNumber m n → groundStateEnergy (V := Fin N) m n = 0) ∧
      0 < groundStateEnergy (V := Fin (ramseyNumber m n)) m n :=
  ⟨fun N hN => below_threshold_energy_zero m n N hN,
    at_or_above_threshold_energy_pos m n (ramseyNumber m n) le_rfl⟩

end Qatlib.Papers.RamseyAdiab11.MainResults.Threshold
