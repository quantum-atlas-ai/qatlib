/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Adjacent particle exchanges on the path

The vertices are occupied-site subsets. A move exchanges an occupied and an
unoccupied adjacent site. Equal-cardinality subsets are connected because
adjacent transpositions generate every finite permutation. The parity of the
sum of occupied positions changes along each move, giving a bipartition.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.PathModel

/-- Exchange the labels on the adjacent sites indexed by `i`. -/
def flip {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N) : Finset (Fin (N + 1)) :=
  v.map (Equiv.swap i.castSucc i.succ).toEmbedding

/-- An actual particle-hole exchange, retaining both its generator and output. -/
def Hop {N : ℕ} (v w : Finset (Fin (N + 1))) : Prop :=
  ∃ i : Fin N, (i.castSucc ∈ v) ≠ (i.succ ∈ v) ∧ w = flip v i

/-- The sum of the occupied positions. -/
def positionSum {N : ℕ} (v : Finset (Fin (N + 1))) : ℕ := ∑ x ∈ v, x.val

/-- The parity coloring of occupied-site subsets. -/
def color {N : ℕ} (v : Finset (Fin (N + 1))) : Bool :=
  decide (positionSum v % 2 = 0)

/-- An exchange preserves the particle number exactly. -/
theorem flip_card {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N) :
    (flip v i).card = v.card := Finset.card_map _

/-- A transposition between an occupied and an empty site removes and inserts one site. -/
theorem flip_right {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N)
    (hi : i.castSucc ∈ v) (hj : i.succ ∉ v) :
    flip v i = insert i.succ (v.erase i.castSucc) := by
  ext x
  simp only [flip, Finset.mem_map_equiv, Equiv.symm_swap, Finset.mem_insert,
    Finset.mem_erase]
  by_cases hxi : x = i.castSucc
  · subst x
    simp [hi, hj]
    exact fun h => hj (h ▸ hi)
  by_cases hxj : x = i.succ
  · subst x
    simp [hi]
  simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

/-- The reverse adjacent exchange inserts the left site. -/
theorem flip_left {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N)
    (hi : i.castSucc ∉ v) (hj : i.succ ∈ v) :
    flip v i = insert i.castSucc (v.erase i.succ) := by
  ext x
  simp only [flip, Finset.mem_map_equiv, Equiv.symm_swap, Finset.mem_insert,
    Finset.mem_erase]
  by_cases hxi : x = i.castSucc
  · subst x
    simp [hj]
  by_cases hxj : x = i.succ
  · subst x
    simp [hi, hj, hxi]
  simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

/-- Exchanging equally occupied sites leaves the subset unchanged. -/
theorem flip_fixed {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N)
    (h : (i.castSucc ∈ v) = (i.succ ∈ v)) : flip v i = v := by
  ext x
  simp only [flip, Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hxi : x = i.castSucc
  · subst x
    simpa only [Equiv.swap_apply_left] using h.symm.to_iff
  by_cases hxj : x = i.succ
  · subst x
    simpa only [Equiv.swap_apply_right] using h.to_iff
  simp only [Equiv.swap_apply_of_ne_of_ne hxi hxj]

/-- Every adjacent permutation is either a genuine move or a stationary step. -/
theorem flip_reachable {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N) :
    Relation.ReflTransGen Hop v (flip v i) := by
  by_cases h : (i.castSucc ∈ v) = (i.succ ∈ v)
  · rw [flip_fixed v i h]
  · exact Relation.ReflTransGen.single ⟨i, h, rfl⟩

/-- Adjacent exchanges realize every finite permutation as an actual path. -/
theorem perm_reachable {N : ℕ} (e : Equiv.Perm (Fin (N + 1)))
    (v : Finset (Fin (N + 1))) :
    Relation.ReflTransGen Hop v (v.map e.toEmbedding) := by
  have he : e ∈ Submonoid.closure
      (Set.range fun i : Fin N => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top e
  induction he using Submonoid.closure_induction generalizing v with
  | mem e he =>
    obtain ⟨i, rfl⟩ := he
    exact flip_reachable v i
  | one =>
    simpa only [Equiv.Perm.one_def, Equiv.refl_toEmbedding, Finset.map_refl] using
      (Relation.ReflTransGen.refl : Relation.ReflTransGen Hop v v)
  | mul e f _ _ he hf =>
    have hpath := (hf v).trans (he (v.map f.toEmbedding))
    convert hpath using 1
    rw [Finset.map_map]
    congr 1

/-- Any two vertices in a fixed particle sector are joined by adjacent exchanges. -/
theorem connected {N : ℕ} (v w : Finset (Fin (N + 1))) (h : v.card = w.card) :
    Relation.ReflTransGen Hop v w := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq v w h
  simpa only [he] using perm_reachable e v

/-- Moving a particle one site right increases the occupied-position sum by one. -/
theorem sum_flip_right {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N)
    (hi : i.castSucc ∈ v) (hj : i.succ ∉ v) :
    positionSum (flip v i) = positionSum v + 1 := by
  rw [flip_right v i hi hj]
  unfold positionSum
  rw [Finset.sum_insert (by simp only [Finset.mem_erase]; exact fun h => hj h.2)]
  have hs := Finset.sum_erase_add (s := v) (f := fun x : Fin (N + 1) => x.val) hi
  simp only [Fin.val_castSucc, Fin.val_succ] at hs ⊢
  omega

/-- Moving a particle one site left decreases that sum by one. -/
theorem sum_flip_left {N : ℕ} (v : Finset (Fin (N + 1))) (i : Fin N)
    (hi : i.castSucc ∉ v) (hj : i.succ ∈ v) :
    positionSum v = positionSum (flip v i) + 1 := by
  rw [flip_left v i hi hj]
  unfold positionSum
  rw [Finset.sum_insert (by simp only [Finset.mem_erase]; exact fun h => hi h.2)]
  have hs := Finset.sum_erase_add (s := v) (f := fun x : Fin (N + 1) => x.val) hj
  simp only [Fin.val_castSucc, Fin.val_succ] at hs ⊢
  omega

/-- The parity color changes at every genuine particle-hole exchange. -/
theorem hop_color {N : ℕ} {v w : Finset (Fin (N + 1))} (h : Hop v w) :
    color v ≠ color w := by
  obtain ⟨i, hxor, rfl⟩ := h
  have hs : positionSum (flip v i) = positionSum v + 1 ∨
      positionSum v = positionSum (flip v i) + 1 := by
    by_cases hi : i.castSucc ∈ v
    · left
      exact sum_flip_right v i hi (fun hj => hxor (by simp [hi, hj]))
    · right
      have hj : i.succ ∈ v := by
        by_contra hj
        exact hxor (by simp [hi, hj])
      exact sum_flip_left v i hi hj
  unfold color
  by_cases hv : positionSum v % 2 = 0 <;>
    by_cases hw : positionSum (flip v i) % 2 = 0
  · omega
  · simp only [hv, hw, decide_true, decide_false]
    decide
  · simp only [hv, hw, decide_true, decide_false]
    decide
  · omega

end Qatlib.Papers.KhovanovHom25.MainResults.PathModel
