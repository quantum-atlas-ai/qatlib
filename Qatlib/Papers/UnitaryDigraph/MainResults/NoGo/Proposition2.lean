/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Order.Preorder.Finite
import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
import Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular
import Qatlib.Papers.UnitaryDigraph.MainResults.Permutation

/-!
# Looped paths, cycles, and directed-tree obstructions

This module establishes cases of Proposition 2 of [Severini2003]: looped paths with at least
three vertices, cycles with at least five vertices, and finite nonempty directed trees do not
support unitary matrices. The arguments use outgoing quadrangularity or a vertex with no
outgoing neighbors and extend to permutation-equivalent digraphs.

## Main statements

* `proposition2_pathLoops`: The looped-path obstruction.
* `proposition2_nCycle`: The cycle obstruction for at least five vertices.
* `proposition2_directedTree`: The finite nonempty directed-tree obstruction.

## References

* [Severini, 2003][Severini2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.NoGo

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular
open Qatlib.Papers.UnitaryDigraph.MainResults.Permutation
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs.Digraph

/-- For `n ≥ 3`, vertices zero and two of `nPathLoops n` have exactly vertex one as a common
outgoing neighbor. -/
theorem nPathLoops_inter {n : ℕ} (hn : 3 ≤ n) :
    ((nPathLoops n).outNbrs ⟨0, by omega⟩ ∩ (nPathLoops n).outNbrs ⟨2, by omega⟩)
      = ({⟨1, by omega⟩} : Set (Fin n)) := by
  ext j
  rw [Set.mem_inter_iff, mem_outNbrs, mem_outNbrs]
  simp only [nPathLoops, Set.mem_singleton_iff, Fin.ext_iff]
  constructor
  · rintro ⟨h0, h2⟩
    have h1 : j.val = 1 := by
      rcases h0 with h0 | h0 | h0 <;> rcases h2 with h2 | h2 | h2 <;> omega
    exact h1
  · rintro hj
    constructor <;> simp [hj]

/-- For `n ≥ 3`, the looped path fails outgoing quadrangularity. -/
theorem nPathLoops_not_outQuadrangular {n : ℕ} (hn : 3 ≤ n) :
    ¬ OutQuadrangular (nPathLoops n) := by
  intro h
  have hcard : ((nPathLoops n).outNbrs ⟨0, by omega⟩ ∩
      (nPathLoops n).outNbrs ⟨2, by omega⟩).ncard = 1 := by
    rw [nPathLoops_inter hn, Set.ncard_singleton]
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro he
    have := congrArg Fin.val he
    simp at this
  exact h ⟨0, by omega⟩ ⟨2, by omega⟩ hne hcard

/-- For `n ≥ 3`, the looped path is not a unitary digraph [Severini2003]. -/
theorem nPathLoops_not_unitary {n : ℕ} (hn : 3 ≤ n) : ¬ IsUnitaryDigraph (nPathLoops n) :=
  fun hU => nPathLoops_not_outQuadrangular hn (outQuadrangular_of_isUnitaryDigraph _ hU)

/-- A digraph permutation equivalent to a looped path on at least three vertices is not unitary
[Severini2003]. -/
theorem proposition2_pathLoops {V : Type} [Fintype V] [DecidableEq V]
    (D : Defs.Digraph V) (n : ℕ)
    (hn : 3 ≤ n) (h : PermEquivalentTo D (nPathLoops n)) : ¬ IsUnitaryDigraph D := by
  intro hUD
  exact nPathLoops_not_unitary hn ((lemma2 h).mp hUD)

/-- For `m < n`, the successor of `m` is zero modulo `n` exactly when `m + 1 = n`. -/
theorem modSucc_eq_zero_iff {n m : ℕ} (hm : m < n) : (m + 1) % n = 0 ↔ m + 1 = n := by
  have hle : m + 1 ≤ n := by omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · exact ⟨fun _ => heq, fun h => by rw [h, Nat.mod_self]⟩

/-- For `n ≥ 3` and `m < n`, the successor of `m` is two modulo `n` exactly when `m = 1`. -/
theorem modSucc_eq_two_iff {n m : ℕ} (hn : 3 ≤ n) (hm : m < n) : (m + 1) % n = 2 ↔ m = 1 := by
  have hle : m + 1 ≤ n := by omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · rw [heq, Nat.mod_self]; omega

/-- For `n ≥ 5`, vertices zero and two of `nCycle n` have exactly vertex one as a common
outgoing neighbor. -/
theorem nCycle_inter {n : ℕ} (hn : 5 ≤ n) :
    ((nCycle n).outNbrs ⟨0, by omega⟩ ∩ (nCycle n).outNbrs ⟨2, by omega⟩)
      = ({⟨1, by omega⟩} : Set (Fin n)) := by
  ext j
  rw [Set.mem_inter_iff, mem_outNbrs, mem_outNbrs, Set.mem_singleton_iff, Fin.ext_iff]
  simp only [nCycle]
  have h0a : (0 + 1) % n = j.val ↔ j.val = 1 := by
    rw [show (0 + 1) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
  have h0b : (j.val + 1) % n = 0 ↔ j.val + 1 = n := modSucc_eq_zero_iff j.isLt
  have h2a : (2 + 1) % n = j.val ↔ j.val = 3 := by
    rw [show (2 + 1) = 3 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
  have h2b : (j.val + 1) % n = 2 ↔ j.val = 1 := modSucc_eq_two_iff (by omega) j.isLt
  rw [h0a, h0b, h2a, h2b]
  constructor
  · rintro ⟨h0, h2⟩
    rcases h2 with h2 | h2
    · rcases h0 with h0 | h0 <;> omega
    · exact h2
  · intro h
    exact ⟨Or.inl h, Or.inr h⟩

/-- For `n ≥ 5`, `nCycle n` fails outgoing quadrangularity. -/
theorem nCycle_not_outQuadrangular {n : ℕ} (hn : 5 ≤ n) : ¬ OutQuadrangular (nCycle n) := by
  intro h
  have hcard : ((nCycle n).outNbrs ⟨0, by omega⟩ ∩
      (nCycle n).outNbrs ⟨2, by omega⟩).ncard = 1 := by
    rw [nCycle_inter hn, Set.ncard_singleton]
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro he
    have := congrArg Fin.val he
    simp at this
  exact h ⟨0, by omega⟩ ⟨2, by omega⟩ hne hcard

/-- For `n ≥ 5`, `nCycle n` is not a unitary digraph [Severini2003]. -/
theorem nCycle_not_unitary {n : ℕ} (hn : 5 ≤ n) : ¬ IsUnitaryDigraph (nCycle n) :=
  fun hU => nCycle_not_outQuadrangular hn (outQuadrangular_of_isUnitaryDigraph _ hU)

/-- A digraph permutation equivalent to `nCycle n` with `n ≥ 5` is not unitary [Severini2003]. -/
theorem proposition2_nCycle {V : Type} [Fintype V] [DecidableEq V] (D : Defs.Digraph V) (n : ℕ)
    (hn : 5 ≤ n) (h : PermEquivalentTo D (nCycle n)) : ¬ IsUnitaryDigraph D := by
  intro hUD
  exact nCycle_not_unitary hn ((lemma2 h).mp hUD)

/-- A finite nonempty digraph in which every vertex has an outgoing neighbor has a directed
cycle. -/
theorem hasDirectedCycle_of_forall_outNbrs_nonempty {V : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] (D : Defs.Digraph V) (hne : ∀ v, (D.outNbrs v).Nonempty) :
    HasDirectedCycle D := by
  classical
  let f : V → V := fun v => Classical.choose (hne v)
  have hf : ∀ v, D.Adj v (f v) := fun v => mem_outNbrs.mp (Classical.choose_spec (hne v))
  let x : V := Classical.arbitrary V
  let seq : ℕ → V := fun n => f^[n] x
  have hseq : ∀ n, D.Adj (seq n) (seq (n + 1)) := by
    intro n
    have h1 : seq (n + 1) = f (seq n) := Function.iterate_succ_apply' (f := f) n x
    rw [h1]
    exact hf (seq n)
  obtain ⟨a, b, hab, hba⟩ :=
    Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := seq) (fun _ => Set.mem_univ _)
  have hper : Function.IsPeriodicPt f (b - a) (seq a) := by
    show f^[b - a] (seq a) = seq a
    have hsplit : f^[b - a] (seq a) = seq b := by
      show f^[b - a] (f^[a] x) = f^[b] x
      rw [(Function.iterate_add_apply f (b - a) a x).symm, Nat.sub_add_cancel (le_of_lt hab)]
    rw [hsplit, hba]
  have hbapos : 0 < b - a := Nat.sub_pos_of_lt hab
  have hm : 0 < Function.minimalPeriod f (seq a) := hper.minimalPeriod_pos hbapos
  let c : Fin (Function.minimalPeriod f (seq a)) → V := fun k => f^[k.val] (seq a)
  have hc_inj : Function.Injective c := by
    intro k l hkl
    have hinj : Set.InjOn (fun n => f^[n] (seq a))
        (Set.Iio (Function.minimalPeriod f (seq a))) :=
      Function.iterate_injOn_Iio_minimalPeriod
    exact Fin.ext (hinj k.isLt l.isLt (by simpa [c] using hkl))
  have hc_adj : ∀ k : Fin (Function.minimalPeriod f (seq a)),
      D.Adj (c k) (c (next hm k)) := by
    intro k
    have hval : (next hm k).val = (k.val + 1) % Function.minimalPeriod f (seq a) := rfl
    have hcnext : c (next hm k) = f^[k.val + 1] (seq a) := by
      show f^[(next hm k).val] (seq a) = f^[k.val + 1] (seq a)
      rw [hval, Function.iterate_mod_minimalPeriod_eq]
    rw [hcnext]
    have hck : c k = f^[k.val] (seq a) := rfl
    rw [hck, Function.iterate_succ_apply']
    exact hf (f^[k.val] (seq a))
  exact ⟨Function.minimalPeriod f (seq a), hm, c, hc_inj, hc_adj⟩

/-- A finite nonempty directed tree has a vertex with empty outgoing neighborhood. -/
theorem exists_outNbrs_empty_of_isDirectedTree {V : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] (D : Defs.Digraph V) (h : IsDirectedTree D) : ∃ v, D.outNbrs v = ∅ := by
  by_contra hcon
  push Not at hcon
  exact h (hasDirectedCycle_of_forall_outNbrs_nonempty D fun v => hcon v)

/-- A finite nonempty directed tree is not a unitary digraph [Severini2003]. -/
theorem directedTree_not_unitary {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (D : Defs.Digraph V) (h : IsDirectedTree D) : ¬ IsUnitaryDigraph D := by
  intro hU
  obtain ⟨v, hv⟩ := exists_outNbrs_empty_of_isDirectedTree D h
  have h' := outNbrs_nonempty_of_isUnitaryDigraph D hU v
  rw [hv] at h'
  obtain ⟨w, hw⟩ := h'
  exact hw

/-- A digraph permutation equivalent to a finite nonempty directed tree is not unitary
[Severini2003]. -/
theorem proposition2_directedTree {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Nonempty W] (D : Defs.Digraph V) (D₀ : Defs.Digraph W)
    (h : PermEquivalentTo D D₀) (htree : IsDirectedTree D₀) : ¬ IsUnitaryDigraph D := by
  intro hUD
  exact directedTree_not_unitary D₀ htree ((lemma2 h).mp hUD)

end Qatlib.Papers.UnitaryDigraph.MainResults.NoGo
