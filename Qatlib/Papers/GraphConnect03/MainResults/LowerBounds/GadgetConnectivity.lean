/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.ParityReduce
import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.Theorem4StrongConnectivity

/-!
# Connectivity of the parity-clique gadget

This module proves that the neighbor-list gadget is strongly connected exactly when its
underlying Boolean input has odd parity, assuming a nonzero layer count and clique size greater
than one. The predicate `OrbitOrClique` tracks vertices reachable from the base point and
connects gadget reachability to the parity permutation orbit. See [DurrMhallaLei2003].

## Main statements

* `gadget_reach_parity_iff`: A parity vertex is reachable from the base vertex in the gadget
  exactly when it occurs in the base parity-permutation orbit.
* `gadget_reach_to_v0`: For clique size greater than one, every gadget vertex reaches the base
  parity vertex.
* `gadget_strong_iff`: For nonzero layer count and clique size greater than one, all-pairs
  gadget reachability is equivalent to odd input parity.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

open Qatlib.Papers.GraphConnect03.MainResults.Defs
open Qatlib.Papers.GraphConnect03.ParityReduce

/-- The edge relation induced by the gadget neighbor function, with an edge when some port
selects the target vertex. -/
def gadgetEdge {p k : ℕ} (b : ZMod p → Bool) (jf : ZMod p → Bool → ZMod k)
    (u v : GadgetVertex p k) : Prop :=
  ∃ j : ZMod k, gadgetNbr b jf u j = v

/-- The reflexive transitive closure of the gadget edge relation. -/
def gadgetReach {p k : ℕ} (b : ZMod p → Bool) (jf : ZMod p → Bool → ZMod k) :
    GadgetVertex p k → GadgetVertex p k → Prop :=
  Relation.ReflTransGen (gadgetEdge b jf)

variable {p k : ℕ} {b : ZMod p → Bool} {jf : ZMod p → Bool → ZMod k}

/-- A single gadget edge gives gadget reachability. -/
theorem gadgetReach.single {u v : GadgetVertex p k} (h : gadgetEdge b jf u v) :
    gadgetReach b jf u v :=
  Relation.ReflTransGen.single h

/-- Gadget reachability is transitive. -/
theorem gadgetReach.trans {a c d : GadgetVertex p k}
    (h1 : gadgetReach b jf a c) (h2 : gadgetReach b jf c d) :
    gadgetReach b jf a d :=
  Relation.ReflTransGen.trans h1 h2

/-- Every clique vertex has a gadget edge to the base parity vertex `(0, false)`. -/
theorem gadget_clique_v0 (jf : ZMod p → Bool → ZMod k) (u : ZMod k) :
    gadgetEdge b jf (Sum.inr u) (Sum.inl ((0 : ZMod p), false)) :=
  ⟨0, by simp [gadgetNbr]⟩

/-- Any clique vertex can reach any other clique vertex [DurrMhallaLei2003]. -/
theorem gadget_clique_reach (jf : ZMod p → Bool → ZMod k) (u m : ZMod k) :
    gadgetReach b jf (Sum.inr u) (Sum.inr m) := by
  by_cases h : u = m
  · subst h
    exact Relation.ReflTransGen.refl
  · have hj : m - u ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hstep : gadgetEdge b jf (Sum.inr u) (Sum.inr (u + (m - u))) :=
      ⟨m - u, by simp [gadgetNbr, hj]⟩
    rw [add_sub_cancel] at hstep
    exact gadgetReach.single hstep

/-- Every parity vertex has a gadget edge to its successor under the parity step. -/
theorem gadget_parity_forward (jf : ZMod p → Bool → ZMod k) (i : ZMod p) (l : Bool) :
    gadgetEdge b jf (Sum.inl (i, l)) (Sum.inl (i + 1, Bool.xor l (b i))) :=
  ⟨jf i l, by simp [gadgetNbr]⟩

/-- When the clique size is greater than one, every parity vertex has an edge to some clique
vertex. -/
theorem gadget_parity_back [NeZero k] (jf : ZMod p → Bool → ZMod k) (hk : 1 < k)
    (i : ZMod p) (l : Bool) :
    ∃ u : ZMod k, gadgetEdge b jf (Sum.inl (i, l)) (Sum.inr u) := by
  have hcard : 1 < Fintype.card (ZMod k) := by
    rw [ZMod.card]
    exact hk
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard (jf i l)
  exact ⟨j, j, by simp [gadgetNbr, hj]⟩

/-- A vertex is either in the forward parity-permutation orbit of `(0, false)` or is a clique
vertex. -/
def OrbitOrClique (p k : ℕ) [NeZero p] (b : ZMod p → Bool)
    (s : GadgetVertex p k) : Prop :=
  (∃ t : ℕ, Sum.inl ((parityEquiv b)^[t] ((0 : ZMod p), false)) = s) ∨
    ∃ u : ZMod k, s = Sum.inr u

namespace OrbitOrClique

/-- The base parity vertex satisfies `OrbitOrClique`. -/
theorem base [NeZero p] :
    OrbitOrClique p k b (Sum.inl ((0 : ZMod p), false)) := by
  left
  exact ⟨0, by simp⟩

/-- The predicate `OrbitOrClique` is preserved by a gadget edge. -/
theorem step [NeZero p] {s s' : GadgetVertex p k}
    (hs : OrbitOrClique p k b s) (he : gadgetEdge b jf s s') :
    OrbitOrClique p k b s' := by
  rcases hs with ⟨t, ht⟩ | ⟨u, rfl⟩
  · rw [← ht] at he
    cases hq' : (parityEquiv b)^[t] ((0 : ZMod p), false) with
    | mk i l =>
      rw [hq'] at he
      obtain ⟨j, hj⟩ := he
      by_cases hcond : j = jf i l
      · left
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply', hq']
        simp only [parityEquiv_apply, parityStep]
        simp only [gadgetNbr, if_pos hcond] at hj
        exact hj
      · right
        simp only [gadgetNbr] at hj
        rw [if_neg hcond] at hj
        exact ⟨j, hj.symm⟩
  · obtain ⟨j, hj⟩ := he
    by_cases hcond : j = 0
    · left
      refine ⟨0, ?_⟩
      simp only [gadgetNbr, if_pos hcond] at hj
      simpa using hj
    · right
      simp only [gadgetNbr, if_neg hcond] at hj
      exact ⟨u + j, hj.symm⟩

end OrbitOrClique

/-- Every gadget vertex reachable from the base parity vertex satisfies `OrbitOrClique`. -/
theorem gadget_reach_orbit_aux [NeZero p] {s : GadgetVertex p k}
    (h : gadgetReach b jf (Sum.inl ((0 : ZMod p), false)) s) :
    OrbitOrClique p k b s := by
  induction h with
  | refl => exact OrbitOrClique.base
  | tail _ hbc ih => exact OrbitOrClique.step ih hbc

/-- Every iterate of the base parity vertex under the parity permutation is reachable in the
gadget. -/
theorem gadget_orbit_reach [NeZero p] (jf : ZMod p → Bool → ZMod k) :
    ∀ (t : ℕ) (q : ParityVertex p),
      (parityEquiv b)^[t] ((0 : ZMod p), false) = q →
      gadgetReach b jf (Sum.inl ((0 : ZMod p), false)) (Sum.inl q) := by
  intro t
  induction t with
  | zero =>
      intro q hq
      rw [Function.iterate_zero] at hq
      subst hq
      exact Relation.ReflTransGen.refl
  | succ t ih =>
      intro q hq
      rw [Function.iterate_succ_apply'] at hq
      cases hq' : (parityEquiv b)^[t] ((0 : ZMod p), false) with
      | mk i l =>
        rw [hq'] at hq
        have hstep : gadgetEdge b jf (Sum.inl (i, l)) (Sum.inl q) := by
          have hqeq : q = (i + 1, Bool.xor l (b i)) := by
            rw [← hq, parityEquiv_apply]
            rfl
          rw [hqeq]
          exact gadget_parity_forward jf i l
        exact (ih (i, l) hq').tail hstep

/-- A parity vertex is reachable from the base vertex in the gadget exactly when it occurs in
the base parity-permutation orbit [DurrMhallaLei2003]. -/
theorem gadget_reach_parity_iff [NeZero p] (jf : ZMod p → Bool → ZMod k)
    (q : ParityVertex p) :
    gadgetReach b jf (Sum.inl ((0 : ZMod p), false)) (Sum.inl q) ↔
      ∃ t : ℕ, (parityEquiv b)^[t] ((0 : ZMod p), false) = q := by
  constructor
  · intro h
    rcases gadget_reach_orbit_aux h with ⟨t, ht⟩ | ⟨u, hu⟩
    · exact ⟨t, Sum.inl.inj ht⟩
    · exact absurd hu (by simp)
  · rintro ⟨t, rfl⟩
    exact gadget_orbit_reach jf t _ rfl

/-- For odd input parity and clique size greater than one, the base vertex reaches every gadget
vertex. -/
theorem gadget_reach_from_v0 [NeZero p] [NeZero k] (jf : ZMod p → Bool → ZMod k)
    (hk : 1 < k) (hp : parityOf b = true) (s : GadgetVertex p k) :
    gadgetReach b jf (Sum.inl ((0 : ZMod p), false)) s := by
  cases s with
  | inl q =>
      obtain ⟨t, ht⟩ := parity_strong b hp (0, false) q
      exact gadget_orbit_reach jf t q ht
  | inr u =>
      obtain ⟨u₀, hedge⟩ := gadget_parity_back jf hk (0 : ZMod p) false
      exact (gadgetReach.single hedge).trans (gadget_clique_reach jf u₀ u)

/-- For clique size greater than one, every gadget vertex reaches the base parity vertex. -/
theorem gadget_reach_to_v0 [NeZero k] (jf : ZMod p → Bool → ZMod k) (hk : 1 < k)
    (s : GadgetVertex p k) :
    gadgetReach b jf s (Sum.inl ((0 : ZMod p), false)) := by
  cases s with
  | inl q =>
      obtain ⟨i, l⟩ := q
      obtain ⟨u, hedge⟩ := gadget_parity_back jf hk i l
      exact (gadgetReach.single hedge).trans
        (gadgetReach.single (gadget_clique_v0 jf u))
  | inr u =>
      exact gadgetReach.single (gadget_clique_v0 jf u)

/-- For even input parity, no iterate of `(0, false)` under the parity permutation equals `(0,
true)`. -/
theorem parity_no_mixed_orbit [NeZero p] (hp : parityOf b = false) (t : ℕ) :
    (parityEquiv b)^[t] ((0 : ZMod p), false) ≠ ((0 : ZMod p), true) := by
  intro ht
  rw [parityEquiv_iterate] at ht
  have hcol : ((t : ZMod p)) = 0 := by
    have := congrArg Prod.fst ht
    simpa using this
  have hlev : segXor b 0 t = true := by
    have := congrArg Prod.snd ht
    simpa using this
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff t p).mp hcol
  subst hq
  have hzero : segXor b 0 (p * q) = false := by
    rw [show p * q = q * p by ring, segXor_mul, hp]
    split <;> rfl
  rw [hzero] at hlev
  exact Bool.false_ne_true hlev

/-- For nonzero layer count and clique size greater than one, all-pairs gadget reachability is
equivalent to odd input parity [DurrMhallaLei2003]. -/
theorem gadget_strong_iff [NeZero p] [NeZero k] (jf : ZMod p → Bool → ZMod k)
    (hk : 1 < k) :
    (∀ a c : GadgetVertex p k, gadgetReach b jf a c) ↔ parityOf b = true := by
  constructor
  · intro hSC
    by_contra h
    have hfalse : parityOf b = false := by
      cases hb : parityOf b <;> simp_all
    have hreach : gadgetReach b jf (Sum.inl ((0 : ZMod p), false))
        (Sum.inl ((0 : ZMod p), true)) := hSC _ _
    obtain ⟨t, ht⟩ := (gadget_reach_parity_iff jf (0, true)).mp hreach
    exact parity_no_mixed_orbit hfalse t ht
  · intro hp a c
    exact (gadget_reach_to_v0 jf hk a).trans (gadget_reach_from_v0 jf hk hp c)

end Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
