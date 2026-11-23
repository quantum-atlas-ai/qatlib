/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseNetwork13.MainResults.Model.ElectricalNetwork
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod

/-!
# The parity network

This is the unweighted network of [Wang2017Networks], Theorem 6, Figure 2 and Equations
(185)–(186), using zero-based vertex indices. The short rails switch according to the
input bits. Two long rails connect the source to both final short-rail vertices.
The directed short-rail walk records the parity at its final vertex. The spectral estimates
and query lower bound require additional arguments about this network.

Source: [arXiv:1311.1851v10](https://arxiv.org/abs/1311.1851v10).
-/

@[expose] public section

namespace Qatlib.Papers.SparseNetwork13.MainResults.LowerBound

open Qatlib.Papers.SparseNetwork13.MainResults.Model

/-- Short-rail and long-rail vertices, with the rail labelled by a Boolean. -/
abbrev ParityVertex (n : ℕ) := (Fin (n + 1) × Bool) ⊕ (Fin (4 * n - 1) × Bool)

/-- The two kinds of rail edges and the terminal edges at either end of the long rails. -/
abbrev ParityEdge (n : ℕ) :=
  ((Fin n × Bool) ⊕ (Fin (4 * n - 2) × Bool)) ⊕ (Bool ⊕ Bool)

/-- The paper's parity network, with conductance one on every edge. -/
def parityNetwork {n : ℕ} (hn : 0 < n) (bits : Fin n → Bool) :
    ElecNetwork (ParityVertex n) (ParityEdge n) where
  tail
    | .inl (.inl (i, a)) => .inl (i.castSucc, a)
    | .inl (.inr (j, a)) => .inr (⟨j.val, by omega⟩, a)
    | .inr (.inl _) => .inl (0, false)
    | .inr (.inr a) => .inr (⟨4 * n - 2, by omega⟩, a)
  head
    | .inl (.inl (i, a)) => .inl (i.succ, Bool.xor a (bits i))
    | .inl (.inr (j, a)) => .inr (⟨j.val + 1, by omega⟩, a)
    | .inr (.inl a) => .inr (⟨0, by omega⟩, a)
    | .inr (.inr a) => .inl (Fin.last n, a)
  w _ := 1
  w_pos _ := zero_lt_one
  nonloop := by
    rintro ((⟨i, a⟩ | ⟨j, a⟩) | (a | a))
    · intro h
      have hi := congrArg (fun p : Fin (n + 1) × Bool => p.1.val) (Sum.inl.inj h)
      simp at hi
    · intro h
      have hj := congrArg (fun p : Fin (4 * n - 1) × Bool => p.1.val) (Sum.inr.inj h)
      simp at hj
    · simp
    · simp

/-- For every positive input length the network has exactly ten vertices and ten edges
per input bit. The two rail lengths contribute the same totals for every input string. -/
theorem parity_network_card {n : ℕ} (hn : 0 < n) :
    Fintype.card (ParityVertex n) = 10 * n ∧ Fintype.card (ParityEdge n) = 10 * n := by
  constructor <;>
    simp only [ParityVertex, ParityEdge, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool] <;> omega

/-- The four terminals specified for the voltage, current, and effective-resistance tests
are distinct. The two measurement terminals are the tail and head of the selected long edge. -/
theorem parity_network_terminals {n : ℕ} (hn : 0 < n) (bits : Fin n → Bool) :
    let s : ParityVertex n := .inl (0, false)
    let t : ParityVertex n := .inl (Fin.last n, false)
    let u : ParityVertex n := .inr (⟨2 * n - 2, by omega⟩, false)
    let v : ParityVertex n := .inr (⟨2 * n - 1, by omega⟩, false)
    s ≠ t ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v ∧ u ≠ v ∧
      ∃ e, (parityNetwork hn bits).tail e = u ∧ (parityNetwork hn bits).head e = v := by
  dsimp
  refine ⟨?_, by simp, by simp, by simp, by simp, ?_, ?_⟩
  · intro h
    have hi := congrArg (fun p : Fin (n + 1) × Bool => p.1.val) (Sum.inl.inj h)
    simp at hi
    omega
  · intro h
    have hi := congrArg (fun p : Fin (4 * n - 1) × Bool => p.1.val) (Sum.inr.inj h)
    simp at hi
    omega
  · refine ⟨.inl (.inr (⟨2 * n - 2, by omega⟩, false)), rfl, ?_⟩
    have hstep : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    simp [parityNetwork, hstep]

/-- Cumulative XOR of the first `k` input bits, starting with `initial` on the chosen rail.
Indices beyond the input length leave the accumulated bit unchanged. -/
def railParity {n : ℕ} (bits : Fin n → Bool) (initial : Bool) : ℕ → Bool
  | 0 => initial
  | k + 1 => if hk : k < n then Bool.xor (railParity bits initial k) (bits ⟨k, hk⟩)
    else railParity bits initial k

/-- Following the directed short-rail edges up to layer `i` arrives on the rail obtained
by XOR of the first `i` input bits. Taking the final layer gives Equation (185). -/
theorem parity_network_short_walk {n : ℕ} (hn : 0 < n) (bits : Fin n → Bool)
    (initial : Bool) (i : Fin (n + 1)) :
    Relation.ReflTransGen
      (fun a b => ∃ e, (parityNetwork hn bits).tail e = a ∧ (parityNetwork hn bits).head e = b)
      (.inl (0, initial)) (.inl (i, railParity bits initial i.val)) := by
  induction i using Fin.induction with
  | zero =>
    exact Relation.ReflTransGen.refl
  | succ i ih =>
    apply ih.tail
    refine ⟨.inl (.inl (i, railParity bits initial i.val)), rfl, ?_⟩
    simp [parityNetwork, railParity, i.isLt]

/-- Each long rail is a directed chain from its first vertex to any of its vertices. -/
private theorem parity_network_long_walk {n : ℕ} (hn : 0 < n) (bits : Fin n → Bool)
    (a : Bool) (j : ℕ) (hj : j < 4 * n - 1) :
    Relation.ReflTransGen
      (fun u v => ∃ e, (parityNetwork hn bits).tail e = u ∧ (parityNetwork hn bits).head e = v)
      (.inr (⟨0, by omega⟩, a)) (.inr (⟨j, hj⟩, a)) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
    apply (ih (by omega)).tail
    exact ⟨.inl (.inr (⟨j, by omega⟩, a)), rfl, rfl⟩

/-- The initial rail label is XORed with the parity of the input prefix. -/
private theorem railParity_initial {n : ℕ} (bits : Fin n → Bool) (initial : Bool) (k : ℕ) :
    railParity bits initial k = Bool.xor initial (railParity bits false k) := by
  induction k with
  | zero => simp [railParity]
  | succ k ih =>
    by_cases hk : k < n
    · simp [railParity, hk, ih]
    · simp [railParity, hk, ih]

/-- The incidence network is connected for every positive input length and all bit strings.
The undirected reachability relation is the equivalence closure of the oriented edges. -/
theorem parity_network_connected {n : ℕ} (hn : 0 < n) (bits : Fin n → Bool)
    (u v : ParityVertex n) :
    Relation.EqvGen
      (fun a b => ∃ e, (parityNetwork hn bits).tail e = a ∧ (parityNetwork hn bits).head e = b)
      u v := by
  let G := parityNetwork hn bits
  let R : ParityVertex n → ParityVertex n → Prop := fun a b => ∃ e, G.tail e = a ∧ G.head e = b
  let s : ParityVertex n := .inl (0, false)
  have lift {a b : ParityVertex n} (h : Relation.ReflTransGen R a b) :
      Relation.EqvGen R a b := by
    induction h with
    | refl => exact .refl _
    | tail _ hEdge ih => exact .trans _ _ _ ih (.rel _ _ hEdge)
  have fromLong (j : Fin (4 * n - 1)) (a : Bool) : Relation.EqvGen R s (.inr (j, a)) :=
    .trans _ _ _ (.rel _ _ ⟨.inr (.inl a), rfl, rfl⟩)
      (lift (parity_network_long_walk hn bits a j j.isLt))
  have fromRight (a : Bool) : Relation.EqvGen R s (.inl (Fin.last n, a)) :=
    .trans _ _ _ (fromLong ⟨4 * n - 2, by omega⟩ a) (.rel _ _ ⟨.inr (.inr a), rfl, rfl⟩)
  have fromStart (a : Bool) : Relation.EqvGen R s (.inl (0, a)) :=
    .trans _ _ _ (fromRight (railParity bits a n))
      (.symm _ _ (lift (parity_network_short_walk hn bits a (Fin.last n))))
  have fromSource (p : ParityVertex n) : Relation.EqvGen R s p := by
    rcases p with ⟨i, a⟩ | ⟨j, a⟩
    · let b := Bool.xor a (railParity bits false i.val)
      have hlabel : railParity bits b i.val = a := by
        rw [railParity_initial bits b i.val]
        simp [b]
      have hwalk := lift (parity_network_short_walk hn bits b i)
      rw [hlabel] at hwalk
      exact .trans _ _ _ (fromStart b) hwalk
    · exact fromLong j a
  exact .trans _ _ _ (.symm _ _ (fromSource u)) (fromSource v)

end Qatlib.Papers.SparseNetwork13.MainResults.LowerBound
