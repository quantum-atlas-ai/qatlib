/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.ParityReduction
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Parity and strong connectivity of a cyclic gadget

This module translates Boolean XOR into addition in `ZMod 2` and identifies each full-round
segment XOR with `parityOf`. It proves that the parity permutation, and equivalently its
directed successor graph, is strongly connected exactly when the input parity is odd. See
[DurrMhallaLei2003].

## Main statements

* `segXor_full`: For nonzero `p`, every full-round segment XOR equals the input parity.
* `parity_reduction_strong_iff`: The parity permutation is strongly connected exactly when the
  input parity is true.
* `parity_edge_strong_iff`: For nonzero `p`, all-pairs reachability in the parity successor
  graph is equivalent to odd input parity.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GraphConnect03.ParityReduce

open Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

/-- The encoding of a Boolean value in `ZMod 2`, sending false to zero and true to one. -/
def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The Boolean-to-`ZMod 2` encoding sends XOR to addition. -/
theorem bitZ_xor (a b : Bool) : bitZ (Bool.xor a b) = bitZ a + bitZ b := by
  cases a <;> cases b <;> decide

/-- The Boolean-to-`ZMod 2` encoding is injective. -/
theorem bitZ_injective : Function.Injective bitZ := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitZ]

/-- A Boolean value has encoding one exactly when it is true. -/
theorem bitZ_eq_one_iff (b : Bool) : bitZ b = 1 ↔ b = true := by
  cases b <;> simp [bitZ]

/-- A Boolean value has encoding zero exactly when it is false. -/
theorem bitZ_eq_zero_iff (b : Bool) : bitZ b = 0 ↔ b = false := by
  cases b <;> simp [bitZ]

/-- The sum in `ZMod 2` of the next `k` encoded input bits starting at cyclic layer `i`. -/
def zseg {p : ℕ} (x : ZMod p → Bool) (i : ZMod p) (k : ℕ) : ZMod 2 :=
  ∑ t ∈ Finset.range k, bitZ (x (i + (t : ZMod p)))

/-- Encoding a segment XOR in `ZMod 2` gives the corresponding segment sum `zseg`. -/
theorem bitZ_segXor {p : ℕ} (x : ZMod p → Bool) (i : ZMod p) (k : ℕ) :
    bitZ (segXor x i k) = zseg x i k := by
  induction k with
  | zero => simp [segXor, zseg, bitZ]
  | succ k ih =>
      rw [segXor, bitZ_xor, ih]
      unfold zseg
      rw [Finset.sum_range_succ]

/-- The XOR over a segment of length `a + b` splits into the first `a` bits and the following
`b` bits. -/
theorem segXor_add {p : ℕ} (x : ZMod p → Bool) (i : ZMod p) (a b : ℕ) :
    segXor x i (a + b) =
      Bool.xor (segXor x i a) (segXor x (i + (a : ZMod p)) b) := by
  induction b with
  | zero => simp [segXor]
  | succ b ih =>
      rw [Nat.add_succ, segXor, ih]
      simp only [segXor, Nat.cast_add, add_assoc]
      rw [Bool.xor_assoc]

/-- For nonzero `p`, the next `p` cyclic indices starting at any layer cover all of `ZMod p`. -/
theorem range_add_image {p : ℕ} [NeZero p] (i : ZMod p) :
    (Finset.range p).image (fun t : ℕ => i + (t : ZMod p)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn]
  · simp
  · intro t ht t' ht' hEq
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    have h : ((t : ZMod p)) = ((t' : ZMod p)) := add_left_cancel hEq
    have hmod : t % p = t' % p := (ZMod.natCast_eq_natCast_iff' t t' p).mp h
    rwa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hmod

/-- For nonzero `p`, a full-round encoded segment sum is the sum of all encoded input bits. -/
theorem zseg_full {p : ℕ} [NeZero p] (x : ZMod p → Bool) (i : ZMod p) :
    zseg x i p = ∑ j : ZMod p, bitZ (x j) := by
  have himg := range_add_image i
  unfold zseg
  rw [← himg, Finset.sum_image]
  · intro t ht t' ht' hEq
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    have h : ((t : ZMod p)) = ((t' : ZMod p)) := add_left_cancel hEq
    have hmod : t % p = t' % p := (ZMod.natCast_eq_natCast_iff' t t' p).mp h
    rwa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hmod

/-- The sum of encoded bits in `ZMod 2` is the cast of the number of true input bits. -/
theorem sum_bitZ {p : ℕ} [NeZero p] (x : ZMod p → Bool) :
    (∑ j : ZMod p, bitZ (x j)) =
      ((Finset.univ.filter (fun j => x j = true)).card : ZMod 2) := by
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl ?_
  intro j _
  cases hx : x j <;> simp [bitZ]

/-- For nonzero `p`, every full-round segment XOR equals the input parity [DurrMhallaLei2003]. -/
theorem segXor_full {p : ℕ} [NeZero p] (x : ZMod p → Bool) (i : ZMod p) :
    segXor x i p = parityOf x := by
  refine bitZ_injective ?_
  rw [bitZ_segXor, zseg_full, sum_bitZ]
  by_cases h : Odd (Finset.univ.filter (fun j => x j = true)).card
  · rw [ZMod.natCast_eq_one_iff_odd.mpr h]
    simp [parityOf, h, bitZ]
  · have hev : Even (Finset.univ.filter (fun j => x j = true)).card :=
      Nat.not_odd_iff_even.mp h
    rw [ZMod.natCast_eq_zero_iff_even.mpr hev]
    simp [parityOf, h, bitZ]

/-- For nonzero `p`, advancing a cyclic layer by `k` returns to the same layer exactly when `p`
divides `k`. -/
theorem col_add_eq_self_iff {p : ℕ} [NeZero p] (i : ZMod p) (k : ℕ) :
    i + (k : ZMod p) = i ↔ p ∣ k := by
  rw [← ZMod.natCast_eq_zero_iff k p]
  constructor
  · intro h
    exact add_left_cancel (show i + (k : ZMod p) = i + 0 by simpa using h)
  · intro h
    rw [h, add_zero]

/-- The XOR over `q` full rounds is the input parity when `q` is odd and false when `q` is even. -/
theorem segXor_mul {p : ℕ} [NeZero p] (x : ZMod p → Bool) (i : ZMod p) (q : ℕ) :
    segXor x i (q * p) = if Odd q then parityOf x else false := by
  induction q with
  | zero => simp [segXor]
  | succ q ih =>
      have h : (q + 1) * p = q * p + p := by ring
      rw [h, segXor_add, ih, segXor_full]
      by_cases hq : Odd q
      · have hq1 : ¬ Odd (q + 1) := fun h => (Nat.odd_add_one.mp h) hq
        cases hp : parityOf x <;> simp [hq, hq1]
      · have hq1 : Odd (q + 1) := Nat.odd_add_one.mpr hq
        cases hp : parityOf x <;> simp [hq, hq1]

/-- Even input parity prevents the parity permutation from being strongly connected
[DurrMhallaLei2003]. -/
theorem parity_not_strong {p : ℕ} [NeZero p] (x : ZMod p → Bool)
    (hp : parityOf x = false) : ¬ StronglyConnectedEquiv (parityEquiv x) := by
  intro hSC
  obtain ⟨k, hk⟩ := hSC (0, false) (0, true)
  rw [parityEquiv_iterate] at hk
  have hcol : ((k : ZMod p)) = 0 := by
    have := congrArg Prod.fst hk
    simpa using this
  have hlev : Bool.xor false (segXor x 0 k) = true := by
    have := congrArg Prod.snd hk
    simpa using this
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff k p).mp hcol
  subst hq
  have hzero : segXor x 0 (p * q) = false := by
    rw [show p * q = q * p by ring, segXor_mul, hp]
    split <;> rfl
  rw [hzero] at hlev
  exact Bool.false_ne_true hlev

/-- Odd input parity makes the parity permutation strongly connected [DurrMhallaLei2003]. -/
theorem parity_strong {p : ℕ} [NeZero p] (x : ZMod p → Bool)
    (hp : parityOf x = true) : StronglyConnectedEquiv (parityEquiv x) := by
  intro a b
  obtain ⟨i, l⟩ := a
  obtain ⟨j, l'⟩ := b
  let d : ZMod p := j - i
  let r : ℕ := d.val
  have hr : ((r : ℕ) : ZMod p) = d := ZMod.natCast_zmod_val d
  have hcol : i + (r : ZMod p) = j := by
    rw [hr]
    dsimp only [d]
    abel
  let s : Bool := segXor x i r
  by_cases hb : l' = Bool.xor l s
  · refine ⟨r, ?_⟩
    rw [parityEquiv_iterate, hcol]
    simp only [s] at hb
    rw [hb]
  · refine ⟨r + p, ?_⟩
    have hcol2 : i + ((r + p : ℕ) : ZMod p) = j := by
      push_cast
      rw [← add_assoc, hcol]
      simp
    rw [parityEquiv_iterate, hcol2]
    have hseg : segXor x i (r + p) = Bool.xor s (parityOf x) := by
      rw [segXor_add]
      simp only [s, segXor_full]
    rw [hseg, hp]
    simp only [s] at hb
    cases l <;> cases l' <;> cases hs : segXor x i r <;> simp_all [s]

/-- The parity permutation is strongly connected exactly when the input parity is true
[DurrMhallaLei2003]. -/
theorem parity_reduction_strong_iff {p : ℕ} [NeZero p] (x : ZMod p → Bool) :
    StronglyConnectedEquiv (parityEquiv x) ↔ parityOf x = true := by
  constructor
  · intro hSC
    by_contra h
    have hfalse : parityOf x = false := by
      cases hp : parityOf x <;> simp_all
    exact parity_not_strong x hfalse hSC
  · intro hp
    exact parity_strong x hp

/-- An equality between a permutation iterate of `a` and `b` yields reachability from `a` to `b`
through successor edges. -/
theorem perm_reach_of_iterate {α : Type*} (e : α ≃ α) :
    ∀ (k : ℕ) (a b : α), e^[k] a = b →
      Relation.ReflTransGen (fun x y => e x = y) a b
  | 0, a, b, h => by
      rw [Function.iterate_zero] at h
      subst h
      exact Relation.ReflTransGen.refl
  | k + 1, a, b, h => by
      rw [Function.iterate_succ_apply] at h
      exact Relation.ReflTransGen.head rfl (perm_reach_of_iterate e k (e a) b h)

/-- Reachability through permutation successor edges is witnessed by some natural iterate of the
permutation. -/
theorem iterate_of_perm_reach {α : Type*} (e : α ≃ α) {a b : α}
    (h : Relation.ReflTransGen (fun x y => e x = y) a b) :
    ∃ k : ℕ, e^[k] a = b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk]; exact hbc⟩

/-- All-pairs reachability through permutation successor edges is equivalent to
`StronglyConnectedEquiv`. -/
theorem perm_reach_all_iff {α : Type*} (e : α ≃ α) :
    (∀ a b : α, Relation.ReflTransGen (fun x y => e x = y) a b) ↔
      StronglyConnectedEquiv e := by
  constructor
  · intro h a b
    exact iterate_of_perm_reach e (h a b)
  · intro h a b
    obtain ⟨k, hk⟩ := h a b
    exact perm_reach_of_iterate e k a b hk

/-- The directed successor relation given by one parity step. -/
def parityEdge {p : ℕ} (x : ZMod p → Bool) (u v : ParityVertex p) : Prop :=
  parityStep x u = v

/-- For nonzero `p`, all-pairs reachability in the parity successor graph is equivalent to odd
input parity [DurrMhallaLei2003]. -/
theorem parity_edge_strong_iff {p : ℕ} [NeZero p] (x : ZMod p → Bool) :
    (∀ u v : ParityVertex p, Relation.ReflTransGen (parityEdge x) u v) ↔
      parityOf x = true := by
  have hstep : (parityEdge x) = (fun u v => parityEquiv x u = v) := by
    funext u v
    simp [parityEdge, parityEquiv_apply]
  rw [hstep]
  rw [perm_reach_all_iff]
  exact parity_reduction_strong_iff x

end Qatlib.Papers.GraphConnect03.ParityReduce
