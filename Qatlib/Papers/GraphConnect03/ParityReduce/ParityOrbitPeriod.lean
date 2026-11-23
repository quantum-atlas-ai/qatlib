/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GraphConnect03.ParityReduce

@[expose] public section

/-!
# ParityOrbitPeriod — cycle structure of the parity gadget

[DurrMhallaLei2003], Lemma 2 and Figure 1 (p. 6).

Lemma 2 encodes a bit string `x ∈ {0,1}^p` into the permutation
`v_(2i+b) ↦ v_(2(i+1)+(b⊕x_i))` on `2p` vertices.  Every row and every
column of the encoding has degree `1`, and the permutation consists of a
single directed `2p`-cycle when the parity of `x` is odd and of two
disjoint directed cycles when the parity is even.

This file makes that cycle structure explicit for the library's parity
permutation `parityEquiv`: after one full round of `p` steps the column
returns to its starting value and the track is flipped exactly when the
parity is odd, hence the `p`-th iterate is the track swap in the odd case
and the identity in the even case, and the `2p`-th iterate is always the
identity.  It also records that the successor graph of the encoding is
`1`-regular in both directions, the source's "each row and column has
degree `1`" for the list encoding.  The transport of the parity query
lower bound through a list-oracle simulation is not rebuilt here.

## Main statements

* `parityEdge_out_card`: every vertex has exactly one parity successor.
* `parityEdge_in_card`: every vertex has exactly one parity predecessor.
* `parityEquiv_iterate_p_of_odd`: for odd parity, `p` steps swap the track.
* `parityEquiv_iterate_p_of_even`: for even parity, `p` steps are trivial.
* `parityEquiv_iterate_two_p`: `2p` steps are always trivial, so every
  orbit of the parity permutation has at most `2p` elements.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.ParityReduce

open Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
open Qatlib.Papers.GraphConnect03.ParityReduce

/-- Every vertex of the parity encoding has exactly one outgoing successor
edge: the list row of the encoding has degree `1` (source Lemma 2). -/
theorem parityEdge_out_card {p : ℕ} [NeZero p] (x : ZMod p → Bool)
    (u : ParityVertex p) :
    (Finset.univ.filter (fun v => parityStep x u = v)).card = 1 := by
  have hset : Finset.univ.filter (fun v => parityStep x u = v) =
      {parityStep x u} := by
    apply Finset.ext
    intro v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, eq_comm]
  rw [hset, Finset.card_singleton]

/-- Every vertex of the parity encoding has exactly one incoming
predecessor edge: every column of the encoding has degree `1`, because
the parity step is a permutation with predecessor `parityStepInv`
(source Lemma 2). -/
theorem parityEdge_in_card {p : ℕ} [NeZero p] (x : ZMod p → Bool)
    (v : ParityVertex p) :
    (Finset.univ.filter (fun u => parityStep x u = v)).card = 1 := by
  have hset : Finset.univ.filter (fun u => parityStep x u = v) =
      {parityStepInv x v} := by
    apply Finset.ext
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      have h1 : parityStepInv x (parityStep x u) = parityStepInv x v :=
        congrArg (parityStepInv x) h
      rw [parityStep_left_inv x u] at h1
      exact h1
    · intro h
      rw [h]
      exact parityStep_right_inv x v
  rw [hset, Finset.card_singleton]

/-- For odd parity, one full round of `p` parity steps returns to the same
column and swaps the track: the two tracks belong to a single `2p`-cycle
orbit (source Lemma 2, odd case). -/
theorem parityEquiv_iterate_p_of_odd {p : ℕ} [NeZero p]
    (x : ZMod p → Bool) (hp : parityOf x = true) (i : ZMod p) (l : Bool) :
    (parityEquiv x)^[p] (i, l) = (i, !l) := by
  rw [parityEquiv_iterate_round, segXor_full, hp]
  cases l <;> rfl

/-- For even parity, one full round of `p` parity steps returns to the
starting vertex. The two vertices in its starting column lie on separate
orbits (source Lemma 2, even case). -/
theorem parityEquiv_iterate_p_of_even {p : ℕ} [NeZero p]
    (x : ZMod p → Bool) (hp : parityOf x = false) (v : ParityVertex p) :
    (parityEquiv x)^[p] v = v := by
  obtain ⟨i, l⟩ := v
  rw [parityEquiv_iterate_round, segXor_full, hp]
  cases l <;> rfl

/-- In both parity cases, `2p` steps return every vertex to its starting
point, so each orbit has period dividing `2p`. -/
theorem parityEquiv_iterate_two_p {p : ℕ} [NeZero p]
    (x : ZMod p → Bool) (v : ParityVertex p) :
    (parityEquiv x)^[2 * p] v = v := by
  obtain ⟨i, l⟩ := v
  rw [parityEquiv_iterate]
  have hcol : i + ((2 * p : ℕ) : ZMod p) = i := by
    push_cast
    simp
  rw [hcol]
  have hseg : segXor x i (2 * p) = false := by
    rw [segXor_mul]
    simp
  rw [hseg]
  cases l <;> rfl

end Qatlib.Papers.GraphConnect03.ParityReduce
