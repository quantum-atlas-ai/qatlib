/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Qatlib.Papers.GraphConnect03.MainResults.Defs

/-!
# The parity permutation gadget

This module defines the two-layer cyclic parity step, its inverse, and the permutation
`parityEquiv`. The segment XOR `segXor` describes its iterates, while `parityOf` and
`StronglyConnectedEquiv` supply the parity and orbit predicates used in the connectivity
reduction. See [DurrMhallaLei2003].

## Main statements

* `parityStep_left_inv`: For nonzero `p`, the predecessor step is a left inverse of the parity
  successor step.
* `parityEquiv_iterate`: After `k` parity-permutation steps, the layer advances by `k` and the
  track is XORed with the corresponding segment XOR.
* `parityEquiv_iterate_round`: After one full round of `p` steps, the layer returns to its
  starting value and the track is XORed with the full-round segment XOR.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

open Qatlib.Papers.GraphConnect03.MainResults.Defs

/-- A cyclic layer index in `ZMod p` paired with a Boolean track label. -/
abbrev ParityVertex (p : ℕ) := ZMod p × Bool

/-- The successor moves one cyclic layer forward and XORs the current track label with the input
bit at that layer. -/
def parityStep {p : ℕ} (x : ZMod p → Bool) : ParityVertex p → ParityVertex p
  | (i, l) => (i + 1, Bool.xor l (x i))

/-- The predecessor moves one cyclic layer backward and XORs the track label with the input bit
at the preceding layer. -/
def parityStepInv {p : ℕ} (x : ZMod p → Bool) : ParityVertex p → ParityVertex p
  | (j, l) => (j - 1, Bool.xor l (x (j - 1)))

/-- For nonzero `p`, the predecessor step is a left inverse of the parity successor step
[DurrMhallaLei2003]. -/
theorem parityStep_left_inv {p : ℕ} [NeZero p] (x : ZMod p → Bool) :
    Function.LeftInverse (parityStepInv x) (parityStep x) := by
  rintro ⟨i, l⟩
  refine Prod.ext ?_ ?_
  · simp only [parityStep, parityStepInv]
    ring
  · simp only [parityStep, parityStepInv]
    have hidx : i + 1 - 1 = i := by ring
    rw [hidx, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- For nonzero `p`, the predecessor step is a right inverse of the parity successor step
[DurrMhallaLei2003]. -/
theorem parityStep_right_inv {p : ℕ} [NeZero p] (x : ZMod p → Bool) :
    Function.RightInverse (parityStepInv x) (parityStep x) := by
  rintro ⟨j, l⟩
  refine Prod.ext ?_ ?_
  · simp only [parityStep, parityStepInv]
    ring
  · simp only [parityStep, parityStepInv]
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The permutation of parity vertices induced by the invertible parity successor step
[DurrMhallaLei2003]. -/
def parityEquiv {p : ℕ} [NeZero p] (x : ZMod p → Bool) : ParityVertex p ≃ ParityVertex p :=
  Equiv.ofBijective (parityStep x)
    ⟨(parityStep_left_inv x).injective, (parityStep_right_inv x).surjective⟩

/-- The XOR of the next `k` input bits starting at cyclic layer `i`, defined recursively in `k`. -/
def segXor {p : ℕ} (x : ZMod p → Bool) (i : ZMod p) : ℕ → Bool
  | 0 => false
  | k + 1 => Bool.xor (segXor x i k) (x (i + (k : ZMod p)))

/-- The parity permutation acts by the parity successor step. -/
theorem parityEquiv_apply {p : ℕ} [NeZero p] (x : ZMod p → Bool) (v : ParityVertex p) :
    parityEquiv x v = parityStep x v := rfl

/-- After `k` parity-permutation steps, the layer advances by `k` and the track is XORed with
the corresponding segment XOR [DurrMhallaLei2003]. -/
theorem parityEquiv_iterate {p : ℕ} [NeZero p] (x : ZMod p → Bool) (i : ZMod p)
    (l : Bool) (k : ℕ) :
    (parityEquiv x)^[k] (i, l) = (i + (k : ZMod p), Bool.xor l (segXor x i k)) := by
  induction k with
  | zero => simp [segXor]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, parityEquiv_apply]
      simp only [parityStep, segXor]
      refine Prod.ext ?_ ?_
      · push_cast
        ring
      · rw [Bool.xor_assoc]

/-- The Boolean decision that the number of true input bits is odd. -/
def parityOf {p : ℕ} [NeZero p] (x : ZMod p → Bool) : Bool :=
  decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

/-- After one full round of `p` steps, the layer returns to its starting value and the track is
XORed with the full-round segment XOR [DurrMhallaLei2003]. -/
theorem parityEquiv_iterate_round {p : ℕ} [NeZero p] (x : ZMod p → Bool) (i : ZMod p)
    (l : Bool) :
    (parityEquiv x)^[p] (i, l) = (i, Bool.xor l (segXor x i p)) := by
  rw [parityEquiv_iterate, ZMod.natCast_self, add_zero]

/-- Every element can be sent to every other element by some natural iterate of the equivalence. -/
def StronglyConnectedEquiv {α : Type*} (e : α ≃ α) : Prop :=
  ∀ a b : α, ∃ k : ℕ, e^[k] a = b

end Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
