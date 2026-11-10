/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Qatlib.Papers.GraphConnect03.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

open Qatlib.Papers.GraphConnect03.MainResults.Defs

abbrev ParityVertex (p : ℕ) := ZMod p × Bool

def parityStep {p : ℕ} (x : ZMod p → Bool) : ParityVertex p → ParityVertex p
  | (i, l) => (i + 1, Bool.xor l (x i))

def parityStepInv {p : ℕ} (x : ZMod p → Bool) : ParityVertex p → ParityVertex p
  | (j, l) => (j - 1, Bool.xor l (x (j - 1)))

theorem parityStep_left_inv {p : ℕ} [NeZero p] (x : ZMod p → Bool) :
    Function.LeftInverse (parityStepInv x) (parityStep x) := by
  rintro ⟨i, l⟩
  refine Prod.ext ?_ ?_
  · simp only [parityStep, parityStepInv]
    ring
  · simp only [parityStep, parityStepInv]
    have hidx : i + 1 - 1 = i := by ring
    rw [hidx, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem parityStep_right_inv {p : ℕ} [NeZero p] (x : ZMod p → Bool) :
    Function.RightInverse (parityStepInv x) (parityStep x) := by
  rintro ⟨j, l⟩
  refine Prod.ext ?_ ?_
  · simp only [parityStep, parityStepInv]
    ring
  · simp only [parityStep, parityStepInv]
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

def parityEquiv {p : ℕ} [NeZero p] (x : ZMod p → Bool) : ParityVertex p ≃ ParityVertex p :=
  Equiv.ofBijective (parityStep x)
    ⟨(parityStep_left_inv x).injective, (parityStep_right_inv x).surjective⟩

def segXor {p : ℕ} (x : ZMod p → Bool) (i : ZMod p) : ℕ → Bool
  | 0 => false
  | k + 1 => Bool.xor (segXor x i k) (x (i + (k : ZMod p)))

theorem parityEquiv_apply {p : ℕ} [NeZero p] (x : ZMod p → Bool) (v : ParityVertex p) :
    parityEquiv x v = parityStep x v := rfl

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

def parityOf {p : ℕ} [NeZero p] (x : ZMod p → Bool) : Bool :=
  decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

theorem parityEquiv_iterate_round {p : ℕ} [NeZero p] (x : ZMod p → Bool) (i : ZMod p)
    (l : Bool) :
    (parityEquiv x)^[p] (i, l) = (i, Bool.xor l (segXor x i p)) := by
  rw [parityEquiv_iterate, ZMod.natCast_self, add_zero]

def StronglyConnectedEquiv {α : Type*} (e : α ≃ α) : Prop :=
  ∀ a b : α, ∃ k : ℕ, e^[k] a = b

end Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
