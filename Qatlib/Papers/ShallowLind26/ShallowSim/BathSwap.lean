/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic

/-!
# Bath-register exchange (Lemma 5.2)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 5.2, page 26.

The bath register is a configuration `L : ι → α`; the exchange map for a
permanent label `b` and a supplied value `v` is

`F_b (L, v) = (L[b := v], L b)`.

It stores the old value of the label in the second component and overwrites the
configuration at `b`.  The paper observes that this map is an involution: a
second exchange restores the old value and puts the supplied value back where it
was.  We prove exactly this involution property, including the behaviour at the
boundary of the register (where `update` is still defined and leaves `L`
unchanged away from `b`).
-/

namespace Qatlib.Papers.ShallowLind26.ShallowSim.BathSwap

set_option autoImplicit false

variable {ι α : Type*} [DecidableEq ι]

/-- Exchange the value stored at a permanent bath label with a supplied value. -/
def exchange (b : ι) (L : ι → α) (v : α) : (ι → α) × α :=
  (Function.update L b v, L b)

/-- **Lemma 5.2, involution.**  Exchanging twice at the same permanent label is
the identity on the register/value pair. -/
theorem exchange_involutive (b : ι) (L : ι → α) (v : α) :
    exchange b (exchange b L v).1 (exchange b L v).2 = (L, v) := by
  unfold exchange
  simp only
  refine Prod.ext ?_ ?_
  · funext i
    by_cases h : i = b
    · subst h
      simp
    · simp [h]
  · simp

/-- The second component of the exchange is the value that was stored at `b`. -/
@[simp] theorem exchange_snd (b : ι) (L : ι → α) (v : α) :
    (exchange b L v).2 = L b := rfl

/-- After the exchange the register stores the supplied value at `b`. -/
@[simp] theorem exchange_fst_self (b : ι) (L : ι → α) (v : α) :
    (exchange b L v).1 b = v := by
  simp [exchange]

/-- Away from the permanent label the register is unchanged. -/
theorem exchange_fst_of_ne {b i : ι} (L : ι → α) (v : α) (h : i ≠ b) :
    (exchange b L v).1 i = L i := by
  simp [exchange, h]

end Qatlib.Papers.ShallowLind26.ShallowSim.BathSwap
