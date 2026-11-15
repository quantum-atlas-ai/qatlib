/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.QuditF1024
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.MagicDistill24.Triorthogonal

def quditQubitLabelEquiv : F1024 ≃ (Fin 10 → Bool) :=
  Fintype.equivOfCardEq (by simp [card_F1024])

/-- Shows that the qudit-qubit label equivalence is bijective. -/
theorem quditQubitLabelEquiv_bijective : Function.Bijective quditQubitLabelEquiv :=
  quditQubitLabelEquiv.bijective

/-- Shows that an element pairing to trace zero with every field element must be zero. -/
theorem f1024TracePair_nondegenerate (x : F1024)
    (hx : ∀ y : F1024, f1024Trace (x * y) = 0) : x = 0 :=
  (traceForm_nondegenerate (ZMod 2) F1024).1 x
    (by intro y; exact hx y)

end Qatlib.Papers.MagicDistill24.Triorthogonal
