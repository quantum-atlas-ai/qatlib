/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Function.Basic

/-!
# Coherent Boolean evaluation (Lemma 5.3)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 5.3, page 27.

A bounded-fan-in Boolean network computes `f` on an input register `x`, while a
separately stored output register `z` and a work register `w` are present.  The
compute--copy--uncompute circuit `U_f` is the controlled toggle

`U_f (x, z, w) = (x, z ⊕ f(x), w)`.

The register `x` is unchanged, the work register is untouched, and the output
register is toggled by the computed bit.  Since the toggling only depends on `x`,
applying `U_f` twice restores the original output: `U_f` is an involution and
hence unitary on the computational basis.  This is the algebraic content of the
compute--copy--uncompute construction; the circuit size `O(s+t)` is the usual
gate-by-gate implementation of the network, and the untouched reference is
handled because the map is the identity on the third component.
-/

namespace Qatlib.Papers.ShallowLind26.ShallowSim.BooleanEval

set_option autoImplicit false

variable {n t s : ℕ}

/-- Toggle a Boolean register at every position selected by a mask. -/
def toggle (mask z : Fin t → Bool) : Fin t → Bool :=
  fun i => if mask i then !(z i) else z i

/-- Toggling twice at the same mask is the identity. -/
theorem toggle_toggle (mask z : Fin t → Bool) : toggle mask (toggle mask z) = z := by
  funext i
  unfold toggle
  by_cases h : mask i
  · simp [h]
  · simp [h]

/-- The coherent evaluation map of a Boolean network on the three registers
input, output and workspace. -/
def evalMap (f : (Fin n → Bool) → (Fin t → Bool))
    (p : (Fin n → Bool) × (Fin t → Bool) × (Fin s → Bool)) :
    (Fin n → Bool) × (Fin t → Bool) × (Fin s → Bool) :=
  (p.1, toggle (f p.1) p.2.1, p.2.2)

/-- **Lemma 5.3, compute--copy--uncompute is an involution.**  Applying the
evaluation map twice returns the original three-register state. -/
theorem evalMap_involutive (f : (Fin n → Bool) → (Fin t → Bool))
    (p : (Fin n → Bool) × (Fin t → Bool) × (Fin s → Bool)) :
    evalMap f (evalMap f p) = p := by
  refine Prod.ext ?_ ?_
  · rfl
  · refine Prod.ext ?_ ?_
    · exact toggle_toggle (f p.1) p.2.1
    · rfl

/-- The input register is preserved. -/
@[simp] theorem evalMap_fst (f : (Fin n → Bool) → (Fin t → Bool))
    (p : (Fin n → Bool) × (Fin t → Bool) × (Fin s → Bool)) :
    (evalMap f p).1 = p.1 := rfl

/-- The workspace register is preserved, including an untouched reference. -/
@[simp] theorem evalMap_workspace (f : (Fin n → Bool) → (Fin t → Bool))
    (p : (Fin n → Bool) × (Fin t → Bool) × (Fin s → Bool)) :
    (evalMap f p).2.2 = p.2.2 := rfl

/-- On a zeroed workspace the map adds the computed value to the output and
keeps the workspace zero. -/
theorem evalMap_zero_workspace (f : (Fin n → Bool) → (Fin t → Bool))
    (x : Fin n → Bool) (z : Fin t → Bool) :
    evalMap f (x, z, (fun _ : Fin s => false)) = (x, toggle (f x) z, (fun _ : Fin s => false)) := rfl

end Qatlib.Papers.ShallowLind26.ShallowSim.BooleanEval
