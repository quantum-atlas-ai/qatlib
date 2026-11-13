/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates

/-!
# Register and state embeddings with fixed surrounding wires

`wireContextExtend` places a smaller Boolean register on wires selected by an injection and uses
a fixed register on the remaining wires. `wireContextEmbed` extends this construction to quantum
states by summing over computational basis vectors, following the register conventions of
[NielsenChuang2010].

## Main statements

* `wireContextExtend`: extend a basis register along an injection of wires.
* `wireContextEmbed`: embed a state by extending each basis register.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped BigOperators
set_option autoImplicit false

/-- Extend a smaller register along an injective wire map, using the fixed surrounding register
on all other wires. -/
noncomputable def wireContextExtend {a L : ℕ} (e : Fin a ↪ Fin L)
    (s : Reg L) (x : Reg a) : Reg L := Function.extend e x s

/-- Embed a quantum state by linearly extending the computational basis map induced by
`wireContextExtend`. -/
noncomputable def wireContextEmbed {a L : ℕ} (e : Fin a ↪ Fin L)
    (s : Reg L) (ψ : QState (Reg a)) : QState (Reg L) :=
  ∑ x, ψ x • Ket (wireContextExtend e s x)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
