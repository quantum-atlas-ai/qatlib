/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs

/-!
# Witness decoding and success functionals

A finite witness assignment defines `generalMarkedVertices`, the least-witness decoder
`generalCollisionDecoder`, and the marked-coordinate mass `generalCollisionSuccess`. These
definitions supply the decoding and output quantities for walk applications in the setting of
[Szegedy2004].

## Main statements

* `generalMarkedVertices`: selects vertices with at least one witness.
* `generalCollisionDecoder`: returns the least available witness.
* `generalCollisionSuccess`: sums the squared coordinate norms on marked vertices.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QWalkSpectra04.EndToEnd
namespace WalkApplicationSourceDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- The finite set of vertices whose assigned witness sets are nonempty. -/
def generalMarkedVertices {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) : Finset V :=
  Finset.univ.filter fun v => (marked v).Nonempty

/-- The decoder returning the least witness at a vertex when its witness set is nonempty, and
`none` otherwise. -/
noncomputable def generalCollisionDecoder {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (v : V) : Option E :=
  if h : (marked v).Nonempty then some (Finset.min' (marked v) h) else none

/-- The sum of squared state-coordinate norms over vertices with a nonempty witness set. -/
noncomputable def generalCollisionSuccess {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (ψ : QState V) : ℝ :=
  ∑ v, if (marked v).Nonempty then ‖ψ v‖ ^ 2 else 0

end WalkApplicationSourceDefs
end Qatlib.Papers.QWalkSpectra04.EndToEnd
