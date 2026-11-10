/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QWalkSpectra04.EndToEnd
namespace WalkApplicationSourceDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

def generalMarkedVertices {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) : Finset V :=
  Finset.univ.filter fun v => (marked v).Nonempty

noncomputable def generalCollisionDecoder {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (v : V) : Option E :=
  if h : (marked v).Nonempty then some (Finset.min' (marked v) h) else none

noncomputable def generalCollisionSuccess {V : Type} [Fintype V] {E : Type} [LinearOrder E]
    (marked : V → Finset E) (ψ : QState V) : ℝ :=
  ∑ v, if (marked v).Nonempty then ‖ψ v‖ ^ 2 else 0

end WalkApplicationSourceDefs
end Qatlib.Papers.QWalkSpectra04.EndToEnd
