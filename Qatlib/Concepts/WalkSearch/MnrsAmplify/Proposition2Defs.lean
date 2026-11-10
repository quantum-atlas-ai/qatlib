/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Operations
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Relation
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

def mnrsWalkUpdateCount (circuit : List (Fin 6)) : ℕ :=
  (circuit.map (fun i => if i = 1 ∨ i = 4 then (0 : ℕ) else 1)).sum
def mnrsWalkZeroCount (circuit : List (Fin 6)) : ℕ :=
  (circuit.map (fun i => if i = 1 ∨ i = 4 then (1 : ℕ) else 0)).sum
def mnrsWalkAccountedCost {C : Type*} [AddCommMonoid C]
    (U : C) (circuit : List (Fin 6)) : C :=
  mnrsWalkUpdateCount circuit • U
def mnrsWalkRun {H : Type*} (gates : Fin 6 → H → H)
    (circuit : List (Fin 6)) (v : H) : H :=
  circuit.foldl (fun w i => gates i w) v

end Qatlib.Concepts.WalkSearch.MnrsAmplify
