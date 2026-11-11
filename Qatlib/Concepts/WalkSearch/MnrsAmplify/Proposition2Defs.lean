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

/-!
# Accounting for walk reflection circuits

Defines the execution and resource counters for six labelled operations in the MNRS
walk-with-data construction [MagniezNayakRolandSantha2011]. The labels distinguish update
operations from the two zero-register reflections, and `mnrsWalkAccountedCost` charges the
update count in an arbitrary additive commutative monoid.

## Main statements

* `mnrsWalkUpdateCount`: Counts circuit labels other than `1` and `4`, the labels designated as
  update operations.
* `mnrsWalkRun`: Executes the labelled gates in list order by folding their actions over the
  input state.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

/-- Counts circuit labels other than `1` and `4`, the labels designated as update operations. -/
def mnrsWalkUpdateCount (circuit : List (Fin 6)) : ℕ :=
  (circuit.map (fun i => if i = 1 ∨ i = 4 then (0 : ℕ) else 1)).sum
/-- Counts occurrences of labels `1` and `4`, the two designated zero-register reflection
operations. -/
def mnrsWalkZeroCount (circuit : List (Fin 6)) : ℕ :=
  (circuit.map (fun i => if i = 1 ∨ i = 4 then (1 : ℕ) else 0)).sum
/-- Charges one copy of `U` for each update operation counted by `mnrsWalkUpdateCount`. -/
def mnrsWalkAccountedCost {C : Type*} [AddCommMonoid C]
    (U : C) (circuit : List (Fin 6)) : C :=
  mnrsWalkUpdateCount circuit • U
/-- Executes the labelled gates in list order by folding their actions over the input state. -/
def mnrsWalkRun {H : Type*} (gates : Fin 6 → H → H)
    (circuit : List (Fin 6)) (v : H) : H :=
  circuit.foldl (fun w i => gates i w) v

end Qatlib.Concepts.WalkSearch.MnrsAmplify
