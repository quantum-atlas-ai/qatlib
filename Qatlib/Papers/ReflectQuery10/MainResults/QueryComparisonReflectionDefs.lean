/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonDefs
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgram
import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionQueryAlgorithmStat
import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionQueryAlgorithmRefl
import Mathlib.Tactic.Linarith

/-!
# Source programs and successful query counts

Defines the source-program data used for reflection-based query comparisons, including input
encodings, circuits, initial states, and input-dependent acceptance events. It also packages
feasible dual witnesses and defines the finite set and minimum of query counts for programs
meeting a uniform success threshold. See [Reichardt2011].

## Main statements

* `SourceProgram.DecidesWithSuccess`: requires the acceptance probability to exceed the
  threshold on every input.
* `sourceMinQueries`: selects the minimum successful query count from a nonempty finite set.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.Reflections

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.ReflectQuery10.MainResults

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A source-program record containing input and target data, a workspace query circuit, an
initial state, and an acceptance event for each input. -/
structure SourceProgram (X : Type) where
  n : ℕ
  r : ℕ
  input : X → Fin n → Bool
  f : X → Bool
  circuit : Circuit ((Fin n × Bool) × Fin r)
  initial : QState ((Fin n × Bool) × Fin r)
  accept : X → Finset ((Fin n × Bool) × Fin r)

/-- The measurement probability of the program's acceptance event after executing its circuit
with the input-dependent workspace bit oracle. -/
noncomputable def SourceProgram.successProb (P : SourceProgram X) (x : X) : ℝ :=
  MeasureProb (Run (workspaceBitOracle (W := Fin P.r) (P.input x)) P.circuit P.initial) (P.accept x)

/-- The condition that the program's acceptance probability is at least `threshold` for every
input. -/
def SourceProgram.DecidesWithSuccess (P : SourceProgram X) (threshold : ℝ) : Prop :=
  ∀ x : X, threshold ≤ P.successProb x

/-- A record of `SourceDualFeasible input f v W` together with the lower bound `1 ≤ W`. -/
structure SourceDualWitness (n m : ℕ) (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) where
  feasible : SourceDualFeasible input f v W
  positive : 1 ≤ W

/-- The finite set of circuit query counts among listed source programs satisfying the specified
uniform success threshold. -/
def sourceQueryCounts (M : List (SourceProgram X)) (threshold : ℝ) : Finset ℕ :=
  (M.filter (fun P => decide (P.DecidesWithSuccess threshold))).map
    (fun P => QueryCount P.circuit) |>.toFinset

/-- The minimum query count among listed programs meeting the threshold, given that this set of
counts is nonempty. -/
noncomputable def sourceMinQueries (M : List (SourceProgram X)) (threshold : ℝ)
    (h : ∃ k, k ∈ sourceQueryCounts M threshold) : ℕ :=
  finsetMinNat (sourceQueryCounts M threshold) h

end Qatlib.Papers.ReflectQuery10.MainResults
