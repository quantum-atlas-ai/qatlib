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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
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

structure SourceProgram (X : Type) where
  n : ℕ
  r : ℕ
  input : X → Fin n → Bool
  f : X → Bool
  circuit : Circuit ((Fin n × Bool) × Fin r)
  initial : QState ((Fin n × Bool) × Fin r)
  accept : X → Finset ((Fin n × Bool) × Fin r)

noncomputable def SourceProgram.successProb (P : SourceProgram X) (x : X) : ℝ :=
  MeasureProb (Run (workspaceBitOracle (W := Fin P.r) (P.input x)) P.circuit P.initial) (P.accept x)

def SourceProgram.DecidesWithSuccess (P : SourceProgram X) (threshold : ℝ) : Prop :=
  ∀ x : X, threshold ≤ P.successProb x

structure SourceDualWitness (n m : ℕ) (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ) where
  feasible : SourceDualFeasible input f v W
  positive : 1 ≤ W

def sourceQueryCounts (M : List (SourceProgram X)) (threshold : ℝ) : Finset ℕ :=
  (M.filter (fun P => decide (P.DecidesWithSuccess threshold))).map
    (fun P => QueryCount P.circuit) |>.toFinset

noncomputable def sourceMinQueries (M : List (SourceProgram X)) (threshold : ℝ)
    (h : ∃ k, k ∈ sourceQueryCounts M threshold) : ℕ :=
  finsetMinNat (sourceQueryCounts M threshold) h

end Qatlib.Papers.ReflectQuery10.MainResults
