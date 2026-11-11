/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Algorithm and solution predicates for graph queries

This module packages normalized unitary bit-query algorithms and finite randomized families,
with acceptance probabilities and query costs. It defines reachability, connectivity,
spanning-tree and minimum-weight predicates, and the finite selection predicates used for minima
of different types.

The source paper is [DurrEtAl2006].

## Main statements

* `BitAlgorithm`: A unitary bit-query circuit with a normalized initial state and a finite
  workspace.
* `IsMST`: A spanning tree whose total edge weight is no larger than that of any spanning tree.
* `IsMinDifferentTypeSolution`: A size-d selection of distinct types such that every smaller
  unselected value has a selected representative of its type with no larger value.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch

open scoped BigOperators

/-- A unitary bit-query circuit with a normalized initial state and a finite workspace. -/
structure BitAlgorithm (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where

  circuit : Circuit ((Fin n × Bool) × W)

  init : QState ((Fin n × Bool) × W)

  unitary : IsUnitaryCircuit circuit

  normalized : Normalized init

namespace BitAlgorithm

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The probability that running a bit-query algorithm on input `x` produces an outcome in
`out`. -/
noncomputable def acceptProb (A : BitAlgorithm n W) (x : Fin n → Bool)
    (out : Finset ((Fin n × Bool) × W)) : ℝ :=
  MeasureProb (Run (workspaceBitOracle (W := W) x) A.circuit A.init) out

/-- The number of query instructions in a bit-query algorithm. -/
def cost (A : BitAlgorithm n W) : ℕ := QueryCount A.circuit

end BitAlgorithm

/-- The algorithm assigns probability at least 1 − eps to the specified correct outcomes on
every input. -/
def SolvesSearch {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : BitAlgorithm n W) (correct : (Fin n → Bool) → Finset ((Fin n × Bool) × W))
    (eps : ℝ) : Prop :=
  ∀ x, 1 - eps ≤ A.acceptProb x (correct x)

/-- The algorithm assigns probability at least 1 − eps to `yes` on true inputs and to `no` on
false inputs. -/
def SolvesDecision {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : BitAlgorithm n W) (lang : (Fin n → Bool) → Bool)
    (yes no : Finset ((Fin n × Bool) × W)) (eps : ℝ) : Prop :=
  (∀ x, lang x = true → 1 - eps ≤ A.acceptProb x yes) ∧
    ∀ x, lang x = false → 1 - eps ≤ A.acceptProb x no

/-- A finite family of bit-query algorithms with nonnegative weights summing to one. -/
structure RandomizedAlgorithm (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where

  Run_ : Type
  [fintypeRun : Fintype Run_]

  weight : Run_ → ℝ

  alg : Run_ → BitAlgorithm n W
  weight_nonneg : ∀ r, 0 ≤ weight r
  weight_sum : (∑ r, weight r) = 1

/-- The weighted sum of the query counts of the algorithms in a finite randomized family. -/
noncomputable def RandomizedAlgorithm.expectedCost {n : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] (R : RandomizedAlgorithm n W) : ℝ :=
  letI := R.fintypeRun
  ∑ r, R.weight r * (QueryCount (R.alg r).circuit : ℝ)

/-- Every algorithm in the randomized family satisfies the specified search success guarantee. -/
def RandomizedAlgorithm.SolvesSearch {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (R : RandomizedAlgorithm n W) (correct : (Fin n → Bool) → Finset ((Fin n × Bool) × W))
    (eps : ℝ) : Prop :=
  ∀ r, ProblemDefs.SolvesSearch (R.alg r) correct eps

/-- Reflexive transitive reachability in the directed Boolean adjacency relation. -/
def Reach {V : Type*} (adj : V → V → Bool) : V → V → Prop :=
  Relation.ReflTransGen fun a b => adj a b = true

/-- Every two vertices in the specified finite set are mutually reachable in the ambient
directed graph. -/
def StronglyConnectedOn {V : Type*} (adj : V → V → Bool) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, Reach adj u v ∧ Reach adj v u

/-- Every two vertices in the specified finite set are reachable in the symmetrized ambient
graph. -/
def ConnectedOn {V : Type*} (adj : V → V → Bool) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, Reach (fun a b => adj a b || adj b a) u v

/-- The finite edge set uses edges of the symmetrized graph, has n − 1 edges, and connects all
vertices. -/
def IsSpanningTree {n : ℕ} (adj : Fin n → Fin n → Bool)
    (T : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ T, adj e.1 e.2 = true ∨ adj e.2 e.1 = true) ∧
    T.card = n - 1 ∧
    ConnectedOn (fun a b => T.toList.any fun e => (e.1 = a ∧ e.2 = b) || (e.1 = b ∧ e.2 = a))
      (Finset.univ : Finset (Fin n))

/-- The sum of the assigned weights of the ordered edges in a finite edge set. -/
noncomputable def edgeWeight {n : ℕ} (w : Fin n → Fin n → ℕ)
    (T : Finset (Fin n × Fin n)) : ℕ :=
  ∑ e ∈ T, w e.1 e.2

/-- A spanning tree whose total edge weight is no larger than that of any spanning tree. -/
def IsMST {n : ℕ} (adj : Fin n → Fin n → Bool) (w : Fin n → Fin n → ℕ)
    (T : Finset (Fin n × Fin n)) : Prop :=
  IsSpanningTree adj T ∧ ∀ S, IsSpanningTree adj S → edgeWeight w T ≤ edgeWeight w S

/-- A size-d selection of distinct types such that every smaller unselected value has a selected
representative of its type with no larger value. -/
def IsMinDifferentTypeSolution {N : ℕ} (f g : Fin N → ℕ) (d : ℕ)
    (I : Finset (Fin N)) : Prop :=
  I.card = d ∧
    (∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → g i ≠ g i') ∧
    ∀ j ∉ I, ∀ i ∈ I, f j < f i → ∃ i' ∈ I, g i' = g j ∧ f i' ≤ f j

/-- A size-d selection whose values are no larger than any unselected value. -/
def IsMinValuesSolution {N : ℕ} (f : Fin N → ℕ) (d : ℕ) (I : Finset (Fin N)) : Prop :=
  I.card = d ∧ ∀ j ∉ I, ∀ i ∈ I, f i ≤ f j

/-- A size-d selection with pairwise distinct types. -/
def IsDifferentTypeSolution {N : ℕ} (g : Fin N → ℕ) (d : ℕ)
    (I : Finset (Fin N)) : Prop :=
  I.card = d ∧ ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → g i ≠ g i'

end Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs
