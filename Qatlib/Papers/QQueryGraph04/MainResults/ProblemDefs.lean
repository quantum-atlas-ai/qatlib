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
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch

open scoped BigOperators

structure BitAlgorithm (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where

  circuit : Circuit ((Fin n × Bool) × W)

  init : QState ((Fin n × Bool) × W)

  unitary : IsUnitaryCircuit circuit

  normalized : Normalized init

namespace BitAlgorithm

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

noncomputable def acceptProb (A : BitAlgorithm n W) (x : Fin n → Bool)
    (out : Finset ((Fin n × Bool) × W)) : ℝ :=
  MeasureProb (Run (workspaceBitOracle (W := W) x) A.circuit A.init) out

def cost (A : BitAlgorithm n W) : ℕ := QueryCount A.circuit

end BitAlgorithm

def SolvesSearch {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : BitAlgorithm n W) (correct : (Fin n → Bool) → Finset ((Fin n × Bool) × W))
    (eps : ℝ) : Prop :=
  ∀ x, 1 - eps ≤ A.acceptProb x (correct x)

def SolvesDecision {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : BitAlgorithm n W) (lang : (Fin n → Bool) → Bool)
    (yes no : Finset ((Fin n × Bool) × W)) (eps : ℝ) : Prop :=
  (∀ x, lang x = true → 1 - eps ≤ A.acceptProb x yes) ∧
    ∀ x, lang x = false → 1 - eps ≤ A.acceptProb x no

structure RandomizedAlgorithm (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where

  Run_ : Type
  [fintypeRun : Fintype Run_]

  weight : Run_ → ℝ

  alg : Run_ → BitAlgorithm n W
  weight_nonneg : ∀ r, 0 ≤ weight r
  weight_sum : (∑ r, weight r) = 1

noncomputable def RandomizedAlgorithm.expectedCost {n : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] (R : RandomizedAlgorithm n W) : ℝ :=
  letI := R.fintypeRun
  ∑ r, R.weight r * (QueryCount (R.alg r).circuit : ℝ)

def RandomizedAlgorithm.SolvesSearch {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (R : RandomizedAlgorithm n W) (correct : (Fin n → Bool) → Finset ((Fin n × Bool) × W))
    (eps : ℝ) : Prop :=
  ∀ r, ProblemDefs.SolvesSearch (R.alg r) correct eps

def Reach {V : Type*} (adj : V → V → Bool) : V → V → Prop :=
  Relation.ReflTransGen fun a b => adj a b = true

def StronglyConnectedOn {V : Type*} (adj : V → V → Bool) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, Reach adj u v ∧ Reach adj v u

def ConnectedOn {V : Type*} (adj : V → V → Bool) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, Reach (fun a b => adj a b || adj b a) u v

def IsSpanningTree {n : ℕ} (adj : Fin n → Fin n → Bool)
    (T : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ T, adj e.1 e.2 = true ∨ adj e.2 e.1 = true) ∧
    T.card = n - 1 ∧
    ConnectedOn (fun a b => T.toList.any fun e => (e.1 = a ∧ e.2 = b) || (e.1 = b ∧ e.2 = a))
      (Finset.univ : Finset (Fin n))

noncomputable def edgeWeight {n : ℕ} (w : Fin n → Fin n → ℕ)
    (T : Finset (Fin n × Fin n)) : ℕ :=
  ∑ e ∈ T, w e.1 e.2

def IsMST {n : ℕ} (adj : Fin n → Fin n → Bool) (w : Fin n → Fin n → ℕ)
    (T : Finset (Fin n × Fin n)) : Prop :=
  IsSpanningTree adj T ∧ ∀ S, IsSpanningTree adj S → edgeWeight w T ≤ edgeWeight w S

def IsMinDifferentTypeSolution {N : ℕ} (f g : Fin N → ℕ) (d : ℕ)
    (I : Finset (Fin N)) : Prop :=
  I.card = d ∧
    (∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → g i ≠ g i') ∧
    ∀ j ∉ I, ∀ i ∈ I, f j < f i → ∃ i' ∈ I, g i' = g j ∧ f i' ≤ f j

def IsMinValuesSolution {N : ℕ} (f : Fin N → ℕ) (d : ℕ) (I : Finset (Fin N)) : Prop :=
  I.card = d ∧ ∀ j ∉ I, ∀ i ∈ I, f i ≤ f j

def IsDifferentTypeSolution {N : ℕ} (g : Fin N → ℕ) (d : ℕ)
    (I : Finset (Fin N)) : Prop :=
  I.card = d ∧ ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → g i ≠ g i'

end Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs
