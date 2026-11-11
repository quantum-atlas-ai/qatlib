/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic

/-!
# Abstract machine and connectivity interfaces

`GraphInstance` packages a finite regular graph with source and target vertices. `QTM`,
`ReversibleMachine`, and `USTCONMachine` record resource functions and, where applicable,
bounded acceptance probabilities.

The predicates `LogSpace`, `PolyTime`, `DecidesOneSided`, and `InQRHL` state properties of these
records. `Reduces` requires a membership-preserving map without a resource bound, and `InSL` is
the corresponding reduction-based predicate for decoded regular graph connectivity. The
formalization follows [Watrous1998].

## Main statements

* `GraphInstance`: finite regular graph instances with distinguished endpoints.
* `QTM` and `USTCONMachine`: abstract resource and acceptance records.
* `InQRHL` and `InSL`: language predicates used by the machine results.

## References

* [Watrous, 1998][Watrous1998]
-/

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

open Finset
open scoped BigOperators

set_option autoImplicit false

/-- A finite decidable simple graph of degree `d` with decidable adjacency and distinguished
source and target vertices. -/
structure GraphInstance (d : ℕ) where

  V : Type

  [instFintype : Fintype V]

  [instDecEq : DecidableEq V]

  G : SimpleGraph V

  [instDecRel : DecidableRel G.Adj]

  regular : ∀ v : V, (G.neighborFinset v).card = d

  s : V

  t : V

/-- The number of vertices of a graph instance. -/
def InstanceSize {d : ℕ} (I : GraphInstance d) : ℕ := @Fintype.card I.V I.instFintype

/-- The predicate that the source and target vertices of an instance are reachable from each
other. -/
def InstanceConnected {d : ℕ} (I : GraphInstance d) : Prop := I.G.Reachable I.s I.t

/-- An abstract record of space and step functions and a real acceptance function on boolean
lists with values between zero and one. -/
structure QTM where

  space : ℕ → ℕ

  steps : ℕ → ℕ

  acceptProb : List Bool → ℝ

  acceptProb_nonneg : ∀ x, 0 ≤ acceptProb x

  acceptProb_le_one : ∀ x, acceptProb x ≤ 1

/-- The predicate that the space function is bounded by a constant multiple of `Nat.log2 (n + 1)
+ 1`. -/
def LogSpace (M : QTM) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, M.space n ≤ c * (Nat.log2 (n + 1) + 1)

/-- The predicate that `f n` is bounded by `(n + 2) ^ c` for some natural exponent `c`. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, f n ≤ (n + 2) ^ c

/-- The predicate that a machine's step function satisfies `PolyBounded`. -/
def PolyTime (M : QTM) : Prop := PolyBounded M.steps

/-- The predicate that a machine accepts members of `P` with probability at least `p` and
nonmembers with probability zero. -/
def DecidesOneSided (M : QTM) (P : List Bool → Prop) (p : ℝ) : Prop :=
  (∀ x, P x → p ≤ M.acceptProb x) ∧ (∀ x, ¬ P x → M.acceptProb x = 0)

/-- The predicate that a language has a logarithmic-space, polynomial-time `QTM` record deciding
it with one-sided threshold `1 / 2`. -/
def InQRHL (P : List Bool → Prop) : Prop :=
  ∃ M : QTM, LogSpace M ∧ PolyTime M ∧ DecidesOneSided M P (1 / 2)

/-- The predicate that a boolean-list map preserves membership from `A` to `B`, with no resource
bound imposed on the map. -/
def Reduces (A B : List Bool → Prop) : Prop :=
  ∃ f : List Bool → List Bool, ∀ x, A x ↔ B (f x)

/-- The predicate that a language reduces to source-target connectivity for some decoding into
regular graphs of a fixed degree at least three. -/
def InSL (A : List Bool → Prop) : Prop :=
  ∃ (d : ℕ) (decode : List Bool → GraphInstance d),
    3 ≤ d ∧ Reduces A (fun x => InstanceConnected (decode x))

/-- A record of a space function, input-dependent equivalences of the workspace, and step
counts. -/
structure ReversibleMachine (W : Type*) where

  space : ℕ → ℕ

  transform : List Bool → W ≃ W

  steps : List Bool → W → ℕ

/-- The predicate that a reversible machine's space function is bounded by a constant multiple
of `Nat.log2 (n + 1) + 1`. -/
def ReversibleMachine.LogSpace {W : Type*} (M : ReversibleMachine W) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, M.space n ≤ c * (Nat.log2 (n + 1) + 1)

/-- An abstract machine record on degree-`d` graph instances, with space and step functions and
an acceptance function valued between zero and one. -/
structure USTCONMachine (d : ℕ) where

  space : ℕ → ℕ

  steps : GraphInstance d → ℕ

  acceptProb : GraphInstance d → ℝ

  acceptProb_nonneg : ∀ I, 0 ≤ acceptProb I

  acceptProb_le_one : ∀ I, acceptProb I ≤ 1

/-- The predicate that the space usage of a connectivity machine is logarithmically bounded in
the instance vertex count. -/
def USTCONMachine.LogSpace {d : ℕ} (M : USTCONMachine d) : Prop :=
  ∃ c : ℕ, ∀ I : GraphInstance d, M.space (InstanceSize I) ≤ c * (Nat.log2 (InstanceSize I + 1) + 1)

/-- The predicate that the step count is bounded by `(InstanceSize I + 1) ^ c` for some natural
exponent `c`. -/
def USTCONMachine.PolyTime {d : ℕ} (M : USTCONMachine d) : Prop :=
  ∃ c : ℕ, ∀ I : GraphInstance d, M.steps I ≤ (InstanceSize I + 1) ^ c

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
