/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryEffective
import Qatlib.Concepts.AdversaryBounds.AdvDuality.StoppingReferenceTransport
import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingExt
import QuantumInfo.ForMathlib.HermitianMat.CFC

/-!
# Definitions for Loss and Query-Cost Certificates

This module defines the objects used to account for loss and coordinate costs in adversary
arguments. `LossCompletion` packages Kraus operators with a positive semidefinite defect, and
`lossKraus` completes them by its positive square root. `certifiedCutCostE` retains extended
nonnegative costs, while `weightedCutCheck`, `executableCutCost`, and `executableCutWitness`
provide finite-list searches with nonnegative rational costs in the adversary setting of
[HoyerLeeSpalek2007].

`crossFilteredGamma2` and `stateConversionSDPGeneral` formulate filtered matrix differences and
approximate state conversion in the framework of [LeeEtAl2011]. `neverQueryCost`, `neverMass`,
and `acceptedMass` measure the two acceptance events after truncating an instrument circuit to a
query budget; `neverEvent` means that the truncated trace is unaccepted.

## Main statements

- `LossCompletion` and its mass definitions encode genuine and loss outcomes.
* `certifiedCutCostE`, `executableCutCost`, and `executableCutWitness` define mathematical and
  executable cut data.
* `crossFilteredGamma2`, `ZeroFilterInstance`, and `stateConversionSDPGeneral` define filtered
  state-conversion quantities.
* `commonStop`, `neverQueryCost`, `neverMass`, and `acceptedMass` define truncated-query
  accounting.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger.
- [Lee et al., 2011][LeeEtAl2011], Quantum Query Complexity of State Conversion.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.SignedWeights.Representations

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal MatrixOrder
open Qatlib

/-- Packages a finite Kraus family with its positive semidefinite defect, defined as the
identity minus the sum of the Kraus Gram operators. -/
structure LossCompletion (m D : ℕ) where

  kraus : Fin m → Operator D

  defect : Operator D

  defect_eq : defect = 1 - ∑ i, (kraus i)ᴴ * (kraus i)

  defect_pos : defect.PosSemidef

namespace LossCompletion

variable {m D : ℕ}

/-- The positive square root of the stored defect, used as the additional loss Kraus operator. -/
noncomputable def lossKraus (C : LossCompletion m D) : Operator D := CFC.sqrt C.defect

/-- Extends the genuine Kraus family by a single loss outcome whose operator is `lossKraus`. -/
noncomputable def completed (C : LossCompletion m D) : (Fin m ⊕ Unit) → Operator D
  | .inl i => C.kraus i
  | .inr _ => C.lossKraus

/-- Embeds a genuine Kraus index into the completed outcome type. -/
def genuineOutcome (i : Fin m) : Fin m ⊕ Unit := .inl i

/-- The distinguished loss label in the completed outcome type. -/
def lossOutcome : Fin m ⊕ Unit := .inr ()

/-- The real part of the trace of the input operator after conjugation by the Kraus operator for
the chosen completed outcome. -/
noncomputable def branchMass (C : LossCompletion m D) (rho : Operator D)
    (o : Fin m ⊕ Unit) : ℝ :=
  (Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose)).re

/-- The real part of the sum of branch traces over all genuine and loss outcomes. -/
noncomputable def totalMass (C : LossCompletion m D) (rho : Operator D) : ℝ :=
  (∑ o, Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose)).re

/-- The real part of the sum of branch traces over the original genuine Kraus outcomes. -/
noncomputable def genuineMass (C : LossCompletion m D) (rho : Operator D) : ℝ :=
  (∑ i, Matrix.trace ((C.kraus i) * rho * (C.kraus i).conjTranspose)).re

/-- The real part of the branch trace produced by the loss Kraus operator. -/
noncomputable def lossMass (C : LossCompletion m D) (rho : Operator D) : ℝ :=
  (Matrix.trace ((C.lossKraus) * rho * (C.lossKraus).conjTranspose)).re

end LossCompletion

/-- The least extended nonnegative cost among coordinates separating `x` and `y`, with value
zero when no coordinate separates them. -/
noncomputable def certifiedCutCostE {X : Type} [Fintype X] [DecidableEq X] {κ : Type}
    [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A)
    (beta : κ → ℝ≥0∞) (x y : X) : ℝ≥0∞ :=
  if h : (separatingCoords input x y).Nonempty then
    (separatingCoords input x y).inf' h (fun j => beta j)
  else 0

/-- Nonnegative rational numbers used as executable coordinate costs. -/
abbrev RationalCost := ℚ≥0

/-- Decides whether a coordinate separates the two inputs and has strictly positive rational
cost. -/
def weightedCutCheck {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) (j : κ) : Bool :=
  decide (input x j ≠ input y j ∧ 0 < beta j)

/-- Filters the candidate list to coordinates that separate the inputs and have strictly
positive rational cost. -/
def certifyingCoords {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) (candidates : List κ) : List κ :=
  candidates.filter (fun j => weightedCutCheck input beta x y j)

/-- Computes the minimum of a list of nonnegative rational costs, returning `none` for an empty
list. -/
def minRationalCost : List RationalCost → Option RationalCost
  | [] => none
  | c :: cs => match minRationalCost cs with
    | none => some c
    | some c' => some (min c c')

/-- Computes the minimum cost among candidate coordinates passing `weightedCutCheck`, returning
`none` if there are no such candidates. -/
def executableCutCost {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) (candidates : List κ) : Option RationalCost :=
  minRationalCost ((certifyingCoords input beta x y candidates).map beta)

/-- Searches the candidate list in order and returns the first coordinate passing
`weightedCutCheck`, or `none` if none passes. -/
def executableCutWitness {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) : List κ → Option κ
  | [] => none
  | j :: js => if weightedCutCheck input beta x y j then some j
      else executableCutWitness input beta x y js

/-- The Hadamard product of the coordinate difference filter with `rho - sigma`. -/
def crossFilteredDifference {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    {A : Type} [DecidableEq A] (input : X → Fin n → A) (rho sigma : Matrix X X ℂ)
    (j : Fin n) : Matrix X X ℂ :=
  genFilterDelta input j ⊙ (rho - sigma)

/-- The extended filtered gamma-two value of a matrix difference with respect to the input
coordinate difference filters, following the framework of [LeeEtAl2011]. -/
noncomputable def crossFilteredGamma2 {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    {A : Type} [DecidableEq A] (input : X → Fin n → A) (diff : Matrix X X ℂ) :
    ℝ≥0∞ :=
  filteredGamma2 diff (genFilterDelta input)

/-- Says that every coordinate difference filter of the input encoding is zero. -/
def ZeroFilterInstance {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    {A : Type} [DecidableEq A] (input : X → Fin n → A) : Prop :=
  ∀ j, genFilterDelta input j = 0

/-- Says that the chosen coordinate takes one common alphabet value on every input. -/
def ConstantCoordinate {X : Type} [DecidableEq X] {n : ℕ} {A : Type} [DecidableEq A]
    (input : X → Fin n → A) (j : Fin n) : Prop :=
  ∃ a : A, ∀ x, input x j = a

/-- The infimum of filtered gamma-two costs from `rho` to positive semidefinite matrices
`sigma'` whose difference from `sigma` has an all-ones filtered certificate of budget
`delta`. This is an approximate state-conversion quantity in the framework of [LeeEtAl2011]. -/
noncomputable def stateConversionSDPGeneral {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} {A : Type} [DecidableEq A] (input : X → Fin n → A) (delta : ℝ)
    (rho sigma : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ sigma' : {sigma' : Matrix X X ℂ // sigma'.PosSemidef ∧
      gramFilteredCert (sigma' - sigma) (fun _ : Fin 1 => gramFilterAllOnes) delta},
    crossFilteredGamma2 input (rho - sigma'.1)

/-- Decides whether the query count is at most the common query budget. -/
def commonStop (budget queries : ℕ) : Bool := decide (queries ≤ budget)

/-- The event that the acceptance flag is false, independently of the outcome history. -/
def neverEvent : Bool → List (ℕ × ℕ) → Bool :=
  fun accepted _ => !accepted

/-- Sums mass times query count over unaccepted mixed traces of the circuit truncated at `K`
queries. -/
noncomputable def neverQueryCost {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) : ℝ :=
  ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
    if neverEvent t.accepted t.outcomes then mixedMass t * t.queries else 0).sum

/-- The event mass of unaccepted traces after truncating the circuit at query budget `K`. -/
noncomputable def neverMass {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) : ℝ :=
  instrumentCircuitEventMass O (truncateInstrumentQueries P K) rho neverEvent

/-- The event mass of accepted traces after truncating the circuit at query budget `K`. -/
noncomputable def acceptedMass {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) : ℝ :=
  instrumentCircuitEventMass O (truncateInstrumentQueries P K) rho (fun accepted _ => accepted)

end Qatlib.Concepts.SignedWeights.Representations
