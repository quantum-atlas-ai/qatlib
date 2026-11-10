/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryEffective
import Qatlib.Concepts.AdversaryBounds.AdvDuality.StoppingReferenceTransport
import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingExt
import QuantumInfo.ForMathlib.HermitianMat.CFC
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

structure LossCompletion (m D : ℕ) where

  kraus : Fin m → Operator D

  defect : Operator D

  defect_eq : defect = 1 - ∑ i, (kraus i)ᴴ * (kraus i)

  defect_pos : defect.PosSemidef

namespace LossCompletion

variable {m D : ℕ}

noncomputable def lossKraus (C : LossCompletion m D) : Operator D := CFC.sqrt C.defect

noncomputable def completed (C : LossCompletion m D) : (Fin m ⊕ Unit) → Operator D
  | .inl i => C.kraus i
  | .inr _ => C.lossKraus

def genuineOutcome (i : Fin m) : Fin m ⊕ Unit := .inl i

def lossOutcome : Fin m ⊕ Unit := .inr ()

noncomputable def branchMass (C : LossCompletion m D) (rho : Operator D)
    (o : Fin m ⊕ Unit) : ℝ :=
  (Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose)).re

noncomputable def totalMass (C : LossCompletion m D) (rho : Operator D) : ℝ :=
  (∑ o, Matrix.trace ((C.completed o) * rho * (C.completed o).conjTranspose)).re

noncomputable def genuineMass (C : LossCompletion m D) (rho : Operator D) : ℝ :=
  (∑ i, Matrix.trace ((C.kraus i) * rho * (C.kraus i).conjTranspose)).re

noncomputable def lossMass (C : LossCompletion m D) (rho : Operator D) : ℝ :=
  (Matrix.trace ((C.lossKraus) * rho * (C.lossKraus).conjTranspose)).re

end LossCompletion

noncomputable def certifiedCutCostE {X : Type} [Fintype X] [DecidableEq X] {κ : Type}
    [Fintype κ] [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A)
    (beta : κ → ℝ≥0∞) (x y : X) : ℝ≥0∞ :=
  if h : (separatingCoords input x y).Nonempty then
    (separatingCoords input x y).inf' h (fun j => beta j)
  else 0

abbrev RationalCost := ℚ≥0

def weightedCutCheck {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) (j : κ) : Bool :=
  decide (input x j ≠ input y j ∧ 0 < beta j)

def certifyingCoords {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) (candidates : List κ) : List κ :=
  candidates.filter (fun j => weightedCutCheck input beta x y j)

def minRationalCost : List RationalCost → Option RationalCost
  | [] => none
  | c :: cs => match minRationalCost cs with
    | none => some c
    | some c' => some (min c c')

def executableCutCost {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) (candidates : List κ) : Option RationalCost :=
  minRationalCost ((certifyingCoords input beta x y candidates).map beta)

def executableCutWitness {X : Type} [DecidableEq X] {κ : Type} [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → RationalCost)
    (x y : X) : List κ → Option κ
  | [] => none
  | j :: js => if weightedCutCheck input beta x y j then some j
      else executableCutWitness input beta x y js

def crossFilteredDifference {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    {A : Type} [DecidableEq A] (input : X → Fin n → A) (rho sigma : Matrix X X ℂ)
    (j : Fin n) : Matrix X X ℂ :=
  genFilterDelta input j ⊙ (rho - sigma)

noncomputable def crossFilteredGamma2 {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    {A : Type} [DecidableEq A] (input : X → Fin n → A) (diff : Matrix X X ℂ) :
    ℝ≥0∞ :=
  filteredGamma2 diff (genFilterDelta input)

def ZeroFilterInstance {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    {A : Type} [DecidableEq A] (input : X → Fin n → A) : Prop :=
  ∀ j, genFilterDelta input j = 0

def ConstantCoordinate {X : Type} [DecidableEq X] {n : ℕ} {A : Type} [DecidableEq A]
    (input : X → Fin n → A) (j : Fin n) : Prop :=
  ∃ a : A, ∀ x, input x j = a

noncomputable def stateConversionSDPGeneral {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} {A : Type} [DecidableEq A] (input : X → Fin n → A) (delta : ℝ)
    (rho sigma : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ sigma' : {sigma' : Matrix X X ℂ // sigma'.PosSemidef ∧
      gramFilteredCert (sigma' - sigma) (fun _ : Fin 1 => gramFilterAllOnes) delta},
    crossFilteredGamma2 input (rho - sigma'.1)

def commonStop (budget queries : ℕ) : Bool := decide (queries ≤ budget)

def neverEvent : Bool → List (ℕ × ℕ) → Bool :=
  fun accepted _ => !accepted

noncomputable def neverQueryCost {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) : ℝ :=
  ((instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho).map fun t =>
    if neverEvent t.accepted t.outcomes then mixedMass t * t.queries else 0).sum

noncomputable def neverMass {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) : ℝ :=
  instrumentCircuitEventMass O (truncateInstrumentQueries P K) rho neverEvent

noncomputable def acceptedMass {d : ℕ} (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) : ℝ :=
  instrumentCircuitEventMass O (truncateInstrumentQueries P K) rho (fun accepted _ => accepted)

end Qatlib.Concepts.SignedWeights.Representations
