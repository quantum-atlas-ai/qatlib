/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalQueryBounds
import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalConsumers
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {H I W : Type}

inductive AdaptiveSignalTree (H : Type) where
  | leaf : AdaptiveSignalTree H
  | node : List (AdjointStep H) → AdaptiveSignalTree H → AdaptiveSignalTree H → AdaptiveSignalTree H

namespace AdaptiveSignalTree

variable {H : Type} [Fintype H] [DecidableEq H]

def rootWord : AdaptiveSignalTree H → List (AdjointStep H)
  | .leaf => []
  | .node w _ _ => w

def paths : AdaptiveSignalTree H → List (List Bool)
  | .leaf => [[]]
  | .node _ t0 t1 =>
      (paths t0).map (fun p => false :: p) ++ (paths t1).map (fun p => true :: p)

def pathWord (tree : AdaptiveSignalTree H) (p : List Bool) : List (AdjointStep H) :=
  match tree with
  | .leaf => []
  | .node w t0 t1 =>
      match p with
      | [] => w
      | b :: rest => w ++ (if b then t1 else t0).pathWord rest

def pathQueries (tree : AdaptiveSignalTree H) (p : List Bool) : ℕ :=
  adjointQueryCount (tree.pathWord p)

def worstCaseQueries (tree : AdaptiveSignalTree H) : ℕ :=
  (tree.paths.map (tree.pathQueries)).foldl max 0

def remainingQueries (tree : AdaptiveSignalTree H) (p : List Bool) : ℕ :=
  tree.worstCaseQueries - tree.pathQueries p

def depth : AdaptiveSignalTree H → ℕ
  | .leaf => 0
  | .node _ t0 t1 => 1 + max (depth t0) (depth t1)

def WellFormed : AdaptiveSignalTree H → Prop
  | .leaf => True
  | .node w t0 t1 => WellFormedAdjointCircuit w ∧ WellFormed t0 ∧ WellFormed t1

theorem pathWord_wellFormed (tree : AdaptiveSignalTree H) (p : List Bool) :
    tree.WellFormed → WellFormedAdjointCircuit (tree.pathWord p) := by
  induction tree generalizing p with
  | leaf =>
    intro _
    simp only [pathWord]
    exact WellFormedAdjointCircuit.nil
  | node w t0 t1 ih0 ih1 =>
    intro h
    rcases h with ⟨hw, h0, h1⟩
    cases p with
    | nil =>
      simp only [pathWord]
      exact hw
    | cons b rest =>
      cases b with
      | false =>
        simp only [pathWord]
        exact WellFormedAdjointCircuit.append hw (ih0 rest h0)
      | true =>
        simp only [pathWord]
        exact WellFormedAdjointCircuit.append hw (ih1 rest h1)

theorem pathWord_evaluate (tree : AdaptiveSignalTree H) (p : List Bool) (U : Matrix H H ℂ) :
    evaluate U (tree.pathWord p) =
      match tree, p with
      | .leaf, _ => 1
      | .node w _ _, [] => evaluate U w
      | .node w t0 t1, b :: rest =>
          evaluate U w * evaluate U ((if b then t1 else t0).pathWord rest) := by
  cases tree <;> cases p <;> simp [pathWord, evaluate, evaluate_append]

def transcript (tree : AdaptiveSignalTree H) (decide : ℝ → List Bool → Bool) (z : ℝ)
    (hist : List Bool) : List Bool :=
  match tree with
  | .leaf => hist
  | .node _ t0 t1 =>
      match decide z hist with
      | true => t1.transcript decide z (hist ++ [true])
      | false => t0.transcript decide z (hist ++ [false])

def realizedPath (tree : AdaptiveSignalTree H) (decide : ℝ → List Bool → Bool) (z : ℝ) :
    List Bool :=
  tree.transcript decide z []

end AdaptiveSignalTree

structure SignalBranchLaw where

  support : List (List Bool × ℝ)

  nonneg : ∀ e ∈ support, 0 ≤ e.2

  total : (support.map (fun e => e.2)).sum = 1

namespace SignalBranchLaw

def expectedQueries (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) : ℝ :=
  (law.support.map (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum

def mass (law : SignalBranchLaw) (S : List (List Bool)) : ℝ :=
  ((law.support.filter (fun e => e.1 ∈ S)).map (fun e => e.2)).sum

def tailMass (law : SignalBranchLaw) (S : List (List Bool)) : ℝ :=
  ((law.support.filter (fun e => e.1 ∉ S)).map (fun e => e.2)).sum

end SignalBranchLaw

abbrev MatrixFamily (I : Type) := ℝ → Matrix I I ℂ

def BoundedMatrixFamily [Fintype I] [DecidableEq I] (F : MatrixFamily I) : Prop :=
  ∀ z, ‖F z‖ ≤ 1

structure OracleAccessModel (I : Type) [Fintype I] [DecidableEq I] where

  realize : Matrix I I ℂ → Bool → Circuit I

  queryFree : ∀ O b, QueryCount (realize O b) = 0

  readBits : Matrix I I ℂ → Bool → ℕ

  forwardRun : ∀ O ψ, Run (1 : Matrix I I ℂ) (realize O false) ψ = O *ᵥ ψ

  backwardRun : ∀ O ψ, Run (1 : Matrix I I ℂ) (realize O true) ψ = Oᴴ *ᵥ ψ

namespace OracleAccessModel

variable {I : Type} [Fintype I] [DecidableEq I]

def accessCircuit (M : OracleAccessModel I) (O : Matrix I I ℂ) (b : Bool) : Circuit I :=
  M.realize O b

def accessGateCost (M : OracleAccessModel I) (O : Matrix I I ℂ) (b : Bool) : ℕ :=
  GateCount (M.realize O b)

def minAccessGateCost (M : OracleAccessModel I) (O : Matrix I I ℂ) : ℕ :=
  min (M.accessGateCost O false) (M.accessGateCost O true)

def minAccessBitCost (M : OracleAccessModel I) (O : Matrix I I ℂ) : ℕ :=
  min (M.readBits O false) (M.readBits O true)

def stepCircuit (M : OracleAccessModel I) (O : Matrix I I ℂ) (c : AdjointStep I) : Circuit I :=
  match c with
  | .gate V => [Step.gate V]
  | .forward => M.realize O false
  | .backward => M.realize O true

def signalWordCircuit (M : OracleAccessModel I) (O : Matrix I I ℂ) :
    List (AdjointStep I) → Circuit I
  | [] => []
  | c :: cs => M.signalWordCircuit O cs ++ M.stepCircuit O c

def realizedWordGateCount (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .gate _ => 0
    | .forward => M.accessGateCost O false
    | .backward => M.accessGateCost O true)).sum

def realizedWordBitCost (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .gate _ => 0
    | .forward => M.readBits O false
    | .backward => M.readBits O true)).sum

def forwardAccessCount {I : Type} (c : AdjointStep I) : ℕ :=
  match c with
  | .forward => 1
  | _ => 0

def backwardAccessCount {I : Type} (c : AdjointStep I) : ℕ :=
  match c with
  | .backward => 1
  | _ => 0

def gateStepCount {I : Type} (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 1
  | _ => 0

def instructionAccessCount {I : Type} (c : AdjointStep I) : ℕ :=
  forwardAccessCount c + backwardAccessCount c

def instructionBitCost (M : OracleAccessModel I) (O : Matrix I I ℂ) (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 0
  | .forward => M.readBits O false
  | .backward => M.readBits O true

def instructionAccessCost (M : OracleAccessModel I) (O : Matrix I I ℂ) (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 0
  | .forward => M.accessGateCost O false
  | .backward => M.accessGateCost O true

def instructionCircuitGateCost (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 1
  | .forward => M.accessGateCost O false
  | .backward => M.accessGateCost O true

def stepSteps (M : OracleAccessModel I) (O : Matrix I I ℂ) (c : AdjointStep I) :
    List Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep :=
  match c with
  | .gate _ => [Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep.macro
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode.h 0)]
  | .forward =>
      [Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep.oracle false [],
        Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep.classical (M.readBits O false)]
  | .backward =>
      [Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep.oracle true [],
        Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep.classical (M.readBits O true)]

def signalWordSteps (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : List Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep :=
  word.flatMap (M.stepSteps O)

def signalWordAccount (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.Account :=
  Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.counters (M.signalWordSteps O word)

end OracleAccessModel

noncomputable def fiberResponse (z : ℝ) (w : List (AdjointStep (Bool × Unit))) : ℝ :=
  (compress (encodingFiber (I:=Unit) false) (evaluate (scalarSignalLift Unit z) w)
    (encodingFiber (I:=Unit) false) Unit.unit Unit.unit).re

theorem fiberResponse_eq_corner (z : ℝ) (w : List (AdjointStep (Bool × Unit))) :
    fiberResponse z w =
      (evaluate (scalarSignalLift Unit z) w (false, Unit.unit) (false, Unit.unit)).re := by
  rw [fiberResponse, compress_encodingFiber_eq]

theorem fiberResponse_forward (z : ℝ) :
    fiberResponse z [AdjointStep.forward] = z := by
  rw [fiberResponse_eq_corner]
  simp [evaluate, instructionMatrix, scalarSignalLift, TensorGate, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.mul_apply, scalarSignalReflection, Complex.ofReal_re]

theorem fiberResponse_forward_x (z : ℝ) :
    fiberResponse z [AdjointStep.forward, AdjointStep.gate (TensorGate PauliX (1 : Matrix Unit Unit ℂ))] =
      Real.sqrt (1 - z ^ 2) := by
  rw [fiberResponse_eq_corner]
  simp [evaluate, instructionMatrix, scalarSignalLift,TensorGate, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, scalarSignalReflection,
    PauliX, permMatrix, Matrix.of_apply, Complex.ofReal_re]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
