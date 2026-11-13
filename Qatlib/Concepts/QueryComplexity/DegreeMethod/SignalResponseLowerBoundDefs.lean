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

/-!
# Adaptive signal words and access costs

This module defines `AdaptiveSignalTree`, pathwise query counts, and finite branch laws for
adaptive signal computations. It also defines `OracleAccessModel`, which realizes forward and
adjoint matrix access by concrete circuits and records gate and bit costs.

The scalar response `fiberResponse` extracts the real encoding-fiber corner of a signal word.
These definitions provide bookkeeping for signal-processing query bounds in the setting of
[GilyenSuLowWiebe2019].

## Main statements

* `AdaptiveSignalTree.pathWord_wellFormed`: path words inherit well-formedness from the tree.
* `AdaptiveSignalTree.pathWord_evaluate`: evaluation decomposes along the chosen branch.
* `fiberResponse_forward`: a single forward query returns the scalar signal.
* `fiberResponse_forward_x`: a word containing a forward query and Pauli X returns the
  complementary square-root response.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019]
-/

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

/-- A finite binary decision tree whose internal nodes carry words of fixed gates and forward or
adjoint oracle queries. -/
inductive AdaptiveSignalTree (H : Type) where
  | leaf : AdaptiveSignalTree H
  | node : List (AdjointStep H) → AdaptiveSignalTree H → AdaptiveSignalTree H → AdaptiveSignalTree H

namespace AdaptiveSignalTree

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The query word stored at the root, with the empty word assigned to a leaf. -/
def rootWord : AdaptiveSignalTree H → List (AdjointStep H)
  | .leaf => []
  | .node w _ _ => w

/-- All Boolean paths from the root to a leaf, with `false` selecting the left subtree and
`true` the right subtree. -/
def paths : AdaptiveSignalTree H → List (List Bool)
  | .leaf => [[]]
  | .node _ t0 t1 =>
      (paths t0).map (fun p => false :: p) ++ (paths t1).map (fun p => true :: p)

/-- Concatenates the words encountered along a Boolean path, stopping at a leaf or when the path
is exhausted. -/
def pathWord (tree : AdaptiveSignalTree H) (p : List Bool) : List (AdjointStep H) :=
  match tree with
  | .leaf => []
  | .node w t0 t1 =>
      match p with
      | [] => w
      | b :: rest => w ++ (if b then t1 else t0).pathWord rest

/-- The number of forward and adjoint oracle queries in the word associated with a path. -/
def pathQueries (tree : AdaptiveSignalTree H) (p : List Bool) : ℕ :=
  adjointQueryCount (tree.pathWord p)

/-- The maximum query count over all root-to-leaf paths of the tree. -/
def worstCaseQueries (tree : AdaptiveSignalTree H) : ℕ :=
  (tree.paths.map (tree.pathQueries)).foldl max 0

/-- The natural-number difference between the worst-case query count and the query count along a
given path. -/
def remainingQueries (tree : AdaptiveSignalTree H) (p : List Bool) : ℕ :=
  tree.worstCaseQueries - tree.pathQueries p

/-- The maximum number of internal nodes along a root-to-leaf path. -/
def depth : AdaptiveSignalTree H → ℕ
  | .leaf => 0
  | .node _ t0 t1 => 1 + max (depth t0) (depth t1)

/-- Requires every word stored at an internal node to be a well-formed adjoint circuit. -/
def WellFormed : AdaptiveSignalTree H → Prop
  | .leaf => True
  | .node w t0 t1 => WellFormedAdjointCircuit w ∧ WellFormed t0 ∧ WellFormed t1

/-- Every path word of a well-formed adaptive signal tree is a well-formed adjoint circuit. -/
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

/-- Evaluation of a path word factors as the root word followed by the selected subtree word,
with the stated leaf and empty-path cases. -/
theorem pathWord_evaluate (tree : AdaptiveSignalTree H) (p : List Bool) (U : Matrix H H ℂ) :
    evaluate U (tree.pathWord p) =
      match tree, p with
      | .leaf, _ => 1
      | .node w _ _, [] => evaluate U w
      | .node w t0 t1, b :: rest =>
          evaluate U w * evaluate U ((if b then t1 else t0).pathWord rest) := by
  cases tree <;> cases p <;> simp [pathWord, evaluate, evaluate_append]

/-- Extends a history by following the decisions determined by the signal parameter and current
history until a leaf is reached. -/
def transcript (tree : AdaptiveSignalTree H) (decide : ℝ → List Bool → Bool) (z : ℝ)
    (hist : List Bool) : List Bool :=
  match tree with
  | .leaf => hist
  | .node _ t0 t1 =>
      match decide z hist with
      | true => t1.transcript decide z (hist ++ [true])
      | false => t0.transcript decide z (hist ++ [false])

/-- The Boolean transcript obtained by running the decision rule from the empty history. -/
def realizedPath (tree : AdaptiveSignalTree H) (decide : ℝ → List Bool → Bool) (z : ℝ) :
    List Bool :=
  tree.transcript decide z []

end AdaptiveSignalTree

/-- A finite list of Boolean paths with nonnegative real weights whose sum is one. -/
structure SignalBranchLaw where

  support : List (List Bool × ℝ)

  nonneg : ∀ e ∈ support, 0 ≤ e.2

  total : (support.map (fun e => e.2)).sum = 1

namespace SignalBranchLaw

/-- The weighted sum of path query counts under a finite branch law. -/
def expectedQueries (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) : ℝ :=
  (law.support.map (fun e => e.2 * (tree.pathQueries e.1 : ℝ))).sum

/-- The total branch-law weight assigned to paths belonging to a specified list. -/
def mass (law : SignalBranchLaw) (S : List (List Bool)) : ℝ :=
  ((law.support.filter (fun e => e.1 ∈ S)).map (fun e => e.2)).sum

/-- The total branch-law weight assigned to paths outside a specified list. -/
def tailMass (law : SignalBranchLaw) (S : List (List Bool)) : ℝ :=
  ((law.support.filter (fun e => e.1 ∉ S)).map (fun e => e.2)).sum

end SignalBranchLaw

/-- A family of square complex matrices indexed by a real signal parameter. -/
abbrev MatrixFamily (I : Type) := ℝ → Matrix I I ℂ

/-- Requires every matrix in a real-parameter family to have operator norm at most one. -/
def BoundedMatrixFamily [Fintype I] [DecidableEq I] (F : MatrixFamily I) : Prop :=
  ∀ z, ‖F z‖ ≤ 1

/-- A realization of forward and adjoint matrix access by query-free circuits, together with bit
costs and matrix-action guarantees. -/
structure OracleAccessModel (I : Type) [Fintype I] [DecidableEq I] where

  realize : Matrix I I ℂ → Bool → Circuit I

  queryFree : ∀ O b, QueryCount (realize O b) = 0

  readBits : Matrix I I ℂ → Bool → ℕ

  forwardRun : ∀ O ψ, Run (1 : Matrix I I ℂ) (realize O false) ψ = O *ᵥ ψ

  backwardRun : ∀ O ψ, Run (1 : Matrix I I ℂ) (realize O true) ψ = Oᴴ *ᵥ ψ

namespace OracleAccessModel

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The circuit realizing forward access when the Boolean flag is `false` and adjoint access
when it is `true`. -/
def accessCircuit (M : OracleAccessModel I) (O : Matrix I I ℂ) (b : Bool) : Circuit I :=
  M.realize O b

/-- The gate count of the circuit realizing the selected direction of matrix access. -/
def accessGateCost (M : OracleAccessModel I) (O : Matrix I I ℂ) (b : Bool) : ℕ :=
  GateCount (M.realize O b)

/-- The smaller of the forward and adjoint access gate costs. -/
def minAccessGateCost (M : OracleAccessModel I) (O : Matrix I I ℂ) : ℕ :=
  min (M.accessGateCost O false) (M.accessGateCost O true)

/-- The smaller of the forward and adjoint access bit costs. -/
def minAccessBitCost (M : OracleAccessModel I) (O : Matrix I I ℂ) : ℕ :=
  min (M.readBits O false) (M.readBits O true)

/-- Realizes a fixed gate as a singleton circuit and replaces each oracle instruction by its
access circuit. -/
def stepCircuit (M : OracleAccessModel I) (O : Matrix I I ℂ) (c : AdjointStep I) : Circuit I :=
  match c with
  | .gate V => [Step.gate V]
  | .forward => M.realize O false
  | .backward => M.realize O true

/-- Compiles an adjoint query word into a circuit, reversing concatenation order to match the
word evaluation convention. -/
def signalWordCircuit (M : OracleAccessModel I) (O : Matrix I I ℂ) :
    List (AdjointStep I) → Circuit I
  | [] => []
  | c :: cs => M.signalWordCircuit O cs ++ M.stepCircuit O c

/-- The sum of gate costs incurred by oracle-access instructions in a word, assigning zero cost
to fixed gates. -/
def realizedWordGateCount (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .gate _ => 0
    | .forward => M.accessGateCost O false
    | .backward => M.accessGateCost O true)).sum

/-- The sum of bit costs incurred by forward and adjoint accesses in a word. -/
def realizedWordBitCost (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .gate _ => 0
    | .forward => M.readBits O false
    | .backward => M.readBits O true)).sum

/-- The indicator that an adjoint-word instruction is a forward oracle access. -/
def forwardAccessCount {I : Type} (c : AdjointStep I) : ℕ :=
  match c with
  | .forward => 1
  | _ => 0

/-- The indicator that an adjoint-word instruction is a backward oracle access. -/
def backwardAccessCount {I : Type} (c : AdjointStep I) : ℕ :=
  match c with
  | .backward => 1
  | _ => 0

/-- The indicator that an adjoint-word instruction is a fixed gate. -/
def gateStepCount {I : Type} (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 1
  | _ => 0

/-- The total forward and backward access count of a single instruction. -/
def instructionAccessCount {I : Type} (c : AdjointStep I) : ℕ :=
  forwardAccessCount c + backwardAccessCount c

/-- The bit cost of an oracle instruction, with zero cost assigned to fixed gates. -/
def instructionBitCost (M : OracleAccessModel I) (O : Matrix I I ℂ) (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 0
  | .forward => M.readBits O false
  | .backward => M.readBits O true

/-- The gate cost of realizing an oracle access, with zero cost assigned to fixed gates. -/
def instructionAccessCost (M : OracleAccessModel I) (O : Matrix I I ℂ) (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 0
  | .forward => M.accessGateCost O false
  | .backward => M.accessGateCost O true

/-- The circuit gate cost of an instruction, counting a fixed gate as one and an access by its
realization cost. -/
def instructionCircuitGateCost (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (c : AdjointStep I) : ℕ :=
  match c with
  | .gate _ => 1
  | .forward => M.accessGateCost O false
  | .backward => M.accessGateCost O true

/-- Encodes one instruction for resource accounting, using a Hadamard macro for a fixed gate and
an oracle step followed by a classical bit charge for an access. -/
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

/-- Concatenates the resource-accounting steps associated with all instructions in a signal
word. -/
def signalWordSteps (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : List Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.DynStep :=
  word.flatMap (M.stepSteps O)

/-- The resource counters obtained from the accounting steps of a signal word. -/
def signalWordAccount (M : OracleAccessModel I) (O : Matrix I I ℂ)
    (word : List (AdjointStep I)) : Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.Account :=
  Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.counters (M.signalWordSteps O word)

end OracleAccessModel

/-- The real scalar response obtained by compressing a scalar-signal word to the `false`
encoding fiber. -/
noncomputable def fiberResponse (z : ℝ) (w : List (AdjointStep (Bool × Unit))) : ℝ :=
  (compress (encodingFiber (I:=Unit) false) (evaluate (scalarSignalLift Unit z) w)
    (encodingFiber (I:=Unit) false) Unit.unit Unit.unit).re

/-- The compressed fiber response equals the real part of the `false`-fiber diagonal matrix
entry. -/
theorem fiberResponse_eq_corner (z : ℝ) (w : List (AdjointStep (Bool × Unit))) :
    fiberResponse z w =
      (evaluate (scalarSignalLift Unit z) w (false, Unit.unit) (false, Unit.unit)).re := by
  rw [fiberResponse, compress_encodingFiber_eq]

/-- A single forward scalar-signal query has fiber response equal to the signal parameter. -/
theorem fiberResponse_forward (z : ℝ) :
    fiberResponse z [AdjointStep.forward] = z := by
  rw [fiberResponse_eq_corner]
  simp [evaluate, instructionMatrix, scalarSignalLift, TensorGate, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.mul_apply, scalarSignalReflection, Complex.ofReal_re]

/-- A forward scalar-signal query followed in word order by a Pauli X gate has fiber response
`Real.sqrt (1 - z ^ 2)`. -/
theorem fiberResponse_forward_x (z : ℝ) :
    fiberResponse z [AdjointStep.forward, AdjointStep.gate (TensorGate PauliX (1 : Matrix Unit Unit ℂ))] =
      Real.sqrt (1 - z ^ 2) := by
  rw [fiberResponse_eq_corner]
  simp [evaluate, instructionMatrix, scalarSignalLift,TensorGate, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, scalarSignalReflection,
    PauliX, permMatrix, Matrix.of_apply, Complex.ofReal_re]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
