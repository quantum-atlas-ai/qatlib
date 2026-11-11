/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeDataNeumann
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! A coherent family of native data bodies sharing one actual oracle query.
The label-dependent gates below are macros; no elementary SELECT synthesis or
Python gate-word correspondence is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep

variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

/-- Label-dependent known macros and one shared query to the controlled original
oracle. Each branch may independently use either slack convention. -/
def nativeMultiNodeBodyWord (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    List (AdjointStep (J × (Reg 6 × H))) :=
  [.gate (select (fun j => TensorGate (program (invWord (prepWord (ps j)))) (1 : Matrix H H ℂ))),
   .gate (select (fun j => TensorGate (program (phaseWord (p j) (slack j))) (1 : Matrix H H ℂ))),
   .forward,
   .gate (select (fun j => TensorGate (program (prepWord (ps j))) (1 : Matrix H H ℂ)))]

/-- On all label sectors simultaneously the shared-query word evaluates to
the actual expanded native body for that sector, not a supplied target gate. -/
theorem nativeMultiNodeBody_evaluate (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) (U : Matrix H H ℂ) :
    evaluate (parallelOracle (J := J) (nativeDataQuery U))
      (nativeMultiNodeBodyWord (H := H) ps p slack) =
      select (fun j => evaluate (nativeDataQuery U)
        (nativeExpandedBodyWord (H := H) (ps j) (p j) (slack j))) := by
  simp only [nativeMultiNodeBodyWord, evaluate, instructionMatrix, Matrix.mul_one,
    parallelOracle, parallel_select_mul]
  apply congrArg select
  funext j
  rw [nativeExpandedBody_evaluate]
  simp only [nativeBodyWord, evaluate, instructionMatrix, Matrix.mul_one]

omit [Fintype J] [Fintype H] in
/-- Exactly one charged shared query, with three selected known macros. -/
theorem nativeMultiNodeBody_cost (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) :
    adjointQueryCount (nativeMultiNodeBodyWord (H := H) ps p slack) = 1 ∧
    adjointGateCount (nativeMultiNodeBodyWord (H := H) ps p slack) = 3 := by
  simp [nativeMultiNodeBodyWord, adjointQueryCount, adjointGateCount]

/-- The macro SELECT gates are unitary on every label sector. -/
theorem nativeMultiNodeBody_legal (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    WellFormedAdjointCircuit (nativeMultiNodeBodyWord (H := H) ps p slack) := by
  have hsector (j : J) := nativeBodyWord_legal (H := H) (ps j) (p j) (slack j)
  simp only [nativeBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil,
    and_true] at hsector
  have h1 : select (fun j => TensorGate (program (invWord (prepWord (ps j))))
      (1 : Matrix H H ℂ)) ∈ unitaryGroup (J × (Reg 6 × H)) ℂ := by
    apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
    intro j
    exact (hsector j).1
  have h2 : select (fun j => TensorGate (program (phaseWord (p j) (slack j)))
      (1 : Matrix H H ℂ)) ∈ unitaryGroup (J × (Reg 6 × H)) ℂ := by
    apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
    intro j
    exact (hsector j).2.1
  have h3 : select (fun j => TensorGate (program (prepWord (ps j)))
      (1 : Matrix H H ℂ)) ∈ unitaryGroup (J × (Reg 6 × H)) ℂ := by
    apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
    intro j
    exact (hsector j).2.2
  simpa only [nativeMultiNodeBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil,
    and_true] using And.intro h1 (And.intro h2 h3)

/-- The real adjoint word gives the adjoint of each actual branch and still
uses one shared query in the backward direction. -/
theorem nativeMultiNodeBody_adjoint (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : J → Bool) (U : Matrix H H ℂ) :
    evaluate (parallelOracle (J := J) (nativeDataQuery U))
      (adjointCircuit (nativeMultiNodeBodyWord (H := H) ps p slack)) =
      select (fun j => evaluate (nativeDataQuery U)
        (adjointCircuit (nativeExpandedBodyWord (H := H) (ps j) (p j) (slack j)))) ∧
    adjointQueryCount (adjointCircuit (nativeMultiNodeBodyWord (H := H) ps p slack)) = 1 := by
  constructor
  · rw [evaluate_adjointCircuit, nativeMultiNodeBody_evaluate, parallel_select_adjoint]
    apply congrArg select
    funext j
    rw [evaluate_adjointCircuit]
  · rw [adjointQueryCount_adjointCircuit]
    exact (nativeMultiNodeBody_cost (H := H) ps p slack).1

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
