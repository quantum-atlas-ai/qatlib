/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.ShiftedEncodingModel
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.ShiftCoefficients
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.CopyEvolution.Discriminate

/-!
# Literal raw controlled-oracle shifted body

The fixed wire permutation exposes exactly one call to the supplied controlled
oracle.  The same literal product-order word realizes the complete coefficient
LCU body, and its actual adjoint retains all query and macro charges.  These
identities hold without legal-parameter or unitarity hypotheses.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix

/-- The fixed wire transport turns the logical SELECT into the actual
spectator lift of the supplied controlled oracle. -/
theorem raw_shifted_query_relabel (H L : Type) [DecidableEq H] [DecidableEq L]
    (U : Matrix H H ℂ) :
    relabelGate (shiftWireEquiv L H) (shiftedSelect (L := L) U) = rawShiftedQuery U := by
  ext ⟨⟨j, k⟩, b, h⟩ ⟨⟨j', k'⟩, b', h'⟩
  change (if j = j' then
      if (b, k) = (b', k') then (if b then U else 1) h h' else 0 else 0) =
    (if (j, k) = (j', k') then
      if b = b' then (if b then U else 1) h h' else 0 else 0)
  by_cases hj : j = j'
  · by_cases hk : k = k'
    · simp [hj, hk]
    · simp [hj, hk]
  · simp [hj]

/-- The coefficient phases are known scalar gates in front of the actual
unknown SELECT, including the total zero-coefficient phase convention. -/
theorem shiftedPhase_mul_shiftedSelect (H L : Type) [Fintype H] [DecidableEq H]
    [Fintype L] [DecidableEq L] (α B₀ : ℝ) (z : L → ℂ) (U : Matrix H H ℂ) :
    shiftedPhase (H := H) α B₀ z * shiftedSelect (L := L) U =
      select (fun j => select (phaseAbsorbed (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient (z j) α B₀)
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U))) := by
  unfold shiftedPhase shiftedSelect
  rw [parallel_select_mul]
  apply congrArg (fun V : L → Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot × H) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot × H) ℂ => select V)
  funext j
  rw [parallel_select_mul]
  apply congrArg (fun V : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot → Matrix H H ℂ => select V)
  funext s
  simp only [phaseAbsorbed, Matrix.smul_mul, Matrix.one_mul]

/-- The literal logical program equals the complete computed coefficient LCU
matrix for arbitrary coefficient parameters and an arbitrary oracle matrix. -/
theorem shifted_body_factorization (H L : Type) [Fintype H] [DecidableEq H]
    [Fintype L] [DecidableEq L] (α B₀ : ℝ) (z : L → ℂ) (U : Matrix H H ℂ) :
    (shiftedPrepare (H := H) α B₀ z)ᴴ * shiftedPhase α B₀ z *
        shiftedSelect U * shiftedPrepare α B₀ z =
      select (fun j => coefficientLCUUnitary (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient (z j) α B₀)
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U) Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSeed) := by
  calc
    _ = (shiftedPrepare (H := H) α B₀ z)ᴴ *
        (shiftedPhase α B₀ z * shiftedSelect U) * shiftedPrepare α B₀ z := by
      simp only [Matrix.mul_assoc]
    _ = (shiftedPrepare (H := H) α B₀ z)ᴴ *
        select (fun j => select (phaseAbsorbed (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient (z j) α B₀)
          (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U))) * shiftedPrepare α B₀ z := by
      rw [shiftedPhase_mul_shiftedSelect]
    _ = _ := by
      simp only [shiftedPrepare, parallel_select_adjoint, parallel_select_mul,
        coefficientLCUUnitary]

/-- G23: the actual original controlled-oracle body and its true adjoint
implement the fixed literal LCU construction with one query and three macros
in each direction. The fixed word has no unknown matrix parameter. -/
theorem raw_shifted_body_law
    (H L : Type) [Fintype H] [DecidableEq H] [Fintype L] [DecidableEq L]
    (α B₀ : ℝ) (z : L → ℂ) (U : Matrix H H ℂ) :
    relabelGate (shiftWireEquiv L H) (shiftedSelect (L := L) U) = rawShiftedQuery U ∧
    evaluate (rawShiftedQuery U) (rawShiftedWord α B₀ z) = rawShiftedBody α B₀ z U ∧
    adjointQueryCount (rawShiftedWord (H := H) α B₀ z) = 1 ∧
    adjointGateCount (rawShiftedWord (H := H) α B₀ z) = 3 ∧
    evaluate (rawShiftedQuery U) (adjointCircuit (rawShiftedWord α B₀ z)) =
      (rawShiftedBody α B₀ z U)ᴴ ∧
    adjointQueryCount (adjointCircuit (rawShiftedWord (H := H) α B₀ z)) = 1 ∧
    adjointGateCount (adjointCircuit (rawShiftedWord (H := H) α B₀ z)) = 3 := by
  have hquery := raw_shifted_query_relabel H L U
  have hfactor := congrArg (relabelGate (shiftWireEquiv L H))
    (shifted_body_factorization H L α B₀ z U)
  simp only [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul] at hfactor
  have hstar : relabelGate (shiftWireEquiv L H) (shiftedPrepare (H := H) α B₀ z)ᴴ =
      (relabelGate (shiftWireEquiv L H) (shiftedPrepare (H := H) α B₀ z))ᴴ :=
    (Matrix.conjTranspose_reindex (shiftWireEquiv L H) (shiftWireEquiv L H)
      (shiftedPrepare (H := H) α B₀ z)).symm
  rw [hstar, hquery] at hfactor
  have heval : evaluate (rawShiftedQuery U) (rawShiftedWord α B₀ z) =
      rawShiftedBody α B₀ z U := by
    simpa only [rawShiftedWord, rawShiftedPrepare, rawShiftedPhase, rawShiftedBody,
      evaluate, instructionMatrix, Matrix.mul_one, Matrix.mul_assoc] using hfactor
  have hqueries : adjointQueryCount (rawShiftedWord (H := H) α B₀ z) = 1 := rfl
  have hgates : adjointGateCount (rawShiftedWord (H := H) α B₀ z) = 3 := rfl
  refine ⟨hquery, heval, hqueries, hgates, ?_, ?_, ?_⟩
  · rw [evaluate_adjointCircuit, heval]
  · rw [adjointQueryCount_adjointCircuit, hqueries]
  · rw [adjointGateCount_adjointCircuit, hgates]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
