/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.ShiftCoefficients
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Literal padded coefficients and the original controlled-oracle program.
The fixed word's parameters exclude the unknown matrix. Its sole query is a
spectator lift of the explicitly supplied controlled oracle. Known preparation
and phase matrices are ideal real-data macros; native synthesis costs remain
separate. The common frame is retained rather than assumed cheaply aligned. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix
/-- Abbreviation for Shifted Logical Space in the shifted encoding model model. -/
abbrev ShiftedLogicalSpace (L H : Type) := L × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot × H)
/-- Abbreviation for Shifted Raw Space in the shifted encoding model model. -/
abbrev ShiftedRawSpace (L H : Type) := (L × Fin 4) × (Bool × H)

/-- Construction for shift Wire Equiv in the shifted encoding model model. -/
def shiftWireEquiv (L H : Type) : ShiftedLogicalSpace L H ≃ ShiftedRawSpace L H where
  toFun p := ((p.1, p.2.1.2), (p.2.1.1, p.2.2))
  invFun p := (p.1.1, ((p.2.1, p.1.2), p.2.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Construction for shifted Prepare in the shifted encoding model model. -/
def shiftedPrepare {H L : Type} [Fintype H] [DecidableEq H]
    [Fintype L] [DecidableEq L] (α B₀ : ℝ) (z : L → ℂ) :
    Matrix (ShiftedLogicalSpace L H) (ShiftedLogicalSpace L H) ℂ :=
  select (fun j => prepareRegister (I := H) (coefficientPrepare (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient (z j) α B₀) Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSeed))

/-- Construction for shifted Phase in the shifted encoding model model. -/
def shiftedPhase {H L : Type} [DecidableEq H] [DecidableEq L]
    (α B₀ : ℝ) (z : L → ℂ) :
    Matrix (ShiftedLogicalSpace L H) (ShiftedLogicalSpace L H) ℂ :=
  select (fun j => select (fun s : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.ShiftSlot =>
    coefficientPhase (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient (z j) α B₀ s) • (1 : Matrix H H ℂ)))

/-- Construction for shifted Select in the shifted encoding model model. -/
def shiftedSelect {H L : Type} [DecidableEq H] [DecidableEq L]
    (U : Matrix H H ℂ) :
    Matrix (ShiftedLogicalSpace L H) (ShiftedLogicalSpace L H) ℂ :=
  select (fun _ : L => select (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U))

/-- Construction for raw Shifted Prepare in the shifted encoding model model. -/
def rawShiftedPrepare {H L : Type} [Fintype H] [DecidableEq H]
    [Fintype L] [DecidableEq L] (α B₀ : ℝ) (z : L → ℂ) :
    Matrix (ShiftedRawSpace L H) (ShiftedRawSpace L H) ℂ :=
  relabelGate (shiftWireEquiv L H) (shiftedPrepare α B₀ z)

/-- Construction for raw Shifted Phase in the shifted encoding model model. -/
def rawShiftedPhase {H L : Type} [DecidableEq H] [DecidableEq L]
    (α B₀ : ℝ) (z : L → ℂ) :
    Matrix (ShiftedRawSpace L H) (ShiftedRawSpace L H) ℂ :=
  relabelGate (shiftWireEquiv L H) (shiftedPhase α B₀ z)

/-- Construction for raw Shifted Query in the shifted encoding model model. -/
def rawShiftedQuery {H L : Type} [DecidableEq H] [DecidableEq L]
    (U : Matrix H H ℂ) :
    Matrix (ShiftedRawSpace L H) (ShiftedRawSpace L H) ℂ :=
  parallelOracle (J := L × Fin 4) (controlOracle U)

/-- Construction for raw Shifted Body in the shifted encoding model model. -/
def rawShiftedBody {H L : Type} [Fintype H] [DecidableEq H]
    [Fintype L] [DecidableEq L] (α B₀ : ℝ) (z : L → ℂ) (U : Matrix H H ℂ) :
    Matrix (ShiftedRawSpace L H) (ShiftedRawSpace L H) ℂ :=
  relabelGate (shiftWireEquiv L H) (select (fun j =>
    coefficientLCUUnitary (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftCoefficient (z j) α B₀) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U) Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSeed))

/-- Product-order instructions. The unknown U is absent from every fixed gate. -/
def rawShiftedWord {H L : Type} [Fintype H] [DecidableEq H]
    [Fintype L] [DecidableEq L] (α B₀ : ℝ) (z : L → ℂ) :
    List (AdjointStep (ShiftedRawSpace L H)) :=
  [.gate (rawShiftedPrepare α B₀ z)ᴴ, .gate (rawShiftedPhase α B₀ z),
    .forward, .gate (rawShiftedPrepare α B₀ z)]

/-- Construction for shifted Logical Frame in the shifted encoding model model. -/
def shiftedLogicalFrame {H I L : Type} [DecidableEq L]
    (F : Matrix H I ℂ) : Matrix (ShiftedLogicalSpace L H) (L × I) ℂ :=
  Matrix.of (fun p q => if p.1 = q.1 ∧ p.2.1 = Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSeed then F p.2.2 q.2 else 0)

/-- Construction for raw Shifted Frame in the shifted encoding model model. -/
def rawShiftedFrame {H I L : Type} [DecidableEq L]
    (F : Matrix H I ℂ) : Matrix (ShiftedRawSpace L H) (L × I) ℂ :=
  (shiftedLogicalFrame F).submatrix (shiftWireEquiv L H).symm id

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
