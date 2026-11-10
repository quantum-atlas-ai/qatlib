/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false


open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QspSimulation.WordModel
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Kronecker

def cppDataOracle {J H : Type} [DecidableEq J] [DecidableEq H]
    (U : Matrix H H ℂ) : Matrix (J × (Bool × H)) (J × (Bool × H)) ℂ :=
  parallelOracle (J := J) ((1 : Matrix Bool Bool ℂ) ⊗ₖ U)

def cppAdjointStep {J H : Type} [DecidableEq J] [DecidableEq H]
    (P Q : Matrix H H ℂ) : CPPStep J → AdjointStep (J × (Bool × H))
  | .forward => .forward
  | .backward => .backward
  | s => .gate (cppInstruction (1 : Matrix H H ℂ) P Q s)

def cppAdjointWord {J H : Type} [DecidableEq J] [DecidableEq H]
    (P Q : Matrix H H ℂ) (ss : List (CPPStep J)) :
    List (AdjointStep (J × (Bool × H))) := ss.map (cppAdjointStep P Q)

def sourceCppAdjointWord {H : Type} [DecidableEq H]
    (P Q : Matrix H H ℂ) (Φ : List ℝ) : List (AdjointStep (Bool × (Bool × H))) :=
  if Φ.length % 2 = 1 then cppAdjointWord P Q (cppCompile (sourceRealFamily Φ))
  else (cppAdjointWord Q P (cppCompile (sourceRealFamily Φ))).map swapQueries

end Qatlib.Concepts.QspSimulation.WordModel
