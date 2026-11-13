/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.QueryWordCore.AdjointCircuits

/-!
# Adjoint-query words for controlled projector phases

This module translates `CPPStep` instructions into `AdjointStep` words with a parallel data
oracle. `sourceCppAdjointWord` chooses the projector order and query orientation according to
the parity of the source phase-list length. Background and related constructions are discussed
in [GilyenSuLowWiebe2019].

## Main statements

* `cppDataOracle`: lifts the data oracle to the control registers.
* `cppAdjointWord`: translates a list of controlled projector-phase instructions.
* `sourceCppAdjointWord`: compiles the source real family with its parity convention.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase

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

/-- Lifts `U` to a parallel oracle acting on the data register and trivially on the Boolean
control register. -/
def cppDataOracle {J H : Type} [DecidableEq J] [DecidableEq H]
    (U : Matrix H H ℂ) : Matrix (J × (Bool × H)) (J × (Bool × H)) ℂ :=
  parallelOracle (J := J) ((1 : Matrix Bool Bool ℂ) ⊗ₖ U)

/-- Translates a controlled projector-phase instruction into an adjoint-query step, preserving
forward and backward queries and interpreting other instructions as fixed gates. -/
def cppAdjointStep {J H : Type} [DecidableEq J] [DecidableEq H]
    (P Q : Matrix H H ℂ) : CPPStep J → AdjointStep (J × (Bool × H))
  | .forward => .forward
  | .backward => .backward
  | s => .gate (cppInstruction (1 : Matrix H H ℂ) P Q s)

/-- Translates a list of controlled projector-phase instructions by mapping `cppAdjointStep`
over the list. -/
def cppAdjointWord {J H : Type} [DecidableEq J] [DecidableEq H]
    (P Q : Matrix H H ℂ) (ss : List (CPPStep J)) :
    List (AdjointStep (J × (Bool × H))) := ss.map (cppAdjointStep P Q)

/-- Compiles `sourceRealFamily Φ` into an adjoint-query word, swapping the projectors and query
directions when the phase-list length is even. -/
def sourceCppAdjointWord {H : Type} [DecidableEq H]
    (P Q : Matrix H H ℂ) (Φ : List ℝ) : List (AdjointStep (Bool × (Bool × H))) :=
  if Φ.length % 2 = 1 then cppAdjointWord P Q (cppCompile (sourceRealFamily Φ))
  else (cppAdjointWord Q P (cppCompile (sourceRealFamily Φ))).map swapQueries

end Qatlib.Concepts.QspSimulation.WordModel
