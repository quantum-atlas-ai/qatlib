/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversal
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion

/-!
# Data for paid adjoint compilation

This module defines circuit compilation of words containing fixed gates, forward oracle uses,
and adjoint oracle uses. `paidAdjointStepCircuit` replaces the latter two by a supplied body
circuit and its reverse, following the unitary circuit interpretation in [NielsenChuang2010].

`paidAdjointFixedGateCost` counts only compiled fixed instructions, while
`paidAdjointCompilerUses` records their allowed gate set and `paidAdjointPipeline` adds setup
and output circuits.

## Main statements

* `paidAdjointCircuit`: compilation of a complete adjoint instruction word.
* `paidAdjointPipeline`: composition with setup and output circuits.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

namespace Qatlib.Concepts.HspRecovery.SieveLaw

open Matrix

/-- The image of a matrix gate set under conjugate transpose. -/
def paidDaggerGateSet {I : Type} (G : Set (Matrix I I ℂ)) : Set (Matrix I I ℂ) :=
  (fun U : Matrix I I ℂ => Uᴴ) '' G

/-- Compilation of a fixed instruction by the gate compiler, a forward instruction by the body
circuit, and a backward instruction by its reverse. -/
noncomputable def paidAdjointStepCircuit
    {I : Type} [Fintype I] [DecidableEq I]
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I → Circuit I
  | .gate U => compiler.compile U
  | .forward => body.circuit
  | .backward => ReverseCircuit body.circuit

/-- The circuit obtained by concatenating paid instruction compilations in reversed word order. -/
noncomputable def paidAdjointCircuit
    {I : Type} [Fintype I] [DecidableEq I]
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I)) : Circuit I :=
  word.reverse.flatMap (paidAdjointStepCircuit body compiler)

/-- The sum of compiled gate counts for fixed-gate instructions in an adjoint word, excluding
forward and backward body uses. -/
def paidAdjointFixedGateCost
    {I : Type} [Fintype I] [DecidableEq I] (compiler : GateCompiler I)
    (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I)) : ℕ :=
  (word.filterMap (fun
    | .gate U => some (GateCount (compiler.compile U))
    | .forward => none
    | .backward => none)).sum

/-- The property that every fixed-gate instruction occurring in the word compiles to a circuit
over `G`. -/
def paidAdjointCompilerUses
    {I : Type} [Fintype I] [DecidableEq I] (compiler : GateCompiler I)
    (G : Set (Matrix I I ℂ)) (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I)) : Prop :=
  ∀ U, Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep.gate U ∈ word →
    Circuit.UsesGateSet G (compiler.compile U)

/-- Concatenation of setup, the paid adjoint word compilation, and output circuits. -/
noncomputable def paidAdjointPipeline
    {I : Type} [Fintype I] [DecidableEq I]
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (setup : Circuit I) (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I))
    (output : Circuit I) : Circuit I :=
  setup ++ paidAdjointCircuit body compiler word ++ output

end Qatlib.Concepts.HspRecovery.SieveLaw
