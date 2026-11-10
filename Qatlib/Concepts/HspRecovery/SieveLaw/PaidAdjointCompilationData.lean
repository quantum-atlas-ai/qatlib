/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversal
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

namespace Qatlib.Concepts.HspRecovery.SieveLaw

open Matrix

def paidDaggerGateSet {I : Type} (G : Set (Matrix I I ℂ)) : Set (Matrix I I ℂ) :=
  (fun U : Matrix I I ℂ => Uᴴ) '' G

noncomputable def paidAdjointStepCircuit
    {I : Type} [Fintype I] [DecidableEq I]
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I → Circuit I
  | .gate U => compiler.compile U
  | .forward => body.circuit
  | .backward => ReverseCircuit body.circuit

noncomputable def paidAdjointCircuit
    {I : Type} [Fintype I] [DecidableEq I]
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I)) : Circuit I :=
  word.reverse.flatMap (paidAdjointStepCircuit body compiler)

def paidAdjointFixedGateCost
    {I : Type} [Fintype I] [DecidableEq I] (compiler : GateCompiler I)
    (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I)) : ℕ :=
  (word.filterMap (fun
    | .gate U => some (GateCount (compiler.compile U))
    | .forward => none
    | .backward => none)).sum

def paidAdjointCompilerUses
    {I : Type} [Fintype I] [DecidableEq I] (compiler : GateCompiler I)
    (G : Set (Matrix I I ℂ)) (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I)) : Prop :=
  ∀ U, Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep.gate U ∈ word →
    Circuit.UsesGateSet G (compiler.compile U)

noncomputable def paidAdjointPipeline
    {I : Type} [Fintype I] [DecidableEq I]
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (setup : Circuit I) (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep I))
    (output : Circuit I) : Circuit I :=
  setup ++ paidAdjointCircuit body compiler word ++ output

end Qatlib.Concepts.HspRecovery.SieveLaw
