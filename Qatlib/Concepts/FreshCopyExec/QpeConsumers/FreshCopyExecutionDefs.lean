/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyQPEConsumers
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.NumericalCopyQPE
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.TwoSpeciesCopyPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyComposition
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout
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

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
set_option autoImplicit false
noncomputable section

@[ext] structure Cost where
  copies : ℕ
  partialSwaps : ℕ
  localGates : ℕ
  fixedMacros : ℕ
  discards : ℕ
  bitQueries : ℕ
  peakFreshRegisters : ℕ
  peakCleanQubits : ℕ
  deriving DecidableEq

def zeroCost : Cost := ⟨0,0,0,0,0,0,0,0⟩
def seqCost (a b : Cost) : Cost :=
  ⟨a.copies+b.copies, a.partialSwaps+b.partialSwaps,
   a.localGates+b.localGates, a.fixedMacros+b.fixedMacros,
   a.discards+b.discards, a.bitQueries+b.bitQueries,
   max a.peakFreshRegisters b.peakFreshRegisters,
   max a.peakCleanQubits b.peakCleanQubits⟩
def freshCost (g clean : ℕ) : Cost := ⟨1,1,g,0,1,0,1,clean⟩
def macroCost : Cost := ⟨0,0,0,1,0,0,0,0⟩

abbrev Register (n M : ℕ) := Fin M × (Bool × Fin (2^n))
abbrev State (n M : ℕ) := Matrix (Register n M) (Register n M) ℂ

inductive Op (n M : ℕ) where
  | gate : Matrix (Register n M) (Register n M) ℂ → Op n M
  | direct : Operator (2^n) → ℝ → Op n M
  | localStep : Operator (2^n) → ℝ → Op n M
  | numeric : Operator (2^n) → ℕ → ℕ → Op n M

def liftMap (n M : ℕ)
    (T : Operator (2*(2^n)) → Operator (2*(2^n))) (X : State n M) : State n M :=
  relabelGate (copyQPERegisterEquiv (2^n) M).symm
    (numericAmplification T M (relabelGate (copyQPERegisterEquiv (2^n) M) X))

def stepMap {n M : ℕ} : Op n M → State n M → State n M
  | .gate U, X => MatrixMap.conj U X
  | .direct ρ θ, X => liftMap n M (controlledCopyChannelMap ρ θ) X
  | .localStep ρ θ, X => liftMap n M (localControlledCopyChannelMap n ρ θ) X
  | .numeric ρ b k, X => liftMap n M (numericCopyFinStep n ρ b k) X

def stepCost {n M : ℕ} : Op n M → Cost
  | .gate _ => macroCost
  | .direct _ _ => freshCost 0 0
  | .localStep _ θ => freshCost
      (GateCount (reflectionCompile (localControlledSwapSteps n θ))) (n+1)
  | .numeric _ b k => freshCost
      (GateCount (reflectionCompile (numericControlledSwapSteps n b k))) (n+1)

def run {n M : ℕ} : List (Op n M) → State n M → State n M × Cost
  | [], X => (X, zeroCost)
  | op :: ops, X =>
      let out := run ops (stepMap op X)
      (out.1, seqCost (stepCost op) out.2)

def compileDirect (n M s : ℕ) (ρ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileDirect n M s ρ C
  | .query :: C => List.replicate s (.direct ρ (Real.pi/(s:ℝ))) ++ compileDirect n M s ρ C

def compileLocal (n M s : ℕ) (ρ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileLocal n M s ρ C
  | .query :: C => List.replicate s (.localStep ρ (Real.pi/(s:ℝ))) ++ compileLocal n M s ρ C

def compileNumeric (n M b k : ℕ) (ρ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileNumeric n M b k ρ C
  | .query :: C => List.replicate (2^b) (.numeric ρ b k) ++ compileNumeric n M b k ρ C

def compileTwo (n M s : ℕ) (ρ σ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileTwo n M s ρ σ C
  | .query :: C =>
      (List.replicate s [.direct σ (-(Real.pi/(s:ℝ))), .direct ρ (Real.pi/(s:ℝ))]).flatten ++
        compileTwo n M s ρ σ C

def runPlain {D : ℕ} : List (Operator D × ℝ) → Operator D → Operator D × Cost
  | [], X => (X, zeroCost)
  | (ρ,θ) :: ops, X =>
      let out := runPlain ops (partialSwapOutput ρ θ X)
      (out.1, seqCost (freshCost 0 0) out.2)

end
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
