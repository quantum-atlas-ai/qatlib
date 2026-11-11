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

/-!
# Fresh-Copy Execution Language

This module defines an operation language and interpreter for direct, local, and numerical fresh
copy QPE implementations, in the density matrix evolution setting of
[LloydMohseniRebentrost2014]. The types `Op`, `Register`, and `State` describe executable
operations and their matrix states; `Cost` records both accumulated resources and peak
workspace.

The interpreter `run` combines `stepMap` with `stepCost`. The compilers `compileDirect`,
`compileLocal`, `compileNumeric`, and `compileTwo` replace circuit queries with the
corresponding fresh copy blocks, while `runPlain` interprets schedules without a QPE register.

## References

- [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

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

/-- The resource record for fresh copy execution, containing copy, partial swap, local-gate,
fixed macro, discard, and bit-query counts. It also records the peak number of fresh
registers and clean qubits. -/
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

/-- The cost record with all accumulated counts and peak workspace equal to zero. -/
def zeroCost : Cost := ⟨0,0,0,0,0,0,0,0⟩
/-- Sequential cost composition, adding accumulated resource counts and taking the maximum of
each peak-workspace count. -/
def seqCost (a b : Cost) : Cost :=
  ⟨a.copies+b.copies, a.partialSwaps+b.partialSwaps,
   a.localGates+b.localGates, a.fixedMacros+b.fixedMacros,
   a.discards+b.discards, a.bitQueries+b.bitQueries,
   max a.peakFreshRegisters b.peakFreshRegisters,
   max a.peakCleanQubits b.peakCleanQubits⟩
/-- The cost of one fresh copy partial swap and discard, with `g` local gates, one peak fresh
register, and `clean` peak clean qubits. -/
def freshCost (g clean : ℕ) : Cost := ⟨1,1,g,0,1,0,1,clean⟩
/-- The cost of one fixed matrix-gate macro, with all other resource counts equal to zero. -/
def macroCost : Cost := ⟨0,0,0,1,0,0,0,0⟩

/-- The product register consisting of a QPE label in `Fin M`, a Boolean control, and an
`n`-qubit data register. -/
abbrev Register (n M : ℕ) := Fin M × (Bool × Fin (2^n))
/-- The complex square-matrix state space on `Register n M`, with no positivity or normalization
requirement built into the type. -/
abbrev State (n M : ℕ) := Matrix (Register n M) (Register n M) ℂ

/-- The executable operations: a fixed matrix gate, a direct fresh copy step, a local fresh copy
step, or a numerical fresh copy step. -/
inductive Op (n M : ℕ) where
  | gate : Matrix (Register n M) (Register n M) ℂ → Op n M
  | direct : Operator (2^n) → ℝ → Op n M
  | localStep : Operator (2^n) → ℝ → Op n M
  | numeric : Operator (2^n) → ℕ → ℕ → Op n M

/-- The blockwise extension of a control and data operator transformation across the QPE label
register, using the register relabeling. -/
def liftMap (n M : ℕ)
    (T : Operator (2*(2^n)) → Operator (2*(2^n))) (X : State n M) : State n M :=
  relabelGate (copyQPERegisterEquiv (2^n) M).symm
    (numericAmplification T M (relabelGate (copyQPERegisterEquiv (2^n) M) X))

/-- The state transformation denoted by one operation, using matrix conjugation for fixed gates
and lifted fresh copy maps for the other constructors. -/
def stepMap {n M : ℕ} : Op n M → State n M → State n M
  | .gate U, X => MatrixMap.conj U X
  | .direct ρ θ, X => liftMap n M (controlledCopyChannelMap ρ θ) X
  | .localStep ρ θ, X => liftMap n M (localControlledCopyChannelMap n ρ θ) X
  | .numeric ρ b k, X => liftMap n M (numericCopyFinStep n ρ b k) X

/-- The cost assigned to one operation, recording fixed macros or fresh copy use and the actual
compiled local-word gate count and clean workspace. -/
def stepCost {n M : ℕ} : Op n M → Cost
  | .gate _ => macroCost
  | .direct _ _ => freshCost 0 0
  | .localStep _ θ => freshCost
      (GateCount (reflectionCompile (localControlledSwapSteps n θ))) (n+1)
  | .numeric _ b k => freshCost
      (GateCount (reflectionCompile (numericControlledSwapSteps n b k))) (n+1)

/-- The interpreter executing an operation list in order and returning its final matrix state
together with the sequentially combined resource cost. -/
def run {n M : ℕ} : List (Op n M) → State n M → State n M × Cost
  | [], X => (X, zeroCost)
  | op :: ops, X =>
      let out := run ops (stepMap op X)
      (out.1, seqCost (stepCost op) out.2)

/-- The compiler retaining known circuit gates and replacing each query with `s` direct fresh
copy steps at angle `Real.pi / s`. -/
def compileDirect (n M s : ℕ) (ρ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileDirect n M s ρ C
  | .query :: C => List.replicate s (.direct ρ (Real.pi/(s:ℝ))) ++ compileDirect n M s ρ C

/-- The compiler retaining known circuit gates and replacing each query with `s` locally
implemented fresh copy steps at angle `Real.pi / s`. -/
def compileLocal (n M s : ℕ) (ρ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileLocal n M s ρ C
  | .query :: C => List.replicate s (.localStep ρ (Real.pi/(s:ℝ))) ++ compileLocal n M s ρ C

/-- The compiler retaining known circuit gates and replacing each query with `2^b` numerical
fresh copy steps at precision parameters `b` and `k`. -/
def compileNumeric (n M b k : ℕ) (ρ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileNumeric n M b k ρ C
  | .query :: C => List.replicate (2^b) (.numeric ρ b k) ++ compileNumeric n M b k ρ C

/-- The compiler replacing each query with `s` pairs of negative angle `σ` steps followed by
positive-angle `ρ` steps, while retaining known gates. -/
def compileTwo (n M s : ℕ) (ρ σ : Operator (2^n)) :
    Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileTwo n M s ρ σ C
  | .query :: C =>
      (List.replicate s [.direct σ (-(Real.pi/(s:ℝ))), .direct ρ (Real.pi/(s:ℝ))]).flatten ++
        compileTwo n M s ρ σ C

/-- The interpreter for lists of copy operators and interaction angles, applying partial swap
outputs sequentially and charging one direct fresh copy cost per entry. -/
def runPlain {D : ℕ} : List (Operator D × ℝ) → Operator D → Operator D × Cost
  | [], X => (X, zeroCost)
  | (ρ,θ) :: ops, X =>
      let out := runPlain ops (partialSwapOutput ρ θ X)
      (out.1, seqCost (freshCost 0 0) out.2)

end
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
