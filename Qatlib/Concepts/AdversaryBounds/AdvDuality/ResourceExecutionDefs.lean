/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransport
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyExecution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ENNReal

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

structure UnifiedCounts where

  queryCount : ℕ

  adjointQueryCount : ℕ

  hamiltonianCount : ℕ
  deriving DecidableEq, Repr

def UnifiedCounts.ofAccount (a : Account) : UnifiedCounts :=
  ⟨a.queries, a.adjointQueries, a.hamiltonianCount⟩

def UnifiedCounts.total (c : UnifiedCounts) : ℕ := c.queryCount + c.adjointQueryCount

def forwardOracleStep : DynStep → ℕ
  | .oracle false _ => 1
  | .oracle true _ => 0
  | .macro _ => 0
  | .evolve _ => 0
  | .classical _ => 0
  | .alloc _ => 0
  | .releaseClean _ => 0
  | .releaseDirty _ => 0
  | .reset _ => 0
  | .uncompute _ => 0

def adjointOracleStep : DynStep → ℕ
  | .oracle false _ => 0
  | .oracle true _ => 1
  | .macro _ => 0
  | .evolve _ => 0
  | .classical _ => 0
  | .alloc _ => 0
  | .releaseClean _ => 0
  | .releaseDirty _ => 0
  | .reset _ => 0
  | .uncompute _ => 0

def evolveStep : DynStep → ℕ
  | .oracle false _ => 0
  | .oracle true _ => 0
  | .macro _ => 0
  | .evolve _ => 1
  | .classical _ => 0
  | .alloc _ => 0
  | .releaseClean _ => 0
  | .releaseDirty _ => 0
  | .reset _ => 0
  | .uncompute _ => 0

def forwardOracleCount : List DynStep → ℕ
  | [] => 0
  | s :: rest => forwardOracleStep s + forwardOracleCount rest

def adjointOracleCount : List DynStep → ℕ
  | [] => 0
  | s :: rest => adjointOracleStep s + adjointOracleCount rest

def evolveCount : List DynStep → ℕ
  | [] => 0
  | s :: rest => evolveStep s + evolveCount rest

noncomputable def freshRunAccount {n M : ℕ} (ops : List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M))
    (X : Qatlib.Concepts.FreshCopyExec.QpeConsumers.State n M) : Account :=
  Account.ofFreshCost ((Qatlib.Concepts.FreshCopyExec.QpeConsumers.run ops X).2)

noncomputable def freshRunCost {n M : ℕ} (ops : List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M))
    (X : Qatlib.Concepts.FreshCopyExec.QpeConsumers.State n M) : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost :=
  (Qatlib.Concepts.FreshCopyExec.QpeConsumers.run ops X).2

def shiftStepWires (k : ℕ) : DynStep → DynStep
  | .alloc w => .alloc (w + k)
  | .releaseClean w => .releaseClean (w + k)
  | .releaseDirty w => .releaseDirty (w + k)
  | .reset w => .reset (w + k)
  | .uncompute w => .uncompute (w + k)
  | s => s

def shiftWord (k : ℕ) : List DynStep → List DynStep := List.map (shiftStepWires k)

def stepTouchedWire : DynStep → ℕ
  | .alloc w | .releaseClean w | .releaseDirty w | .reset w | .uncompute w => w + 1
  | _ => 0

def wordWireBound : List DynStep → ℕ :=
  List.foldl (fun acc s => max acc (stepTouchedWire s)) 0

def mergeWords (a b : List DynStep) : List DynStep :=
  a ++ shiftWord (wordWireBound a) b

structure Program (Out : Type*) where

  word : List DynStep

  base : ℕ

  readout : List ℕ → Out

def Program.account {Out : Type*} (P : Program Out) : Account :=
  Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.account P.base P.word

def Program.outcome {Out : Type*} (P : Program Out) : Outcome (Out × Account) :=
  .done (P.readout (finalLive P.base P.word), P.account)

def Program.gen {Out : Type*} {Inst : Type*} (P : Program Out) : Gen Inst Out :=
  fun _ => P.outcome

def jointFilter : Filter (ℕ × ℝ) := sizeFilter ×ˢ precFilter

def certifiedGateBudget (n : ℕ) (cert : ℝ → SynthCertificate n) : GateBudget :=
  fun _ E => (cert E).word.length

def machineWord (bits : ℕ) (word : List FiniteGateCode) : List DynStep :=
  word.flatMap (fun g => [DynStep.classical bits, DynStep.macro g])

def emissionTime (bits : ℕ) (word : List FiniteGateCode) : ℕ :=
  (account 0 (machineWord bits word)).classicalBits

def lcuTermProgram (terms : List FiniteGateCode) : List DynStep :=
  terms.flatMap (fun g => [DynStep.alloc 0, DynStep.macro g, DynStep.releaseClean 0])

def lcuTermCount (terms : List FiniteGateCode) : ℕ := terms.length

def lcuTermBlock (g : FiniteGateCode) : List DynStep :=
  [DynStep.alloc 0, DynStep.macro g, DynStep.releaseClean 0]

def stoppingWord (prep trial : ℕ) : List DynStep :=
  [DynStep.classical prep, DynStep.classical trial]

def circuitResourceStep {I : Type} (s : Step I) : DynStep :=
  match s with
  | .query => DynStep.oracle false []
  | .gate _ => DynStep.macro (.h 0)

def circuitResourceWord {I : Type} (C : Circuit I) (work : ℕ) : List DynStep :=
  DynStep.alloc work :: (C.map circuitResourceStep ++ [DynStep.releaseClean work])

structure CertifiedSynthesis (n d : ℕ) where

  cert : SynthCertificate n

  ideal : Matrix (Fin d) (Fin d) ℂ

  actual : Matrix (Fin d) (Fin d) ℂ

  error : ℝ

  error_nonneg : 0 ≤ error

  ref_bounded : RefBounded actual ideal error

noncomputable def compileErrorBudget (E : ℝ) : ℝ := 1 / E

end Qatlib.Concepts.AdversaryBounds.AdvDuality
