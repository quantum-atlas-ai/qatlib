/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsExt
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyQPEConsumers
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.NumericalCopyQPE
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.TwoSpeciesCopyPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyComposition
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

set_option autoImplicit false

namespace Qatlib.Concepts.ResourceBounds.AsymBounds

open Qatlib
open Qatlib
noncomputable section

structure WorkLedger where

  queries : ℕ

  adjointQueries : ℕ

  hamiltonianCount : ℕ

  macroGates : ℕ

  basicGates : ℕ

  depth : ℕ

  classicalBits : ℕ

  hamiltonianTicks : ℕ
  deriving DecidableEq, Repr

structure PeakLedger where

  livePeak : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

def workOf (a : Account) : WorkLedger :=
  ⟨a.queries, a.adjointQueries, a.hamiltonianCount, a.macroGates, a.basicGates,
    a.depth, a.classicalBits, a.hamiltonianTicks⟩

def peakOf (a : Account) : PeakLedger :=
  ⟨a.livePeak, a.peakWorkspace⟩

def WorkLedger.add (a b : WorkLedger) : WorkLedger :=
  ⟨a.queries + b.queries, a.adjointQueries + b.adjointQueries,
    a.hamiltonianCount + b.hamiltonianCount, a.macroGates + b.macroGates,
    a.basicGates + b.basicGates, a.depth + b.depth,
    a.classicalBits + b.classicalBits, a.hamiltonianTicks + b.hamiltonianTicks⟩

def PeakLedger.takeMax (a b : PeakLedger) : PeakLedger :=
  ⟨Nat.max a.livePeak b.livePeak, Nat.max a.peakWorkspace b.peakWorkspace⟩

def PeakLedger.add (a b : PeakLedger) : PeakLedger :=
  ⟨a.livePeak + b.livePeak, a.peakWorkspace + b.peakWorkspace⟩

def WorkLedger.smul (k : ℕ) (a : WorkLedger) : WorkLedger :=
  ⟨k * a.queries, k * a.adjointQueries, k * a.hamiltonianCount, k * a.macroGates,
    k * a.basicGates, k * a.depth, k * a.classicalBits, k * a.hamiltonianTicks⟩

theorem Account.seq_work (a b : Account) :
    workOf (Account.seq a b) = (workOf a).add (workOf b) := by
  rfl

theorem Account.seq_peak (a b : Account) :
    peakOf (Account.seq a b) = (peakOf a).takeMax (peakOf b) := by
  rfl

theorem Account.par_work (a b : Account) :
    workOf (Account.par a b) = (workOf a).add (workOf b) := by
  rfl

theorem Account.par_peak (a b : Account) :
    peakOf (Account.par a b) = (peakOf a).add (peakOf b) := by
  rfl

structure FreshPeak where

  peakFreshRegisters : ℕ

  peakCleanQubits : ℕ
  deriving DecidableEq, Repr

def FreshPeak.ofCost (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) : FreshPeak :=
  ⟨c.peakFreshRegisters, c.peakCleanQubits⟩

def FreshPeak.seq (a b : FreshPeak) : FreshPeak :=
  ⟨max a.peakFreshRegisters b.peakFreshRegisters,
    max a.peakCleanQubits b.peakCleanQubits⟩

theorem FreshPeak.ofCost_seq (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) :
    FreshPeak.ofCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b) = (FreshPeak.ofCost a).seq (FreshPeak.ofCost b) := by
  rfl

structure FreshLedger where

  copies : ℕ

  partialSwaps : ℕ

  localGates : ℕ

  discards : ℕ

  bitQueries : ℕ
  deriving DecidableEq, Repr

def FreshLedger.copyDriven (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.1, q.2.1, 0, q.2.2.1, q.2.2.2⟩

def FreshLedger.local (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.2.1, 0, q.1, q.2.2.1, q.2.2.2⟩

def FreshLedger.twoSpecies (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.1, q.2.1, 0, q.2.2.1, q.2.2.2⟩

def FreshLedger.plainComposition (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.1, q.2.1, 0, q.2.2.1, q.2.2.2⟩

def FreshLedger.toCost (l : FreshLedger) (fixedMacros peakFresh peakClean : ℕ) :
    Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost :=
  ⟨l.copies, l.partialSwaps, l.localGates, fixedMacros, l.discards, l.bitQueries,
    peakFresh, peakClean⟩

def FreshLedger.account (l : FreshLedger) (fixedMacros peakFresh peakClean : ℕ) : Account :=
  Account.ofFreshCost (l.toCost fixedMacros peakFresh peakClean)

def copyDrivenLedger (D M n : ℕ) : FreshLedger :=
  FreshLedger.copyDriven (copyQPEResources D M n)

def localCopyLedger (n M s : ℕ) : FreshLedger :=
  FreshLedger.local (localCopyQPEResources n M s)

def numericCopyLedger (n M b : ℕ) : FreshLedger :=
  FreshLedger.local (numericCopyResources n b (countedPhaseCircuit (I := Fin (2 ^ n)) M))

def twoSpeciesLedger (_D M n : ℕ) : FreshLedger :=
  FreshLedger.twoSpecies (twoSpeciesQPEResources M n)

def plainCompositionLedger (D : ℕ) (angles : List ℝ) : FreshLedger :=
  FreshLedger.plainComposition (freshCopyResourceCounts D angles)

def lcuDynamicWord (n : ℕ) : List DynStep :=
  (List.replicate (n * (8 * n + 28)) (DynStep.macro (.h 0)))
    ++ [DynStep.alloc 0, DynStep.uncompute 0]

def lcuDynamicWordGates (n : ℕ) : ℕ := n * (8 * n + 28)

def queryCountOf (a : Account) : ℕ := a.queries + a.adjointQueries

def maxTrail : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.max x (maxTrail xs)

def liveTrail (live : List ℕ) : List DynStep → List ℕ
  | [] => []
  | s :: ops => (applyLive live s).length :: liveTrail (applyLive live s) ops

def wsTrail (base : ℕ) (live : List ℕ) : List DynStep → List ℕ
  | [] => []
  | s :: ops => ((applyLive live s).length - base) :: wsTrail base (applyLive live s) ops

def searchSpace (n : ℕ) : ℝ := (2 ^ n : ℕ)

def searchAccount (n : ℕ) : Account :=
  Account.ofCircuit (workspaceGroverCircuit (W := Unit) n (singletonSearchIterations n))

def searchSizeCost (n : ℕ) : ℝ := Real.sqrt (searchSpace n)

end
end Qatlib.Concepts.ResourceBounds.AsymBounds
