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

/-!
# Work and peak resource ledgers

This module separates the additive work fields of `Account` into `WorkLedger` and its space
peaks into `PeakLedger`. Sequential composition adds work and takes peak maxima, while parallel
composition adds both ledgers. This separation supports explicit resource accounting of the kind
used in [RoettelerEtAl2017].

`FreshLedger` and `FreshPeak` package fresh-copy work and peak counts and convert them to
general accounts. Further definitions expose the ledgers of phase-readout constructions,
live-wire and workspace trails, an LCU counting word, and the search-space cost functions.

## Main statements

* `Account.seq_work`, `Account.seq_peak`: sequential ledger composition.
* `Account.par_work`, `Account.par_peak`: parallel ledger composition.
* `FreshPeak.ofCost_seq`: peak extraction respects fresh-copy sequencing.
* `FreshLedger.account`: conversion to the general account type.
* `liveTrail`, `wsTrail`: resource trails along a dynamic word.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

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

/-- The eight additive work components of an account: queries, adjoint queries, Hamiltonian
evolutions, macro and basic gates, depth, classical bits, and Hamiltonian ticks. -/
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

/-- The live-wire and workspace peak components of an account. -/
structure PeakLedger where

  livePeak : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

/-- Extracts the eight work components of a resource account. -/
def workOf (a : Account) : WorkLedger :=
  ⟨a.queries, a.adjointQueries, a.hamiltonianCount, a.macroGates, a.basicGates,
    a.depth, a.classicalBits, a.hamiltonianTicks⟩

/-- Extracts the live-wire and workspace peaks of a resource account. -/
def peakOf (a : Account) : PeakLedger :=
  ⟨a.livePeak, a.peakWorkspace⟩

/-- Adds corresponding work-ledger components. -/
def WorkLedger.add (a b : WorkLedger) : WorkLedger :=
  ⟨a.queries + b.queries, a.adjointQueries + b.adjointQueries,
    a.hamiltonianCount + b.hamiltonianCount, a.macroGates + b.macroGates,
    a.basicGates + b.basicGates, a.depth + b.depth,
    a.classicalBits + b.classicalBits, a.hamiltonianTicks + b.hamiltonianTicks⟩

/-- Takes the componentwise maximum of two peak ledgers. -/
def PeakLedger.takeMax (a b : PeakLedger) : PeakLedger :=
  ⟨Nat.max a.livePeak b.livePeak, Nat.max a.peakWorkspace b.peakWorkspace⟩

/-- Adds corresponding live-wire and workspace peaks. -/
def PeakLedger.add (a b : PeakLedger) : PeakLedger :=
  ⟨a.livePeak + b.livePeak, a.peakWorkspace + b.peakWorkspace⟩

/-- Multiplies every work-ledger component by a natural-number factor. -/
def WorkLedger.smul (k : ℕ) (a : WorkLedger) : WorkLedger :=
  ⟨k * a.queries, k * a.adjointQueries, k * a.hamiltonianCount, k * a.macroGates,
    k * a.basicGates, k * a.depth, k * a.classicalBits, k * a.hamiltonianTicks⟩

/-- Extracting work from sequential account composition gives the sum of the extracted work
ledgers. -/
theorem Account.seq_work (a b : Account) :
    workOf (Account.seq a b) = (workOf a).add (workOf b) := by
  rfl

/-- Extracting peaks from sequential account composition gives the componentwise maximum of the
extracted peak ledgers. -/
theorem Account.seq_peak (a b : Account) :
    peakOf (Account.seq a b) = (peakOf a).takeMax (peakOf b) := by
  rfl

/-- Extracting work from parallel account composition gives the sum of the extracted work
ledgers. -/
theorem Account.par_work (a b : Account) :
    workOf (Account.par a b) = (workOf a).add (workOf b) := by
  rfl

/-- Extracting peaks from parallel account composition gives the sum of the extracted peak
ledgers. -/
theorem Account.par_peak (a b : Account) :
    peakOf (Account.par a b) = (peakOf a).add (peakOf b) := by
  rfl

/-- Peak numbers of fresh registers and clean qubits in a fresh-copy computation. -/
structure FreshPeak where

  peakFreshRegisters : ℕ

  peakCleanQubits : ℕ
  deriving DecidableEq, Repr

/-- Extracts peak fresh-register and clean-qubit counts from a fresh-copy cost. -/
def FreshPeak.ofCost (c : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) : FreshPeak :=
  ⟨c.peakFreshRegisters, c.peakCleanQubits⟩

/-- Combines fresh-copy peak ledgers by taking the maximum of each component. -/
def FreshPeak.seq (a b : FreshPeak) : FreshPeak :=
  ⟨max a.peakFreshRegisters b.peakFreshRegisters,
    max a.peakCleanQubits b.peakCleanQubits⟩

/-- Peak extraction sends sequential fresh-copy cost composition to componentwise maximum
composition. -/
theorem FreshPeak.ofCost_seq (a b : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost) :
    FreshPeak.ofCost (Qatlib.Concepts.FreshCopyExec.QpeConsumers.seqCost a b) = (FreshPeak.ofCost a).seq (FreshPeak.ofCost b) := by
  rfl

/-- Work counts for fresh copies, partial swaps, local gates, discards, and bit queries. -/
structure FreshLedger where

  copies : ℕ

  partialSwaps : ℕ

  localGates : ℕ

  discards : ℕ

  bitQueries : ℕ
  deriving DecidableEq, Repr

/-- Interprets a resource tuple as copy, partial-swap, discard, and bit-query counts, with zero
local gates. -/
def FreshLedger.copyDriven (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.1, q.2.1, 0, q.2.2.1, q.2.2.2⟩

/-- Interprets a resource tuple as local-gate, copy, discard, and bit-query counts, with zero
partial swaps. -/
def FreshLedger.local (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.2.1, 0, q.1, q.2.2.1, q.2.2.2⟩

/-- Interprets a two-species resource tuple as copy, partial-swap, discard, and bit-query
counts, with zero local gates. -/
def FreshLedger.twoSpecies (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.1, q.2.1, 0, q.2.2.1, q.2.2.2⟩

/-- Interprets a plain-composition resource tuple as copy, partial-swap, discard, and bit-query
counts, with zero local gates. -/
def FreshLedger.plainComposition (q : ℕ × ℕ × ℕ × ℕ) : FreshLedger :=
  ⟨q.1, q.2.1, 0, q.2.2.1, q.2.2.2⟩

/-- Builds a fresh-copy cost from a work ledger and supplied fixed-macro, fresh-register peak,
and clean-qubit peak counts. -/
def FreshLedger.toCost (l : FreshLedger) (fixedMacros peakFresh peakClean : ℕ) :
    Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost :=
  ⟨l.copies, l.partialSwaps, l.localGates, fixedMacros, l.discards, l.bitQueries,
    peakFresh, peakClean⟩

/-- Converts a fresh-copy work ledger with supplied macro and peak counts to a general resource
account. -/
def FreshLedger.account (l : FreshLedger) (fixedMacros peakFresh peakClean : ℕ) : Account :=
  Account.ofFreshCost (l.toCost fixedMacros peakFresh peakClean)

/-- Packages `copyQPEResources` as a fresh-copy work ledger. -/
def copyDrivenLedger (D M n : ℕ) : FreshLedger :=
  FreshLedger.copyDriven (copyQPEResources D M n)

/-- Packages `localCopyQPEResources` as a fresh-copy work ledger. -/
def localCopyLedger (n M s : ℕ) : FreshLedger :=
  FreshLedger.local (localCopyQPEResources n M s)

/-- Packages numeric-copy resources for the counted phase circuit as a fresh-copy work ledger. -/
def numericCopyLedger (n M b : ℕ) : FreshLedger :=
  FreshLedger.local (numericCopyResources n b (countedPhaseCircuit (I := Fin (2 ^ n)) M))

/-- Packages `twoSpeciesQPEResources` as a fresh-copy work ledger; the dimension parameter is
unused. -/
def twoSpeciesLedger (_D M n : ℕ) : FreshLedger :=
  FreshLedger.twoSpecies (twoSpeciesQPEResources M n)

/-- Packages the resource counts of fresh-copy composition for the supplied dimension and angle
list. -/
def plainCompositionLedger (D : ℕ) (angles : List ℝ) : FreshLedger :=
  FreshLedger.plainComposition (freshCopyResourceCounts D angles)

/-- The dynamic word consisting of `n * (8 * n + 28)` Hadamard macros followed by allocation and
uncomputation of wire zero. -/
def lcuDynamicWord (n : ℕ) : List DynStep :=
  (List.replicate (n * (8 * n + 28)) (DynStep.macro (.h 0)))
    ++ [DynStep.alloc 0, DynStep.uncompute 0]

/-- The macro-gate count formula `n * (8 * n + 28)` used in `lcuDynamicWord`. -/
def lcuDynamicWordGates (n : ℕ) : ℕ := n * (8 * n + 28)

/-- The total of forward and adjoint queries in an account. -/
def queryCountOf (a : Account) : ℕ := a.queries + a.adjointQueries

/-- The maximum entry of a natural-number list, with value zero for the empty list. -/
def maxTrail : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.max x (maxTrail xs)

/-- Records the live-wire count after each successive dynamic step, starting from the supplied
live-wire list. -/
def liveTrail (live : List ℕ) : List DynStep → List ℕ
  | [] => []
  | s :: ops => (applyLive live s).length :: liveTrail (applyLive live s) ops

/-- Records the natural-number difference between the live-wire count and `base` after each
successive dynamic step. -/
def wsTrail (base : ℕ) (live : List ℕ) : List DynStep → List ℕ
  | [] => []
  | s :: ops => ((applyLive live s).length - base) :: wsTrail base (applyLive live s) ops

/-- The real-valued singleton-search space size `2 ^ n`. -/
def searchSpace (n : ℕ) : ℝ := (2 ^ n : ℕ)

/-- The account of the singleton-search workspace Grover circuit with unit workspace. -/
def searchAccount (n : ℕ) : Account :=
  Account.ofCircuit (workspaceGroverCircuit (W := Unit) n (singletonSearchIterations n))

/-- The square root of the singleton-search space size. -/
def searchSizeCost (n : ℕ) : ℝ := Real.sqrt (searchSpace n)

end
end Qatlib.Concepts.ResourceBounds.AsymBounds
