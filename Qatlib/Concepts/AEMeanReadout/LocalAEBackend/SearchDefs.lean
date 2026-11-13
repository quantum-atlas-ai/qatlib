/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalAmplitudeEstimation
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.WalkSearchDefs
import Qatlib.Concepts.MonteCarloMean.LayeredMean.NativeComposedMean
import Qatlib.Concepts.AmplitudeSearch.NativeMean
import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeSignedMeanConsumers
import Qatlib.Concepts.MonteCarloMean.LayeredMean.LayeredQuantumMean
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
import Qatlib.Concepts.LocalMachine.LocalTransport.MatrixRepresentationBridgesDefs

/-!
# Staged readout and finite implementation specifications

This module defines rational median stages, their resource ledgers, and a history-based stopping
procedure for amplitude-estimation readout. `StageParams`, `StageLedger`, and `runStages`
organize repeated estimates and their classical postprocessing in the framework of
[BrassardEtAl2002].

`InputTable` and the data-access predicates specify finite table loading, comparison, selection,
and sorting requirements. `AEEncoding` lays out data, phase, and flag registers, while
`HasAEFiniteImplementation` specifies legal gate words, operator error bounds, and resource
accounting for the local amplitude-estimation components.

## Main definitions

* `stageMedianCounted` and `stageLedger`: rational median evaluation and its costs.
* `windowChooser` and `runStages`: finite execution with a window criterion and a stage budget.
* `HasDataAccessTranslation`: resource inequalities connecting abstract queries and table
  operations.
* `RealizesOperatorWithin` and `HasAEFiniteImplementation`: finite circuit approximation
  specifications.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open scoped BigOperators Classical
open Qatlib
open Qatlib

/-- Parameters for a rational readout stage: phase grid size, decoding precision, median index,
and rational window size. -/
structure StageParams where
  grid : ℕ
  prec : ℕ
  mid : ℕ
  win : ℚ

/-- The rational labels of a stage, indexed by its odd number 2m + 1 of repetitions. -/
abbrev StageLabels (p : StageParams) : Type := Fin (2 * p.mid + 1) → ℚ

/-- Inserts a rational value into a list using the nondecreasing comparison and returns both the
resulting list and the number of comparisons performed. -/
def insertSortedRat (x : ℚ) : List ℚ → List ℚ × ℕ
  | [] => ([x], 0)
  | y :: ys =>
    if x ≤ y then (x :: y :: ys, 1)
    else
      let s := insertSortedRat x ys
      (y :: s.1, s.2 + 1)

/-- Insertion sorting of a rational list together with its accumulated comparison count. -/
def sortCountedRat : List ℚ → List ℚ × ℕ
  | [] => ([], 0)
  | x :: xs =>
    let s := sortCountedRat xs
    let t := insertSortedRat x s.1
    (t.1, s.2 + t.2)

/-- Sorts the stage labels and returns the entry at the median index together with the sorting
comparison count. -/
def stageMedianCounted (p : StageParams) (ys : StageLabels p) : ℚ × ℕ :=
  let s := sortCountedRat (List.ofFn ys)
  (s.1.getD p.mid 0, s.2)

/-- The rational median value returned by `stageMedianCounted`. -/
def stageOutput (p : StageParams) (ys : StageLabels p) : ℚ :=
  (stageMedianCounted p ys).1

/-- The comparison count returned by the stage's counted median computation. -/
def stageComparisons (p : StageParams) (ys : StageLabels p) : ℕ :=
  (stageMedianCounted p ys).2

/-- The rational weighted sum of the outputs of a finite family of readout stages. -/
def composedOutput {n : ℕ} (ws : Fin n → ℚ) (ps : Fin n → StageParams)
    (ys : ∀ i : Fin n, StageLabels (ps i)) : ℚ :=
  ∑ i : Fin n, ws i * stageOutput (ps i) (ys i)

/-- The sum of the comparison counts across a finite family of readout stages. -/
def composedComparisons {n : ℕ} (ps : Fin n → StageParams)
    (ys : ∀ i : Fin n, StageLabels (ps i)) : ℕ :=
  ∑ i : Fin n, stageComparisons (ps i) (ys i)

/-- The stage marking-query budget (2m + 1)(grid − 1), with subtraction in the natural numbers. -/
def stageMarkQueries (p : StageParams) : ℕ := (2 * p.mid + 1) * (p.grid - 1)

/-- The stage preparation-call budget (2m + 1)(2 grid − 1), with subtraction in the natural
numbers. -/
def stagePreparationCalls (p : StageParams) : ℕ := (2 * p.mid + 1) * (2 * p.grid - 1)

/-- The stage decoding-term count (2m + 1) · 8(prec + 8). -/
def stageDecodeTerms (p : StageParams) : ℕ := (2 * p.mid + 1) * (8 * (p.prec + 8))

/-- The list of 2m + 1 identical counted amplitude-estimation circuits launched by a readout
stage. -/
noncomputable def stageLaunches {I : Type} [Fintype I] [DecidableEq I] (p : StageParams)
    (A : Matrix I I ℂ) (j : I) : List (Circuit (Fin p.grid × (Bool × I))) :=
  List.replicate (2 * p.mid + 1) (countedAECircuit p.grid A j)

/-- Resource counts for a readout stage: marking queries, preparation calls, rational
comparisons, and decoding terms. -/
structure StageLedger where
  markQueries : ℕ
  prepCalls : ℕ
  comparisons : ℕ
  decodeTerms : ℕ

/-- The stage ledger with every resource count equal to zero. -/
def StageLedger.zero : StageLedger := ⟨0, 0, 0, 0⟩

/-- Adds two stage ledgers componentwise. -/
def StageLedger.add (a b : StageLedger) : StageLedger :=
  { markQueries := a.markQueries + b.markQueries
    prepCalls := a.prepCalls + b.prepCalls
    comparisons := a.comparisons + b.comparisons
    decodeTerms := a.decodeTerms + b.decodeTerms }

/-- Collects a stage's marking-query, preparation-call, comparison, and decoding-term counts for
the supplied labels. -/
def stageLedger (p : StageParams) (ys : StageLabels p) : StageLedger :=
  { markQueries := stageMarkQueries p
    prepCalls := stagePreparationCalls p
    comparisons := stageComparisons p ys
    decodeTerms := stageDecodeTerms p }

/-- A history-dependent rule that selects the next stage parameters or returns `none` to stop. -/
abbrev StageChooser := List (StageParams × ℚ) → Option StageParams

/-- Tests whether any stage in the history has window size at most the target, independently of
its recorded output value. -/
def windowStops (target : ℚ) : List (StageParams × ℚ) → Bool
  | [] => false
  | (p, _) :: rest => decide (p.win ≤ target) || windowStops target rest

/-- Stops when a recorded stage meets the window target or the history reaches the stage budget;
otherwise selects the parameters indexed by the history length. -/
def windowChooser (target : ℚ) (budget : ℕ) (next : ℕ → StageParams) : StageChooser :=
  fun hist =>
    if windowStops target hist = true ∨ budget ≤ hist.length then none
    else some (next hist.length)

/-- Runs stages with bounded fuel, appending each chosen stage and its computed output to the
history until the chooser stops or fuel is exhausted. -/
def runStages (chooser : StageChooser) (source : (p : StageParams) → StageLabels p) :
    ℕ → List (StageParams × ℚ) → List (StageParams × ℚ)
  | 0, hist => hist
  | fuel + 1, hist =>
    match chooser hist with
    | none => hist
    | some p => runStages chooser source fuel (hist ++ [(p, stageOutput p (source p))])

/-- Returns the output of the last recorded stage, or zero for an empty history. -/
def runOutput (hist : List (StageParams × ℚ)) : ℚ :=
  hist.foldl (fun _ s => s.2) 0

/-- Sums the stage ledgers over a history, recomputing the labels from the supplied source for
each stage's parameters. -/
def runLedger (source : (p : StageParams) → StageLabels p)
    (hist : List (StageParams × ℚ)) : StageLedger :=
  hist.foldl (fun d s => d.add (stageLedger s.1 (source s.1))) StageLedger.zero

/-- The native stage parameters at level k, using `layerGrid`, precision 2k + 8,
`layerRepetitions`, and window 2^(−k). -/
def nativeStageParams (k : ℕ) : StageParams :=
  { grid := layerGrid k
    prec := 2 * k + 8
    mid := layerRepetitions k
    win := ((2 : ℚ)⁻¹) ^ k }

/-- The dyadic weights 2^l for the k + 2 native layers. -/
def nativeStageWeights (k : ℕ) : Fin (k + 2) → ℚ := fun l => (2 : ℚ) ^ l.val

/-- Decodes a layer's phase labels with `nativeAEDecode` at the native grid and precision 2k +
8. -/
def nativeStageLabels (k : ℕ) (ω : LayerRecord k) (l : Fin (k + 2)) :
    StageLabels (nativeStageParams k) :=
  fun z => nativeAEDecode (layerGrid k) (2 * k + 8) (ω l z)

/-- A finite Boolean table with a specified number of rows and bits per row. -/
structure InputTable where
  n : ℕ
  w : ℕ
  cell : Fin n → Fin w → Bool

/-- Views a selected table row as a Boolean register. -/
def InputTable.rowReg (t : InputTable) (i : Fin t.n) : Reg t.w := fun b => t.cell i b

/-- The natural value of a Boolean register with bit b weighted by 2^b. -/
def regValue {w : ℕ} (r : Reg w) : ℕ :=
  ∑ b : Fin w, if r b = true then 2 ^ (b.val) else 0

/-- The Boolean test for strict comparison of the natural values encoded by two registers. -/
def rowLess {w : ℕ} (x y : Reg w) : Bool := decide (regValue x < regValue y)

/-- Scans a nonempty table for a row of minimum encoded value, replacing the current choice only
on strict improvement. -/
def InputTable.argmin (t : InputTable) (hn : 0 < t.n) : Fin t.n :=
  (List.finRange t.n).foldl
    (fun best i => if regValue (t.rowReg i) < regValue (t.rowReg best) then i else best)
    ⟨0, hn⟩

/-- The table's row indices sorted by encoded value, breaking equal-value ties by increasing row
index. -/
def InputTable.sortOrder (t : InputTable) : List (Fin t.n) :=
  (List.finRange t.n).mergeSort fun a b =>
    if regValue (t.rowReg a) = regValue (t.rowReg b) then decide (a.val ≤ b.val)
    else decide (regValue (t.rowReg a) ≤ regValue (t.rowReg b))

/-- The finite word of X gates at the true bit positions of a selected table row. -/
def InputTable.loadWord (t : InputTable) (i : Fin t.n) : List FiniteGateCode :=
  (List.finRange t.w).filterMap fun b =>
    if t.cell i b = true then some (FiniteGateCode.x b.val) else none

/-- Extracts the first w bits of a comparison register as its left operand. -/
def compareRowL {w : ℕ} (r : Reg (w + (w + 1))) : Reg w :=
  fun i => r ⟨i.val, by omega⟩

/-- Extracts the next w bits of a comparison register as its right operand. -/
def compareRowR {w : ℕ} (r : Reg (w + (w + 1))) : Reg w :=
  fun i => r ⟨w + i.val, by omega⟩

/-- The final flag bit of a register containing two w-bit comparison operands. -/
def compareFlag {w : ℕ} (r : Reg (w + (w + 1))) : Bool :=
  r ⟨w + w, by omega⟩

/-- XORs the comparison flag with the strict less-than test of the two encoded operands,
preserving every other bit. -/
def compareUpdate {w : ℕ} (r : Reg (w + (w + 1))) : Reg (w + (w + 1)) :=
  fun i =>
    if i.val = w + w then
      Bool.xor (r i) (rowLess (compareRowL r) (compareRowR r))
    else r i

/-- A backend resource ledger together with a table-read count. -/
structure DataAccessLedger where
  backend : BackendLedger
  tableReads : ℕ

/-- The sum of the backend ledger's forward, backward, and controlled call counts. -/
def DataAccessLedger.abstractQueries (d : DataAccessLedger) : ℕ :=
  d.backend.forwardCalls + d.backend.backwardCalls + d.backend.controlledCalls

/-- Specifies legal loading words that prepare every row from zero within the row-width gate
bound, with table-read and total gate accounting in the supplied ledger. -/
def HasTableLoad (t : InputTable) (d : DataAccessLedger) : Prop :=
  (∀ i : Fin t.n,
    finiteWordLegal t.w (t.loadWord i) = true ∧
      finiteWordRun t.w (t.loadWord i) (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin t.w => false)) =
        some (Qatlib.Foundations.PureStateMath.Ket (t.rowReg i)) ∧
      (t.loadWord i).length ≤ t.w) ∧
    d.tableReads = t.n * t.w ∧
    (∑ i : Fin t.n, (t.loadWord i).length) ≤ d.backend.elementaryGates

/-- Specifies a finite word computing the two-register comparison update, bounded by 32(w + 1)²
gates and by the ledger, with enough live qubits for both operands and the flag. -/
def HasCompareSynthesis (w : ℕ) (d : DataAccessLedger) : Prop :=
  ∃ cmpWord : List FiniteGateCode,
    FiniteWordComputes (w + (w + 1)) (w + (w + 1)) cmpWord (compareUpdate (w := w)) ∧
      cmpWord.length ≤ 32 * (w + 1) * (w + 1) ∧
      cmpWord.length ≤ d.backend.elementaryGates ∧
      2 * w + 1 ≤ d.backend.peakLiveQubits

/-- The flattened wire index i · w + b of bit b in row i of an n-row table. -/
def tableWire (n w : ℕ) (i : Fin n) (b : Fin w) : Fin (n * w) :=
  ⟨i.val * w + b.val, by
    have h1 : i.val * w + b.val < i.val * w + w := Nat.add_lt_add_left b.isLt _
    have h2 : i.val * w + w = (i.val + 1) * w := (Nat.succ_mul i.val w).symm
    have h3 : (i.val + 1) * w ≤ n * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    exact Nat.lt_of_lt_of_le h1 (h2.le.trans h3)⟩

/-- Packs all table rows consecutively into a single Boolean register. -/
def InputTable.packed (t : InputTable) : Reg (t.n * t.w) :=
  fun k =>
    if hw : 0 < t.w then
      t.cell ⟨k.val / t.w, Nat.div_lt_of_lt_mul (k.isLt.trans_le (Nat.mul_comm t.n t.w).le)⟩
        ⟨k.val % t.w, Nat.mod_lt _ hw⟩
    else false

/-- Reorders the row blocks of a supplied register according to the table's precomputed row sort
order. -/
def InputTable.sortBlocks (t : InputTable) (r : Reg (t.n * t.w)) : Reg (t.n * t.w) :=
  fun k =>
    if hw : 0 < t.w then
      match t.sortOrder[k.val / t.w]? with
      | some i => r (tableWire t.n t.w i ⟨k.val % t.w, Nat.mod_lt _ hw⟩)
      | none => r k
    else false

/-- Specifies legal checking and extraction words, with the checking word setting an initially
false flag to the predicate value on each table row. It also imposes the stated table-read,
gate, and workspace ledger bounds. -/
def HasSearchAccess (t : InputTable) (M : Reg t.w → Bool) (d : DataAccessLedger) : Prop :=
  ∃ (ws : ℕ) (checkWord extWord : List FiniteGateCode),
    finiteWordLegal ws checkWord = true ∧
      finiteWordLegal ws extWord = true ∧
      (∀ i : Fin t.n,
        finiteWordRun ws checkWord
            (Qatlib.Foundations.PureStateMath.Ket (regPad ws (t.w + 1) (regCat (t.rowReg i) (fun _ : Fin 1 => false)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPad ws (t.w + 1)
            (regCat (t.rowReg i) (fun _ : Fin 1 => M (t.rowReg i)))))) ∧
      d.tableReads = d.abstractQueries * t.w ∧
      d.abstractQueries * t.w + checkWord.length + extWord.length ≤
        d.backend.elementaryGates + d.abstractQueries * t.w ∧
      ws ≤ d.backend.peakLiveQubits

/-- Specifies legal selection and extraction words, with the selection word flagging table rows
whose encoded value equals the chosen minimum. The supplied ledger bounds their lengths,
classical bit operations, and workspace. -/
def HasMinimumExtract (t : InputTable) (hn : 0 < t.n) (d : DataAccessLedger) : Prop :=
  ∃ (ws : ℕ) (selWord extWord : List FiniteGateCode),
    finiteWordLegal ws selWord = true ∧
      finiteWordLegal ws extWord = true ∧
      (∀ i : Fin t.n,
        finiteWordRun ws selWord
            (Qatlib.Foundations.PureStateMath.Ket (regPad ws (t.w + 1) (regCat (t.rowReg i) (fun _ : Fin 1 => false)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPad ws (t.w + 1)
            (regCat (t.rowReg i) (fun _ : Fin 1 =>
              decide (regValue (t.rowReg i) = regValue (t.rowReg (t.argmin hn)))))))) ∧
      selWord.length + extWord.length ≤ d.backend.elementaryGates ∧
      32 * (t.n + 1) * (t.w + 1) * (t.w + 1) ≤ d.backend.classicalBitOps ∧
      ws ≤ d.backend.peakLiveQubits

/-- Specifies a finite word computing the table's row-block reordering and a legal extraction
word, subject to the stated gate, classical operation, and live-qubit bounds. -/
def HasSortingExtract (t : InputTable) (d : DataAccessLedger) : Prop :=
  ∃ netWord extWord : List FiniteGateCode,
    FiniteWordComputes (t.n * t.w) (t.n * t.w) netWord t.sortBlocks ∧
      finiteWordLegal (t.n * t.w) extWord = true ∧
      netWord.length + extWord.length ≤ d.backend.elementaryGates ∧
      64 * (t.n + 1) * (t.w + 1) * (t.w + 1) ≤ d.backend.classicalBitOps ∧
      t.n * t.w ≤ d.backend.peakLiveQubits

/-- The conjunction of the stated loading, comparison, and extraction gate budgets with the
table-read, abstract-query, classical operation, and live-qubit ledger inequalities. -/
def HasDataAccessTranslation (t : InputTable) (loadGates compareGates extractGates : ℕ)
    (d : DataAccessLedger) : Prop :=
  loadGates ≤ t.w ∧
    compareGates ≤ 32 * (t.w + 1) * (t.w + 1) ∧
    extractGates ≤ 16 * (t.w + 1) * (t.w + 1) ∧
    d.tableReads = d.abstractQueries * t.w ∧
    d.abstractQueries * loadGates + compareGates + extractGates ≤
      d.backend.elementaryGates ∧
    d.backend.elementaryGates ≤ d.backend.classicalBitOps ∧
    2 * t.w + 1 ≤ d.backend.peakLiveQubits ∧
    d.backend.forwardCalls + d.backend.backwardCalls + d.backend.controlledCalls =
      d.abstractQueries

/-- The numbers of data and phase wires in an amplitude-estimation register layout with one
additional flag wire. -/
structure AEEncoding where
  dataWires : ℕ
  phaseWires : ℕ

/-- The total workspace width: data wires plus phase wires plus one flag wire. -/
abbrev AEEncoding.workspace (e : AEEncoding) : ℕ := e.dataWires + (e.phaseWires + 1)

/-- Extracts the initial data-wire block from an encoded workspace register. -/
def AEEncoding.dataBits (e : AEEncoding) (r : Reg e.workspace) : Reg e.dataWires :=
  fun i => r ⟨i.val, by show i.val < e.dataWires + (e.phaseWires + 1); omega⟩

/-- Extracts the phase-wire block following the data wires in an encoded workspace register. -/
def AEEncoding.phaseBits (e : AEEncoding) (r : Reg e.workspace) : Reg e.phaseWires :=
  fun i => r ⟨e.dataWires + i.val, by
    show e.dataWires + i.val < e.dataWires + (e.phaseWires + 1); omega⟩

/-- Extracts the flag bit following the data and phase blocks. -/
def AEEncoding.flagBit (e : AEEncoding) (r : Reg e.workspace) : Bool :=
  r ⟨e.dataWires + e.phaseWires, by
    show e.dataWires + e.phaseWires < e.dataWires + (e.phaseWires + 1); omega⟩

/-- Assembles a workspace register from its data block, phase block, and flag bit. -/
def AEEncoding.layout (e : AEEncoding) (x : Reg e.dataWires) (p : Reg e.phaseWires) (b : Bool) :
    Reg e.workspace :=
  fun i =>
    if h : (i : ℕ) < e.dataWires then x ⟨i.val, h⟩
    else if h2 : (i : ℕ) < e.dataWires + e.phaseWires then
      p ⟨i.val - e.dataWires, by omega⟩
    else b

/-- Lifts a data-register matrix to the full workspace by acting identically on the phase and
flag components. -/
noncomputable def AEEncoding.dataLift (e : AEEncoding)
    (U : Matrix (Reg e.dataWires) (Reg e.dataWires) ℂ) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  fun r s => U (e.dataBits r) (e.dataBits s) *
    if e.phaseBits r = e.phaseBits s ∧ e.flagBit r = e.flagBit s then 1 else 0

/-- Lifts a phase-register matrix to the full workspace by acting identically on the data and
flag components. -/
noncomputable def AEEncoding.phaseLift (e : AEEncoding)
    (U : Matrix (Reg e.phaseWires) (Reg e.phaseWires) ℂ) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  fun r s => U (e.phaseBits r) (e.phaseBits s) *
    if e.dataBits r = e.dataBits s ∧ e.flagBit r = e.flagBit s then 1 else 0

/-- Lifts a data-register matrix controlled by a true flag bit, acting as the identity for a
false flag and preserving the phase register. -/
noncomputable def AEEncoding.controlledDataLift (e : AEEncoding)
    (U : Matrix (Reg e.dataWires) (Reg e.dataWires) ℂ) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  fun r s =>
    if e.flagBit r = e.flagBit s then
      if e.flagBit r = false then (if r = s then (1 : ℂ) else 0)
      else U (e.dataBits r) (e.dataBits s) *
        if e.phaseBits r = e.phaseBits s then 1 else 0
    else 0

/-- The workspace lift of reflection about a data basis state, controlled by the flag bit. -/
noncomputable def AEEncoding.controlledReflectLift (e : AEEncoding) (j : Reg e.dataWires) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  e.controlledDataLift (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j)))

/-- The quantum Fourier transform on the phase register, relabeled from finite indices to
Boolean registers. -/
noncomputable def AEEncoding.phaseQFT (e : AEEncoding) :
    Matrix (Reg e.phaseWires) (Reg e.phaseWires) ℂ :=
  relabelGate (bitVecEquiv e.phaseWires).symm (QFTMatrix (2 ^ e.phaseWires))

/-- A finite gate word is legal and approximates the specified matrix action within ε in
Euclidean norm on every normalized input state. -/
def RealizesOperatorWithin (n : ℕ) (gs : List FiniteGateCode)
    (M : Matrix (Reg n) (Reg n) ℂ) (ε : ℝ) : Prop :=
  finiteWordLegal n gs = true ∧
    ∀ ψ : QState (Reg n), Normalized ψ →
      ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ -
        ApplyGate M ψ)‖ ≤ ε

/-- Finite gate words for preparation, inverse and controlled preparation, controlled
reflection, and forward and backward transforms, together with readout precision and a
marking-query count. -/
structure AEFiniteProgram where
  prec : ℕ
  initWord : List FiniteGateCode
  initInvWord : List FiniteGateCode
  controlledInitWord : List FiniteGateCode
  controlledInitInvWord : List FiniteGateCode
  controlledReflectWord : List FiniteGateCode
  forwardWord : List FiniteGateCode
  backwardWord : List FiniteGateCode
  markQueries : ℕ

/-- The native rational amplitude decoder evaluated at the finite program's chosen precision. -/
def AEFiniteProgram.decode (P : AEFiniteProgram) (M : ℕ) (z : Fin M) : ℚ :=
  nativeAEDecode M P.prec z

/-- The gate-depth, bit-time, bit-space, and query counts recorded for a finite
amplitude-estimation program. -/
structure AEProgramLedger where
  gateDepth : ℕ
  bitTime : ℕ
  bitSpace : ℕ
  queries : ℕ

/-- The sum of the initialization window, reflection window, twice the QFT window, and the
dyadic readout error 2^(−prec). -/
noncomputable def unifiedErrorBudget (initWin reflectWin qftWin : ℝ) (prec : ℕ) : ℝ :=
  initWin + reflectWin + 2 * qftWin + ((2 : ℝ)⁻¹) ^ prec

/-- Specifies legal finite words approximating each encoded amplitude-estimation component at
its assigned error tolerance. It also fixes the marking-query count, word-length and
workspace ledger identities, and the unified error-budget expression. -/
def HasAEFiniteImplementation (enc : AEEncoding) (P : AEFiniteProgram)
    (A : Matrix (Reg enc.dataWires) (Reg enc.dataWires) ℂ) (j : Reg enc.dataWires)
    (initWin reflectWin qftWin : ℝ) (d : AEProgramLedger) : Prop :=
  RealizesOperatorWithin enc.workspace P.initWord (enc.dataLift A) initWin ∧
    RealizesOperatorWithin enc.workspace P.initInvWord
      (enc.dataLift A.conjTranspose) initWin ∧
    RealizesOperatorWithin enc.workspace P.controlledInitWord
      (enc.controlledDataLift A) initWin ∧
    RealizesOperatorWithin enc.workspace P.controlledInitInvWord
      (enc.controlledDataLift A.conjTranspose) initWin ∧
    RealizesOperatorWithin enc.workspace P.controlledReflectWord
      (enc.controlledReflectLift j) reflectWin ∧
    RealizesOperatorWithin enc.workspace P.forwardWord
      (enc.phaseLift enc.phaseQFT) qftWin ∧
    RealizesOperatorWithin enc.workspace P.backwardWord
      (enc.phaseLift (enc.phaseQFT).conjTranspose) qftWin ∧
    P.markQueries = 2 ^ enc.phaseWires - 1 ∧
    d.queries = P.markQueries ∧
    d.gateDepth = P.initWord.length + P.initInvWord.length +
      P.controlledInitWord.length + P.controlledInitInvWord.length +
      P.controlledReflectWord.length + P.forwardWord.length + P.backwardWord.length ∧
    d.bitTime = d.gateDepth * enc.workspace ∧
    d.bitSpace = enc.workspace ∧
    initWin + reflectWin + 2 * qftWin + ((2 : ℝ)⁻¹) ^ P.prec =
      unifiedErrorBudget initWin reflectWin qftWin P.prec

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
