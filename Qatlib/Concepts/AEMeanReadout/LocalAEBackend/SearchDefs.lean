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
set_option warningAsError false
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

structure StageParams where
  grid : ℕ
  prec : ℕ
  mid : ℕ
  win : ℚ

abbrev StageLabels (p : StageParams) : Type := Fin (2 * p.mid + 1) → ℚ

def insertSortedRat (x : ℚ) : List ℚ → List ℚ × ℕ
  | [] => ([x], 0)
  | y :: ys =>
    if x ≤ y then (x :: y :: ys, 1)
    else
      let s := insertSortedRat x ys
      (y :: s.1, s.2 + 1)

def sortCountedRat : List ℚ → List ℚ × ℕ
  | [] => ([], 0)
  | x :: xs =>
    let s := sortCountedRat xs
    let t := insertSortedRat x s.1
    (t.1, s.2 + t.2)

def stageMedianCounted (p : StageParams) (ys : StageLabels p) : ℚ × ℕ :=
  let s := sortCountedRat (List.ofFn ys)
  (s.1.getD p.mid 0, s.2)

def stageOutput (p : StageParams) (ys : StageLabels p) : ℚ :=
  (stageMedianCounted p ys).1

def stageComparisons (p : StageParams) (ys : StageLabels p) : ℕ :=
  (stageMedianCounted p ys).2

def composedOutput {n : ℕ} (ws : Fin n → ℚ) (ps : Fin n → StageParams)
    (ys : ∀ i : Fin n, StageLabels (ps i)) : ℚ :=
  ∑ i : Fin n, ws i * stageOutput (ps i) (ys i)

def composedComparisons {n : ℕ} (ps : Fin n → StageParams)
    (ys : ∀ i : Fin n, StageLabels (ps i)) : ℕ :=
  ∑ i : Fin n, stageComparisons (ps i) (ys i)

def stageMarkQueries (p : StageParams) : ℕ := (2 * p.mid + 1) * (p.grid - 1)

def stagePreparationCalls (p : StageParams) : ℕ := (2 * p.mid + 1) * (2 * p.grid - 1)

def stageDecodeTerms (p : StageParams) : ℕ := (2 * p.mid + 1) * (8 * (p.prec + 8))

noncomputable def stageLaunches {I : Type} [Fintype I] [DecidableEq I] (p : StageParams)
    (A : Matrix I I ℂ) (j : I) : List (Circuit (Fin p.grid × (Bool × I))) :=
  List.replicate (2 * p.mid + 1) (countedAECircuit p.grid A j)

structure StageLedger where
  markQueries : ℕ
  prepCalls : ℕ
  comparisons : ℕ
  decodeTerms : ℕ

def StageLedger.zero : StageLedger := ⟨0, 0, 0, 0⟩

def StageLedger.add (a b : StageLedger) : StageLedger :=
  { markQueries := a.markQueries + b.markQueries
    prepCalls := a.prepCalls + b.prepCalls
    comparisons := a.comparisons + b.comparisons
    decodeTerms := a.decodeTerms + b.decodeTerms }

def stageLedger (p : StageParams) (ys : StageLabels p) : StageLedger :=
  { markQueries := stageMarkQueries p
    prepCalls := stagePreparationCalls p
    comparisons := stageComparisons p ys
    decodeTerms := stageDecodeTerms p }

abbrev StageChooser := List (StageParams × ℚ) → Option StageParams

def windowStops (target : ℚ) : List (StageParams × ℚ) → Bool
  | [] => false
  | (p, _) :: rest => decide (p.win ≤ target) || windowStops target rest

def windowChooser (target : ℚ) (budget : ℕ) (next : ℕ → StageParams) : StageChooser :=
  fun hist =>
    if windowStops target hist = true ∨ budget ≤ hist.length then none
    else some (next hist.length)

def runStages (chooser : StageChooser) (source : (p : StageParams) → StageLabels p) :
    ℕ → List (StageParams × ℚ) → List (StageParams × ℚ)
  | 0, hist => hist
  | fuel + 1, hist =>
    match chooser hist with
    | none => hist
    | some p => runStages chooser source fuel (hist ++ [(p, stageOutput p (source p))])

def runOutput (hist : List (StageParams × ℚ)) : ℚ :=
  hist.foldl (fun _ s => s.2) 0

def runLedger (source : (p : StageParams) → StageLabels p)
    (hist : List (StageParams × ℚ)) : StageLedger :=
  hist.foldl (fun d s => d.add (stageLedger s.1 (source s.1))) StageLedger.zero

def nativeStageParams (k : ℕ) : StageParams :=
  { grid := layerGrid k
    prec := 2 * k + 8
    mid := layerRepetitions k
    win := ((2 : ℚ)⁻¹) ^ k }

def nativeStageWeights (k : ℕ) : Fin (k + 2) → ℚ := fun l => (2 : ℚ) ^ l.val

def nativeStageLabels (k : ℕ) (ω : LayerRecord k) (l : Fin (k + 2)) :
    StageLabels (nativeStageParams k) :=
  fun z => nativeAEDecode (layerGrid k) (2 * k + 8) (ω l z)

structure InputTable where
  n : ℕ
  w : ℕ
  cell : Fin n → Fin w → Bool

def InputTable.rowReg (t : InputTable) (i : Fin t.n) : Reg t.w := fun b => t.cell i b

def regValue {w : ℕ} (r : Reg w) : ℕ :=
  ∑ b : Fin w, if r b = true then 2 ^ (b.val) else 0

def rowLess {w : ℕ} (x y : Reg w) : Bool := decide (regValue x < regValue y)

def InputTable.argmin (t : InputTable) (hn : 0 < t.n) : Fin t.n :=
  (List.finRange t.n).foldl
    (fun best i => if regValue (t.rowReg i) < regValue (t.rowReg best) then i else best)
    ⟨0, hn⟩

def InputTable.sortOrder (t : InputTable) : List (Fin t.n) :=
  (List.finRange t.n).mergeSort fun a b =>
    if regValue (t.rowReg a) = regValue (t.rowReg b) then decide (a.val ≤ b.val)
    else decide (regValue (t.rowReg a) ≤ regValue (t.rowReg b))

def InputTable.loadWord (t : InputTable) (i : Fin t.n) : List FiniteGateCode :=
  (List.finRange t.w).filterMap fun b =>
    if t.cell i b = true then some (FiniteGateCode.x b.val) else none

def compareRowL {w : ℕ} (r : Reg (w + (w + 1))) : Reg w :=
  fun i => r ⟨i.val, by omega⟩

def compareRowR {w : ℕ} (r : Reg (w + (w + 1))) : Reg w :=
  fun i => r ⟨w + i.val, by omega⟩

def compareFlag {w : ℕ} (r : Reg (w + (w + 1))) : Bool :=
  r ⟨w + w, by omega⟩

def compareUpdate {w : ℕ} (r : Reg (w + (w + 1))) : Reg (w + (w + 1)) :=
  fun i =>
    if i.val = w + w then
      Bool.xor (r i) (rowLess (compareRowL r) (compareRowR r))
    else r i

structure DataAccessLedger where
  backend : BackendLedger
  tableReads : ℕ

def DataAccessLedger.abstractQueries (d : DataAccessLedger) : ℕ :=
  d.backend.forwardCalls + d.backend.backwardCalls + d.backend.controlledCalls

def HasTableLoad (t : InputTable) (d : DataAccessLedger) : Prop :=
  (∀ i : Fin t.n,
    finiteWordLegal t.w (t.loadWord i) = true ∧
      finiteWordRun t.w (t.loadWord i) (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin t.w => false)) =
        some (Qatlib.Foundations.PureStateMath.Ket (t.rowReg i)) ∧
      (t.loadWord i).length ≤ t.w) ∧
    d.tableReads = t.n * t.w ∧
    (∑ i : Fin t.n, (t.loadWord i).length) ≤ d.backend.elementaryGates

def HasCompareSynthesis (w : ℕ) (d : DataAccessLedger) : Prop :=
  ∃ cmpWord : List FiniteGateCode,
    FiniteWordComputes (w + (w + 1)) (w + (w + 1)) cmpWord (compareUpdate (w := w)) ∧
      cmpWord.length ≤ 32 * (w + 1) * (w + 1) ∧
      cmpWord.length ≤ d.backend.elementaryGates ∧
      2 * w + 1 ≤ d.backend.peakLiveQubits

def tableWire (n w : ℕ) (i : Fin n) (b : Fin w) : Fin (n * w) :=
  ⟨i.val * w + b.val, by
    have h1 : i.val * w + b.val < i.val * w + w := Nat.add_lt_add_left b.isLt _
    have h2 : i.val * w + w = (i.val + 1) * w := (Nat.succ_mul i.val w).symm
    have h3 : (i.val + 1) * w ≤ n * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    exact Nat.lt_of_lt_of_le h1 (h2.le.trans h3)⟩

def InputTable.packed (t : InputTable) : Reg (t.n * t.w) :=
  fun k =>
    if hw : 0 < t.w then
      t.cell ⟨k.val / t.w, Nat.div_lt_of_lt_mul (k.isLt.trans_le (Nat.mul_comm t.n t.w).le)⟩
        ⟨k.val % t.w, Nat.mod_lt _ hw⟩
    else false

def InputTable.sortBlocks (t : InputTable) (r : Reg (t.n * t.w)) : Reg (t.n * t.w) :=
  fun k =>
    if hw : 0 < t.w then
      match t.sortOrder[k.val / t.w]? with
      | some i => r (tableWire t.n t.w i ⟨k.val % t.w, Nat.mod_lt _ hw⟩)
      | none => r k
    else false

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

def HasSortingExtract (t : InputTable) (d : DataAccessLedger) : Prop :=
  ∃ netWord extWord : List FiniteGateCode,
    FiniteWordComputes (t.n * t.w) (t.n * t.w) netWord t.sortBlocks ∧
      finiteWordLegal (t.n * t.w) extWord = true ∧
      netWord.length + extWord.length ≤ d.backend.elementaryGates ∧
      64 * (t.n + 1) * (t.w + 1) * (t.w + 1) ≤ d.backend.classicalBitOps ∧
      t.n * t.w ≤ d.backend.peakLiveQubits

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

structure AEEncoding where
  dataWires : ℕ
  phaseWires : ℕ

abbrev AEEncoding.workspace (e : AEEncoding) : ℕ := e.dataWires + (e.phaseWires + 1)

def AEEncoding.dataBits (e : AEEncoding) (r : Reg e.workspace) : Reg e.dataWires :=
  fun i => r ⟨i.val, by show i.val < e.dataWires + (e.phaseWires + 1); omega⟩

def AEEncoding.phaseBits (e : AEEncoding) (r : Reg e.workspace) : Reg e.phaseWires :=
  fun i => r ⟨e.dataWires + i.val, by
    show e.dataWires + i.val < e.dataWires + (e.phaseWires + 1); omega⟩

def AEEncoding.flagBit (e : AEEncoding) (r : Reg e.workspace) : Bool :=
  r ⟨e.dataWires + e.phaseWires, by
    show e.dataWires + e.phaseWires < e.dataWires + (e.phaseWires + 1); omega⟩

def AEEncoding.layout (e : AEEncoding) (x : Reg e.dataWires) (p : Reg e.phaseWires) (b : Bool) :
    Reg e.workspace :=
  fun i =>
    if h : (i : ℕ) < e.dataWires then x ⟨i.val, h⟩
    else if h2 : (i : ℕ) < e.dataWires + e.phaseWires then
      p ⟨i.val - e.dataWires, by omega⟩
    else b

noncomputable def AEEncoding.dataLift (e : AEEncoding)
    (U : Matrix (Reg e.dataWires) (Reg e.dataWires) ℂ) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  fun r s => U (e.dataBits r) (e.dataBits s) *
    if e.phaseBits r = e.phaseBits s ∧ e.flagBit r = e.flagBit s then 1 else 0

noncomputable def AEEncoding.phaseLift (e : AEEncoding)
    (U : Matrix (Reg e.phaseWires) (Reg e.phaseWires) ℂ) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  fun r s => U (e.phaseBits r) (e.phaseBits s) *
    if e.dataBits r = e.dataBits s ∧ e.flagBit r = e.flagBit s then 1 else 0

noncomputable def AEEncoding.controlledDataLift (e : AEEncoding)
    (U : Matrix (Reg e.dataWires) (Reg e.dataWires) ℂ) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  fun r s =>
    if e.flagBit r = e.flagBit s then
      if e.flagBit r = false then (if r = s then (1 : ℂ) else 0)
      else U (e.dataBits r) (e.dataBits s) *
        if e.phaseBits r = e.phaseBits s then 1 else 0
    else 0

noncomputable def AEEncoding.controlledReflectLift (e : AEEncoding) (j : Reg e.dataWires) :
    Matrix (Reg e.workspace) (Reg e.workspace) ℂ :=
  e.controlledDataLift (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j)))

noncomputable def AEEncoding.phaseQFT (e : AEEncoding) :
    Matrix (Reg e.phaseWires) (Reg e.phaseWires) ℂ :=
  relabelGate (bitVecEquiv e.phaseWires).symm (QFTMatrix (2 ^ e.phaseWires))

def RealizesOperatorWithin (n : ℕ) (gs : List FiniteGateCode)
    (M : Matrix (Reg n) (Reg n) ℂ) (ε : ℝ) : Prop :=
  finiteWordLegal n gs = true ∧
    ∀ ψ : QState (Reg n), Normalized ψ →
      ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ -
        ApplyGate M ψ)‖ ≤ ε

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

def AEFiniteProgram.decode (P : AEFiniteProgram) (M : ℕ) (z : Fin M) : ℚ :=
  nativeAEDecode M P.prec z

structure AEProgramLedger where
  gateDepth : ℕ
  bitTime : ℕ
  bitSpace : ℕ
  queries : ℕ

noncomputable def unifiedErrorBudget (initWin reflectWin qftWin : ℝ) (prec : ℕ) : ℝ :=
  initWin + reflectWin + 2 * qftWin + ((2 : ℝ)⁻¹) ^ prec

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
