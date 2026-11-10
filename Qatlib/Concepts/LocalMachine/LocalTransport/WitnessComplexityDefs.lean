/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.WalshMoment.Forrelation.UniformVerifierDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs

open Qatlib
open Matrix
open scoped ComplexOrder

structure BitstringPromise where
  yes : Finset (List Bool)
  no : Finset (List Bool)
  disjoint : Disjoint yes no

def langAsPromise (S : Finset (List Bool)) : BitstringPromise where
  yes := S
  no := ∅
  disjoint := by simp

inductive WitnessInstruction where
  | fixed (gate : FiniteGateCode)
  | oracle (addresses : List ℕ) (target : ℕ)
  deriving DecidableEq, Repr

structure WitnessVerifierProgram where
  witnessBits : ℕ
  inputBits : ℕ
  ancillaBits : ℕ
  outputWire : ℕ
  instructions : List WitnessInstruction
  deriving DecidableEq, Repr

def programQubits (p : WitnessVerifierProgram) : ℕ :=
  p.witnessBits + p.inputBits + p.ancillaBits

def instructionLegal (q : ℕ) : WitnessInstruction → Prop
  | .fixed gate => finiteCodeLegal q gate = true
  | .oracle addresses target =>
      target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup

def witnessProgramLegal (p : WitnessVerifierProgram) : Prop :=
  p.outputWire < programQubits p ∧
    ∀ i ∈ p.instructions, instructionLegal (programQubits p) i

def oracleFree (p : WitnessVerifierProgram) : Prop :=
  p.instructions.all fun
    | .fixed _ => true
    | .oracle _ _ => false

def defaultVerifierProgram : WitnessVerifierProgram where
  witnessBits := 0
  inputBits := 0
  ancillaBits := 0
  outputWire := 0
  instructions := []

abbrev ClassicalOracle := ∀ ell : ℕ, Reg ell → Bool

def readAddress {q : ℕ} (x : Reg q) (addresses : List ℕ)
    (haddr : ∀ a ∈ addresses, a < q) : Reg addresses.length :=
  fun i => x ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩

def xorQueryUpdate (A : ClassicalOracle) {q : ℕ} (addresses : List ℕ)
    (target : ℕ) (htarget : target < q) (haddr : ∀ a ∈ addresses, a < q) :
    Reg q → Reg q := fun x =>
  Function.update x ⟨target, htarget⟩
    (x ⟨target, htarget⟩ ^^ A addresses.length (readAddress x addresses haddr))

noncomputable def xorQueryMatrix (A : ClassicalOracle) (q : ℕ)
    (addresses : List ℕ) (target : ℕ) : Matrix (Reg q) (Reg q) ℂ := by
  classical
  exact if h : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧
      addresses.Nodup then
    permMatrix (xorQueryUpdate A addresses target h.1 h.2.1)
  else 1

noncomputable def controlledXorUpdate (A : ClassicalOracle) {q : ℕ}
    (addresses : List ℕ) (target control : ℕ) (htarget : target < q)
    (hcontrol : control < q) (haddr : ∀ a ∈ addresses, a < q) :
    Reg q → Reg q := fun x =>
  Function.update x ⟨target, htarget⟩
    (x ⟨target, htarget⟩ ^^ (x ⟨control, hcontrol⟩ &&
      A addresses.length (readAddress x addresses haddr)))

noncomputable def controlledXorMatrix (A : ClassicalOracle) (q : ℕ)
    (addresses : List ℕ) (target control : ℕ) : Matrix (Reg q) (Reg q) ℂ := by
  classical
  exact if h : target < q ∧ control < q ∧ control ≠ target ∧
      (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup then
    permMatrix
      (controlledXorUpdate A addresses target control h.1 h.2.1 h.2.2.2.1)
  else 1

def appendedControlOracle (A : ClassicalOracle) : ClassicalOracle := fun ell r =>
  match ell with
  | 0 => false
  | ℓ + 1 => r (Fin.last _) && A ℓ (fun i => r i.castSucc)

noncomputable def instructionMatrix (A : ClassicalOracle) (q : ℕ) :
    WitnessInstruction → Matrix (Reg q) (Reg q) ℂ
  | .fixed gate => finiteCodeMatrix q gate
  | .oracle addresses target => xorQueryMatrix A q addresses target

noncomputable def programMatrix (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  (p.instructions.map (instructionMatrix A (programQubits p))).reverse.prod

noncomputable def programRun (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (ψ : QState (Reg (programQubits p))) : QState (Reg (programQubits p)) :=
  programMatrix A p *ᵥ ψ

def oracleQueryCount (p : WitnessVerifierProgram) : ℕ :=
  (p.instructions.filterMap fun
    | .fixed _ => none
    | .oracle _ _ => some ()).length

def addressBitLedger (p : WitnessVerifierProgram) : ℕ :=
  (p.instructions.filterMap fun
    | .fixed _ => none
    | .oracle addresses _ => some addresses.length).sum

variable (p : WitnessVerifierProgram)

def witnessWire (i : Fin p.witnessBits) : Fin (programQubits p) :=
  ⟨i.val, by simp only [programQubits]; omega⟩

def inputWire (i : Fin p.inputBits) : Fin (programQubits p) :=
  ⟨p.witnessBits + i.val, by simp only [programQubits]; omega⟩

def ancillaWire (i : Fin p.ancillaBits) : Fin (programQubits p) :=
  ⟨p.witnessBits + p.inputBits + i.val, by simp only [programQubits]; omega⟩

def witnessRestrict (z : Reg (programQubits p)) : Reg p.witnessBits :=
  fun i => z (witnessWire p i)

def inputRestrict (z : Reg (programQubits p)) : Reg p.inputBits :=
  fun i => z (inputWire p i)

def ancillaZero (z : Reg (programQubits p)) : Prop :=
  ∀ i : Fin p.ancillaBits, z (ancillaWire p i) = false

variable {p}

def listToInput (p : WitnessVerifierProgram) (x : List Bool) :
    Reg p.inputBits := fun i => x.getD i.val false

open Classical in

noncomputable def verifierInitialState (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (w : QState (Reg p.witnessBits)) :
    QState (Reg (programQubits p)) :=
  fun z => if inputRestrict p z = x ∧ ancillaZero p z then w (witnessRestrict p z) else 0

open Classical in

noncomputable def verifierInputDensity (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun z z' =>
    if inputRestrict p z = x ∧ inputRestrict p z' = x ∧
        ancillaZero p z ∧ ancillaZero p z' then
      σ (witnessRestrict p z) (witnessRestrict p z')
    else 0

def programOutputEvent (p : WitnessVerifierProgram) :
    Finset (Reg (programQubits p)) :=
  if h : p.outputWire < programQubits p then
    Finset.univ.filter fun z => z ⟨p.outputWire, h⟩ = true
  else ∅

noncomputable def acceptProb (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    ℝ :=
  ∑ z ∈ programOutputEvent p,
    ((programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) z z).re

def IsWitnessDensity {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Prop :=
  σ.IsHermitian ∧ σ.PosSemidef ∧ Matrix.trace σ ≤ 1

noncomputable def pureWitnessDensity {m : ℕ} (ψ : QState (Reg m)) :
    Matrix (Reg m) (Reg m) ℂ := outerProduct ψ

noncomputable def classicalWitnessDensity {m : ℕ} (w : Reg m) :
    Matrix (Reg m) (Reg m) ℂ := outerProduct (Ket w)

def classicalWitnessEncoding (p : WitnessVerifierProgram) (w : Reg p.witnessBits) :
    Reg (programQubits p) := fun i =>
  if h : i.val < p.witnessBits then w ⟨i.val, h⟩ else false

structure WitnessVerifierFamily where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ
  programCoefficient : ℕ
  programDegree : ℕ

def witnessPolynomialBound (c d n : ℕ) : ℕ := c * (n + 1) ^ d

private def runUntilHaltWithin {k : ℕ}
    (machine : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) :
    ℕ → Turing.TM0.Cfg (Option Bool) (Fin (k + 1)) →
      Option (Turing.TM0.Cfg (Option Bool) (Fin (k + 1)))
  | 0, cfg => if Turing.TM0.step machine cfg = none then some cfg else none
  | fuel + 1, cfg =>
      match Turing.TM0.step machine cfg with
      | none => some cfg
      | some next => runUntilHaltWithin machine fuel next

private def readOutputUntilBlank : ℕ → Turing.ListBlank (Option Bool) → Option (List Bool)
  | 0, tape => if tape.nth 0 = none then some [] else none
  | fuel + 1, tape =>
      match tape.nth 0 with
      | none => some []
      | some bit => (readOutputUntilBlank fuel tape.tail).map (bit :: ·)

private def parseUnaryField : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseUnaryField rest).map fun (k, tail) => (k + 1, tail)

private def parseManyNatFields : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← parseUnaryField bits
      let (tail, finalBits) ← parseManyNatFields count rest
      pure (head :: tail, finalBits)

private def parseInstructionFields (tag : ℕ) (bits : List Bool) :
    Option (WitnessInstruction × List Bool) := do
  if tag = 0 then
    let (w, rest) ← parseUnaryField bits
    pure (.fixed (.h w), rest)
  else if tag = 1 then
    let (w, rest) ← parseUnaryField bits
    pure (.fixed (.x w), rest)
  else if tag = 2 then
    let (w, rest) ← parseUnaryField bits
    pure (.fixed (.t w), rest)
  else if tag = 3 then
    let (w, rest) ← parseUnaryField bits
    pure (.fixed (.tdg w), rest)
  else if tag = 4 then
    let (c, rest) ← parseUnaryField bits
    let (t, tail) ← parseUnaryField rest
    pure (.fixed (.cx c t), tail)
  else if tag = 5 then
    let (count, rest) ← parseUnaryField bits
    let (addresses, rest') ← parseManyNatFields count rest
    let (target, tail) ← parseUnaryField rest'
    pure (.oracle addresses target, tail)
  else
    none

private def parseInstructionListFuel : ℕ → List Bool → Option (List WitnessInstruction)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, bits => do
      let (tag, rest) ← parseUnaryField bits
      let (instruction, tail) ← parseInstructionFields tag rest
      let instructions ← parseInstructionListFuel fuel tail
      pure (instruction :: instructions)

def decodeWitnessVerifierProgram (bits : List Bool) : Option WitnessVerifierProgram := do
  if bits.all id then
    pure ⟨0, bits.length, 1, 0, []⟩
  else
    let (witnessBits, rest) ← parseUnaryField bits
    let (inputBits, rest') ← parseUnaryField rest
    let (ancillaBits, rest'') ← parseUnaryField rest'
    let (outputWire, instructionsBits) ← parseUnaryField rest''
    let instructions ← parseInstructionListFuel instructionsBits.length instructionsBits
    pure ⟨witnessBits, inputBits, ancillaBits, outputWire, instructions⟩

private def unaryInput (n : ℕ) : List (Option Bool) :=
  List.replicate n (some true)

variable (f : WitnessVerifierFamily)

private def generatorFuel (f : WitnessVerifierFamily) (n : ℕ) : ℕ :=
  witnessPolynomialBound f.timeCoefficient f.timeDegree n

private def generatorProgramBound (f : WitnessVerifierFamily) (n : ℕ) : ℕ :=
  witnessPolynomialBound f.programCoefficient f.programDegree n

noncomputable def witnessProgramAt (f : WitnessVerifierFamily) (n : ℕ) :
    Option WitnessVerifierProgram :=
  (runUntilHaltWithin f.machine (generatorFuel f n)
    (Turing.TM0.init (unaryInput n))).bind fun cfg =>
      (readOutputUntilBlank (n + generatorFuel f n + 1) cfg.Tape.right₀).bind
        decodeWitnessVerifierProgram

noncomputable def familyProgram (f : WitnessVerifierFamily) (n : ℕ) : WitnessVerifierProgram :=
  (witnessProgramAt f n).getD defaultVerifierProgram

def witnessFamilyValid (f : WitnessVerifierFamily) : Prop :=
  ∀ n : ℕ, ∃ p : WitnessVerifierProgram,
    witnessProgramAt f n = some p ∧
      p.inputBits = n ∧
      programQubits p ≤ generatorProgramBound f n ∧
      p.instructions.length ≤ generatorProgramBound f n ∧
      witnessProgramLegal p

variable {f}

def InQMAWith (A : ClassicalOracle) (L : BitstringPromise) : Prop :=
  ∃ f : WitnessVerifierFamily, witnessFamilyValid f ∧
    (∀ n, oracleFree (familyProgram f n)) ∧
    (∀ x ∈ L.yes, ∃ σ : Matrix (Reg (familyProgram f x.length).witnessBits)
        (Reg (familyProgram f x.length).witnessBits) ℂ,
      IsWitnessDensity σ ∧
        2 / 3 ≤ acceptProb A (familyProgram f x.length) (listToInput _ x) σ) ∧
    (∀ x ∈ L.no, ∀ σ : Matrix (Reg (familyProgram f x.length).witnessBits)
        (Reg (familyProgram f x.length).witnessBits) ℂ,
      IsWitnessDensity σ →
        acceptProb A (familyProgram f x.length) (listToInput _ x) σ ≤ 1 / 3)

def InQMA (L : BitstringPromise) : Prop := InQMAWith (fun _ _ => false) L

def InQCMA (L : BitstringPromise) : Prop :=
  ∃ f : WitnessVerifierFamily, witnessFamilyValid f ∧
    (∀ n, oracleFree (familyProgram f n)) ∧
    (∀ x ∈ L.yes, ∃ w : Reg (familyProgram f x.length).witnessBits,
      2 / 3 ≤ acceptProb (fun _ _ => false) (familyProgram f x.length)
          (listToInput _ x) (classicalWitnessDensity w)) ∧
    (∀ x ∈ L.no, ∀ w : Reg (familyProgram f x.length).witnessBits,
      acceptProb (fun _ _ => false) (familyProgram f x.length)
          (listToInput _ x) (classicalWitnessDensity w) ≤ 1 / 3)

def InBQPWitnessModel (L : BitstringPromise) : Prop :=
  ∃ f : WitnessVerifierFamily, witnessFamilyValid f ∧
    (∀ n, oracleFree (familyProgram f n) ∧ (familyProgram f n).witnessBits = 0) ∧
    (∀ x ∈ L.yes, 2 / 3 ≤ acceptProb (fun _ _ => false) (familyProgram f x.length)
        (listToInput _ x) 1) ∧
    (∀ x ∈ L.no, acceptProb (fun _ _ => false) (familyProgram f x.length)
        (listToInput _ x) 1 ≤ 1 / 3)

def padWire (witnessBits k : ℕ) (w : ℕ) : ℕ :=
  if w < witnessBits then w else w + k

def padFiniteCode (witnessBits k : ℕ) : FiniteGateCode → FiniteGateCode
  | .h w => .h (padWire witnessBits k w)
  | .x w => .x (padWire witnessBits k w)
  | .t w => .t (padWire witnessBits k w)
  | .tdg w => .tdg (padWire witnessBits k w)
  | .cx c t => .cx (padWire witnessBits k c) (padWire witnessBits k t)

def padProgram (p : WitnessVerifierProgram) (k : ℕ) : WitnessVerifierProgram where
  witnessBits := p.witnessBits + k
  inputBits := p.inputBits
  ancillaBits := p.ancillaBits
  outputWire := padWire p.witnessBits k p.outputWire
  instructions := p.instructions.map fun
    | .fixed gate => .fixed (padFiniteCode p.witnessBits k gate)
    | .oracle addresses target => .oracle (addresses.map (padWire p.witnessBits k))
        (padWire p.witnessBits k target)

noncomputable def extendWitnessDensity {m : ℕ}
    (σ : Matrix (Reg m) (Reg m) ℂ) (k : ℕ) :
    Matrix (Reg (m + k)) (Reg (m + k)) ℂ :=
  Matrix.of fun u u' =>
    if (∀ j : Fin k, u (Fin.natAdd m j) = false) ∧
        (∀ j : Fin k, u' (Fin.natAdd m j) = false) then
      σ (fun i => u (Fin.castAdd k i)) (fun i => u' (Fin.castAdd k i))
    else 0

def padClassicalWitness {m : ℕ} (w : Reg m) (k : ℕ) : Reg (m + k) :=
  fun i => if h : i.val < m then w ⟨i.val, h⟩ else false

private def immediateHaltMachine :
    Turing.TM0.Machine (Option Bool) (Fin 1) := fun _ _ => none

def zeroVerifierFamily : WitnessVerifierFamily where
  controlBound := 0
  machine := immediateHaltMachine
  timeCoefficient := 0
  timeDegree := 1
  programCoefficient := 1
  programDegree := 1

open Qatlib.Concepts.QmaCompleteness.HistoryHam in
open Qatlib.Concepts.QmaCompleteness.WitnessSampler in
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 in

def fromUniformVerifierProgram
    (p : UniformVerifierProgram) : WitnessVerifierProgram where
  witnessBits := p.witnessBits
  inputBits := 0
  ancillaBits := p.qubits - p.witnessBits
  outputWire := p.outputWire
  instructions := p.instructions.map fun
    | .fixed gate => .fixed gate
    | .queryS addresses target => .oracle addresses target
    | .queryU addresses target => .oracle addresses target

end Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
