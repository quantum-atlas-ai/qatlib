/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
import Qatlib.Concepts.WalshMoment.Forrelation.SpectralLanguage
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib
open Matrix

set_option autoImplicit false

inductive UniformVerifierInstruction where
  | fixed (gate : FiniteGateCode)
  | queryS (addresses : List ℕ) (target : ℕ)
  | queryU (addresses : List ℕ) (target : ℕ)
  deriving DecidableEq, Repr

structure UniformVerifierProgram where
  qubits : ℕ
  witnessBits : ℕ
  outputWire : ℕ
  instructions : List UniformVerifierInstruction
  deriving DecidableEq, Repr

private def parseUnaryField : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseUnaryField rest).map fun (k, tail) => (k + 1, tail)

private def parseNatField (bits : List Bool) : Option (ℕ × List Bool) :=
  parseUnaryField bits

private def parseTwoNatFields (bits : List Bool) : Option (ℕ × ℕ × List Bool) := do
  let (a, rest) ← parseNatField bits
  let (b, tail) ← parseNatField rest
  pure (a, b, tail)

private def parseManyNatFields : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← parseNatField bits
      let (tail, finalBits) ← parseManyNatFields count rest
      pure (head :: tail, finalBits)

private def parseInstructionFields (tag : ℕ) (bits : List Bool) :
    Option (UniformVerifierInstruction × List Bool) := do
  if tag = 0 then
    let (w, rest) ← parseNatField bits
    pure (.fixed (.h w), rest)
  else if tag = 1 then
    let (w, rest) ← parseNatField bits
    pure (.fixed (.x w), rest)
  else if tag = 2 then
    let (w, rest) ← parseNatField bits
    pure (.fixed (.t w), rest)
  else if tag = 3 then
    let (w, rest) ← parseNatField bits
    pure (.fixed (.tdg w), rest)
  else if tag = 4 then
    let (c, t, rest) ← parseTwoNatFields bits
    pure (.fixed (.cx c t), rest)
  else if tag = 5 then
    let (count, rest) ← parseNatField bits
    let (addresses, rest') ← parseManyNatFields count rest
    let (target, tail) ← parseNatField rest'
    pure (.queryS addresses target, tail)
  else if tag = 6 then
    let (count, rest) ← parseNatField bits
    let (addresses, rest') ← parseManyNatFields count rest
    let (target, tail) ← parseNatField rest'
    pure (.queryU addresses target, tail)
  else
    none

private def parseInstructionListFuel : ℕ → List Bool → Option (List UniformVerifierInstruction)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, bits => do
      let (tag, rest) ← parseNatField bits
      let (instruction, tail) ← parseInstructionFields tag rest
      let instructions ← parseInstructionListFuel fuel tail
      pure (instruction :: instructions)

def decodeUniformVerifierProgram (bits : List Bool) : Option UniformVerifierProgram := do
  if bits.all id then
    pure ⟨bits.length + 1, 0, 0, []⟩
  else
    let (qubits, rest) ← parseNatField bits
    let (witnessBits, rest') ← parseNatField rest
    let (outputWire, instructionsBits) ← parseNatField rest'
    let instructions ← parseInstructionListFuel instructionsBits.length instructionsBits
    pure ⟨qubits, witnessBits, outputWire, instructions⟩

private theorem decodeUnaryZeroProgram (n : ℕ) :
    decodeUniformVerifierProgram (List.replicate n true) =
      some ⟨n + 1, 0, 0, []⟩ := by
  induction n with
  | zero => simp [decodeUniformVerifierProgram]
  | succ n ih => simp [decodeUniformVerifierProgram]

private def queryDescriptionLegal (q : ℕ) (addresses : List ℕ) (target : ℕ) : Prop :=
  target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup

def uniformProgramLegal (p : UniformVerifierProgram) : Prop :=
  p.witnessBits ≤ p.qubits ∧ p.outputWire < p.qubits ∧
    ∀ instruction ∈ p.instructions,
      match instruction with
      | .fixed gate => finiteCodeLegal p.qubits gate = true
      | .queryS addresses target | .queryU addresses target =>
          queryDescriptionLegal p.qubits addresses target

private def readQueryAddress {q : ℕ} (x : Reg q) (addresses : List ℕ)
    (haddr : ∀ a ∈ addresses, a < q) : Reg addresses.length :=
  fun i => x ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩

private theorem readQueryAddress_update {q : ℕ} (x : Reg q) (addresses : List ℕ)
    (target : ℕ) (htarget : target < q) (haddr : ∀ a ∈ addresses, a < q)
    (hdisjoint : target ∉ addresses) (b : Bool) :
    readQueryAddress (Function.update x ⟨target, htarget⟩ b) addresses haddr =
      readQueryAddress x addresses haddr := by
  funext i
  have hne : addresses.get i ≠ target := by
    intro he
    subst target
    exact hdisjoint (List.get_mem addresses i)
  have hneFin : (⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩ : Fin q) ≠
      ⟨target, htarget⟩ := by
    intro he
    apply hne
    exact congrArg Fin.val he
  change Function.update x ⟨target, htarget⟩ b
    ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩ =
      x ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩
  rw [Function.update_of_ne hneFin]

private def queryAddressUpdate {q : ℕ} (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (htarget : target < q)
    (haddr : ∀ a ∈ addresses, a < q) :
    Reg q → Reg q := fun x =>
      Function.update x ⟨target, htarget⟩
        (x ⟨target, htarget⟩ ^^ oracle addresses.length
          (readQueryAddress x addresses haddr))

private theorem queryAddressUpdate_involutive {q : ℕ}
    (oracle : ∀ ell, Reg ell → Bool) (addresses : List ℕ) (target : ℕ)
    (htarget : target < q) (haddr : ∀ a ∈ addresses, a < q)
    (hdisjoint : target ∉ addresses) : Function.Involutive
      (queryAddressUpdate oracle addresses target htarget haddr) := by
  intro x
  funext i
  by_cases hi : i = ⟨target, htarget⟩
  · subst i
    simp only [queryAddressUpdate, Function.update_self]
    rw [readQueryAddress_update x addresses target htarget haddr hdisjoint
      (x ⟨target, htarget⟩ ^^ oracle addresses.length (readQueryAddress x addresses haddr))]
    simp
  · simp [queryAddressUpdate, Function.update, hi]

private noncomputable def validQueryMatrix {q : ℕ} (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (htarget : target < q)
    (haddr : ∀ a ∈ addresses, a < q) :
    Matrix (Reg q) (Reg q) ℂ :=
  permMatrix (queryAddressUpdate oracle addresses target htarget haddr)

private theorem validQueryMatrix_unitary {q : ℕ} (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (htarget : target < q)
    (haddr : ∀ a ∈ addresses, a < q) (hdisjoint : target ∉ addresses) :
    validQueryMatrix oracle addresses target htarget haddr ∈
      Matrix.unitaryGroup (Reg q) ℂ :=
  permMatrix_unitary
    (queryAddressUpdate_involutive oracle addresses target htarget haddr hdisjoint)

private noncomputable def uniformQueryMatrix (q : ℕ) (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) : Matrix (Reg q) (Reg q) ℂ := by
  classical
  exact if h : queryDescriptionLegal q addresses target then
    validQueryMatrix oracle addresses target h.1 h.2.1
  else 1

private theorem uniformQueryMatrix_unitary (q : ℕ) (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (h : queryDescriptionLegal q addresses target) :
    uniformQueryMatrix q oracle addresses target ∈ Matrix.unitaryGroup (Reg q) ℂ := by
  classical
  simp only [uniformQueryMatrix, dif_pos h]
  exact validQueryMatrix_unitary oracle addresses target h.1 h.2.1 h.2.2.1

private noncomputable def uniformInstructionMatrix (q : ℕ)
    (S U : ∀ ell, Reg ell → Bool) : UniformVerifierInstruction →
      Matrix (Reg q) (Reg q) ℂ
  | .fixed gate => finiteCodeMatrix q gate
  | .queryS addresses target => uniformQueryMatrix q S addresses target
  | .queryU addresses target => uniformQueryMatrix q U addresses target

private theorem uniformInstructionMatrix_unitary (q : ℕ)
    (S U : ∀ ell, Reg ell → Bool) (instruction : UniformVerifierInstruction)
    (hlegal : match instruction with
      | .fixed gate => finiteCodeLegal q gate = true
      | .queryS addresses target | .queryU addresses target =>
          queryDescriptionLegal q addresses target) :
    uniformInstructionMatrix q S U instruction ∈ Matrix.unitaryGroup (Reg q) ℂ := by
  cases instruction with
  | fixed gate => exact finiteCodeMatrix_unitary q gate hlegal
  | queryS addresses target => exact uniformQueryMatrix_unitary q S addresses target hlegal
  | queryU addresses target => exact uniformQueryMatrix_unitary q U addresses target hlegal

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

structure UniformVerifierGenerator where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ
  programCoefficient : ℕ
  programDegree : ℕ

private def unaryInput (n : ℕ) : List (Option Bool) :=
  List.replicate n (some true)

def uniformPolynomialBound (c d n : ℕ) : ℕ := c * (n + 1) ^ d

private def generatorFuel (g : UniformVerifierGenerator) (n : ℕ) : ℕ :=
  uniformPolynomialBound g.timeCoefficient g.timeDegree n

private def generatorProgramBound (g : UniformVerifierGenerator) (n : ℕ) : ℕ :=
  uniformPolynomialBound g.programCoefficient g.programDegree n

private def generatorHaltsInFuel (g : UniformVerifierGenerator) (n : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ generatorFuel g n ∧
    BitMachineHaltsAt g.machine (unaryInput n) t

def uniformGeneratedProgramAt (g : UniformVerifierGenerator) (n : ℕ) :
    Option UniformVerifierProgram :=
  (runUntilHaltWithin g.machine (generatorFuel g n)
    (Turing.TM0.init (unaryInput n))).bind fun cfg =>
      (readOutputUntilBlank (n + generatorFuel g n + 1) cfg.Tape.right₀).bind
        decodeUniformVerifierProgram

def uniformGeneratorValid (g : UniformVerifierGenerator) : Prop :=
  ∀ n : ℕ, ∃ p : UniformVerifierProgram,
    uniformGeneratedProgramAt g n = some p ∧
      generatorHaltsInFuel g n ∧
      p.qubits ≤ generatorProgramBound g n ∧
      p.instructions.length ≤ generatorProgramBound g n ∧
      uniformProgramLegal p

private def zeroPaddedClassicalWitness (q witnessBits : ℕ)
    (w : Fin witnessBits → Bool) : Reg q := fun i =>
  if h : i.val < witnessBits then w ⟨i.val, h⟩ else false

private def auxiliaryZeroSupported (q witnessBits : ℕ) (ψ : QState (Reg q)) : Prop :=
  ∀ x : Reg q,
    (∃ i : Fin q, witnessBits ≤ i.val ∧ x i = true) → ψ x = 0

private def outputTrueEvent (q outputWire : ℕ) (hout : outputWire < q) :
    Finset (Reg q) :=
  Finset.univ.filter fun x => x ⟨outputWire, hout⟩ = true

def uniformProgramOutputEvent (p : UniformVerifierProgram) : Finset (Reg p.qubits) :=
  if h : p.outputWire < p.qubits then
    outputTrueEvent p.qubits p.outputWire h
  else ∅

private noncomputable def runUniformInstructions (S U : ∀ ell, Reg ell → Bool)
    (q : ℕ) : List UniformVerifierInstruction → QState (Reg q) → QState (Reg q)
  | [], ψ => ψ
  | instruction :: rest, ψ =>
      runUniformInstructions S U q rest
        (ApplyGate (uniformInstructionMatrix q S U instruction) ψ)

noncomputable def uniformVerifierRun (S U : ∀ ell, Reg ell → Bool)
    (p : UniformVerifierProgram) (ψ : QState (Reg p.qubits)) : QState (Reg p.qubits) :=
  runUniformInstructions S U p.qubits p.instructions ψ

theorem uniformVerifierRun_normalized (S U : ∀ ell, Reg ell → Bool)
    (p : UniformVerifierProgram) (hp : uniformProgramLegal p)
    (ψ : QState (Reg p.qubits)) (hψ : Normalized ψ) :
    Normalized (uniformVerifierRun S U p ψ) := by
  let valid : UniformVerifierInstruction → Prop := fun instruction =>
    match instruction with
    | .fixed gate => finiteCodeLegal p.qubits gate = true
    | .queryS addresses target | .queryU addresses target =>
        queryDescriptionLegal p.qubits addresses target
  have go : ∀ C : List UniformVerifierInstruction,
      (∀ instruction ∈ C, valid instruction) →
      ∀ φ : QState (Reg p.qubits), Normalized φ →
        Normalized (runUniformInstructions S U p.qubits C φ) := by
    intro C
    induction C with
    | nil => intro _ φ hφ; exact hφ
    | cons instruction rest ih =>
        intro hC φ hφ
        have hrest : ∀ step ∈ rest, valid step := by
          intro step hstep
          exact hC step (List.mem_cons_of_mem instruction hstep)
        exact ih hrest _ (normalized_applyGate
          (uniformInstructionMatrix_unitary p.qubits S U instruction
            (hC instruction (List.mem_cons_self))) hφ)
  exact go p.instructions hp.2.2 ψ hψ

def InUniformQMASpectral (S U : ∀ ell, Reg ell → Bool) : Prop :=
  ∃ g : UniformVerifierGenerator, uniformGeneratorValid g ∧
    ∀ n : ℕ, ∃ p : UniformVerifierProgram,
      uniformGeneratedProgramAt g n = some p ∧
      uniformProgramLegal p ∧
      (spectralLangMem S U n →
        ∃ ψ : QState (Reg p.qubits), Normalized ψ ∧
          auxiliaryZeroSupported p.qubits p.witnessBits ψ ∧
          2 / 3 ≤ MeasureProb (uniformVerifierRun S U p ψ)
            (uniformProgramOutputEvent p)) ∧
      (¬ spectralLangMem S U n →
        ∀ ψ : QState (Reg p.qubits), Normalized ψ →
          auxiliaryZeroSupported p.qubits p.witnessBits ψ →
          MeasureProb (uniformVerifierRun S U p ψ)
            (uniformProgramOutputEvent p) ≤ 1 / 3)

def OutUniformQCMASpectral (S U : ∀ ell, Reg ell → Bool) : Prop :=
  ∀ g : UniformVerifierGenerator, uniformGeneratorValid g →
    ∃ n : ℕ, ∃ p : UniformVerifierProgram,
      uniformGeneratedProgramAt g n = some p ∧
      uniformProgramLegal p ∧
      ((spectralLangMem S U n →
          ∀ w : Fin p.witnessBits → Bool,
            MeasureProb
              (uniformVerifierRun S U p
                (Qatlib.Foundations.PureStateMath.Ket (zeroPaddedClassicalWitness p.qubits p.witnessBits w)))
              (uniformProgramOutputEvent p) < 2 / 3) ∧
        (¬ spectralLangMem S U n →
          ∃ w : Fin p.witnessBits → Bool,
            1 / 3 < MeasureProb
              (uniformVerifierRun S U p
                (Qatlib.Foundations.PureStateMath.Ket (zeroPaddedClassicalWitness p.qubits p.witnessBits w)))
              (uniformProgramOutputEvent p)))

private def immediateHaltMachine :
    Turing.TM0.Machine (Option Bool) (Fin 1) := fun _ _ => none

def zeroInstructionGenerator : UniformVerifierGenerator where
  controlBound := 0
  machine := immediateHaltMachine
  timeCoefficient := 0
  timeDegree := 1
  programCoefficient := 1
  programDegree := 1

private theorem readOutputUnaryList (n : ℕ) :
    readOutputUntilBlank (n + 1)
      (Turing.ListBlank.mk (unaryInput n)) =
        some (List.replicate n true) := by
  induction n with
  | zero => simp [readOutputUntilBlank, unaryInput]; rfl
  | succ n ih =>
      change readOutputUntilBlank (n + 1 + 1)
        (Turing.ListBlank.mk (some true :: List.replicate n (some true))) = _
      change readOutputUntilBlank (n + 1)
        (Turing.ListBlank.mk (List.replicate n (some true))) = _ at ih
      rw [readOutputUntilBlank]
      have hhead :
          (Turing.ListBlank.mk (some true :: List.replicate n (some true))).nth 0 = some true := by
        simp
      rw [hhead]
      rw [show (Turing.ListBlank.mk (some true :: List.replicate n (some true))).tail =
          Turing.ListBlank.mk (List.replicate n (some true)) by
        simp [Turing.ListBlank.tail_mk]]
      rw [ih]
      rfl

private theorem readOutputUnaryInput (n : ℕ) :
    readOutputUntilBlank (n + 1)
      (Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (unaryInput n)).Tape.right₀ =
        some (List.replicate n true) := by
  simpa only [Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂,
    Turing.Tape.mk'_right₀] using readOutputUnaryList n

theorem zeroInstructionGenerator_program (n : ℕ) :
    uniformGeneratedProgramAt zeroInstructionGenerator n =
      some ⟨n + 1, 0, 0, []⟩ := by
  unfold uniformGeneratedProgramAt
  dsimp [zeroInstructionGenerator, generatorFuel, uniformPolynomialBound]
  simp only [Nat.zero_mul, Nat.add_zero]
  change ((runUntilHaltWithin immediateHaltMachine 0
    (Turing.TM0.init (unaryInput n))).bind fun cfg =>
      (readOutputUntilBlank (n + 1) cfg.Tape.right₀).bind
        decodeUniformVerifierProgram) = some ⟨n + 1, 0, 0, []⟩
  simp only [runUntilHaltWithin, Turing.TM0.step, immediateHaltMachine,
    Option.map_none, if_true]
  simp only [Option.bind_some]
  change (readOutputUntilBlank (n + 1)
    (Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (unaryInput n)).Tape.right₀).bind
      decodeUniformVerifierProgram = some ⟨n + 1, 0, 0, []⟩
  rw [readOutputUnaryInput]
  simp only [Option.bind_some]
  rw [decodeUnaryZeroProgram]

theorem zeroInstructionGenerator_valid : uniformGeneratorValid zeroInstructionGenerator := by
  intro n
  let p : UniformVerifierProgram := ⟨n + 1, 0, 0, []⟩
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · exact zeroInstructionGenerator_program n
  · refine ⟨0, ?_⟩
    constructor
    · simp [generatorFuel, zeroInstructionGenerator, uniformPolynomialBound]
    · change BitMachineHaltsAt immediateHaltMachine (unaryInput n) 0
      exact ⟨Turing.TM0.init (unaryInput n), rfl,
        by simp [Turing.TM0.step, immediateHaltMachine]⟩
  · change n + 1 ≤ 1 * (n + 1) ^ 1
    simp
  · change 0 ≤ 1 * (n + 1) ^ 1
    simp
  · simp [uniformProgramLegal, p]

theorem zeroInstructionGenerator_rejects (S U : ∀ ell, Reg ell → Bool) (n : ℕ)
    (w : Fin 0 → Bool) :
    MeasureProb (uniformVerifierRun S U ⟨n + 1, 0, 0, []⟩
      (Qatlib.Foundations.PureStateMath.Ket (zeroPaddedClassicalWitness (n + 1) 0 w)))
      (uniformProgramOutputEvent ⟨n + 1, 0, 0, []⟩) = 0 := by
  classical
  simp only [uniformVerifierRun, runUniformInstructions]
  unfold MeasureProb
  apply Finset.sum_eq_zero
  intro a ha
  have hatrue : a 0 = true := by
    simpa [uniformProgramOutputEvent, outputTrueEvent] using ha
  have hne : a ≠ zeroPaddedClassicalWitness (n + 1) 0 w := by
    intro he
    have hbit := congrArg (fun x : Reg (n + 1) => x 0) he
    change a 0 = zeroPaddedClassicalWitness (n + 1) 0 w 0 at hbit
    rw [hatrue] at hbit
    simp [zeroPaddedClassicalWitness] at hbit
  simp [BornProb, Qatlib.Foundations.PureStateMath.Ket, hne]

theorem not_outUniform_of_no_yes_lengths (S U : ∀ ell, Reg ell → Bool)
    (hno : ∀ n, ¬ spectralLangMem S U n) : ¬ OutUniformQCMASpectral S U := by
  intro hout
  obtain ⟨n, p, hp, _, _, hbad⟩ := hout zeroInstructionGenerator zeroInstructionGenerator_valid
  have heq := zeroInstructionGenerator_program n
  rw [heq] at hp
  cases Option.some.inj hp
  obtain ⟨w, hw⟩ := hbad (hno n)
  rw [zeroInstructionGenerator_rejects S U n w] at hw
  norm_num at hw

end Qatlib.Concepts.WalshMoment.Forrelation
