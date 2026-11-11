/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
import Qatlib.Concepts.WalshMoment.Forrelation.SpectralLanguage

/-!
# Uniform oracle verifier programs and generators

`UniformVerifierInstruction` and `UniformVerifierProgram` describe finite gate programs with two
Boolean oracles. The decoder, legality predicates, and unitary instruction semantics feed
`uniformVerifierRun`. `UniformVerifierGenerator` uses a finite-control Turing machine with
polynomial time and program bounds, and `InUniformQMASpectral` and `OutUniformQCMASpectral`
state the corresponding quantum witness verification and classical witness obstruction
properties. `zeroInstructionGenerator` supplies a valid rejecting generator and proves
`not_outUniform_of_no_yes_lengths`.

Uniform quantum computation is treated in [Bernstein and Vazirani, 1997][BernsteinVazirani1997],
while quantum proof verification is discussed in [MarriottWatrous2005].

## References

- [Marriott and Watrous, 2005][MarriottWatrous2005].
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib
open Matrix

set_option autoImplicit false

/-- A verifier instruction consisting of a finite gate code or a query to one of the two Boolean
oracles using a list of address wires and a target wire. -/
inductive UniformVerifierInstruction where
  | fixed (gate : FiniteGateCode)
  | queryS (addresses : List ℕ) (target : ℕ)
  | queryU (addresses : List ℕ) (target : ℕ)
  deriving DecidableEq, Repr

/-- A finite verifier program recording its number of qubits, number of witness bits, output
wire, and instruction list. -/
structure UniformVerifierProgram where
  qubits : ℕ
  witnessBits : ℕ
  outputWire : ℕ
  instructions : List UniformVerifierInstruction
  deriving DecidableEq, Repr

/-- Parses a run of true bits terminated by a false bit as a natural number, returning the
unconsumed suffix. It fails if the terminating false bit is absent. -/
private def parseUnaryField : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseUnaryField rest).map fun (k, tail) => (k + 1, tail)

/-- Parses a natural number using the unary field encoding of `parseUnaryField`. -/
private def parseNatField (bits : List Bool) : Option (ℕ × List Bool) :=
  parseUnaryField bits

/-- Parses two consecutive unary natural number fields and returns both values with the
remaining bits. -/
private def parseTwoNatFields (bits : List Bool) : Option (ℕ × ℕ × List Bool) := do
  let (a, rest) ← parseNatField bits
  let (b, tail) ← parseNatField rest
  pure (a, b, tail)

/-- Parses the specified number of consecutive natural number fields, returning their values in
order and the remaining bits. -/
private def parseManyNatFields : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← parseNatField bits
      let (tail, finalBits) ← parseManyNatFields count rest
      pure (head :: tail, finalBits)

/-- Decodes the fields of an instruction from its tag: zero through four encode H, X, T, inverse
T, and controlled X, while five and six encode oracle queries. Unrecognized tags or
incomplete fields produce failure. -/
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

/-- Parses an instruction list with at most the supplied number of instructions, requiring the
input to be exhausted when the fuel runs out. -/
private def parseInstructionListFuel : ℕ → List Bool → Option (List UniformVerifierInstruction)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, bits => do
      let (tag, rest) ← parseNatField bits
      let (instruction, tail) ← parseInstructionFields tag rest
      let instructions ← parseInstructionListFuel fuel tail
      pure (instruction :: instructions)

/-- Decodes a verifier program from unary header fields and encoded instructions. A list
containing only true bits instead encodes an empty program with one more qubit than the list
length, no witness bits, and output wire zero. -/
def decodeUniformVerifierProgram (bits : List Bool) : Option UniformVerifierProgram := do
  if bits.all id then
    pure ⟨bits.length + 1, 0, 0, []⟩
  else
    let (qubits, rest) ← parseNatField bits
    let (witnessBits, rest') ← parseNatField rest
    let (outputWire, instructionsBits) ← parseNatField rest'
    let instructions ← parseInstructionListFuel instructionsBits.length instructionsBits
    pure ⟨qubits, witnessBits, outputWire, instructions⟩

/-- A list of `n` true bits decodes to the program with `n + 1` qubits, no witness bits, output
wire zero, and no instructions. -/
private theorem decodeUnaryZeroProgram (n : ℕ) :
    decodeUniformVerifierProgram (List.replicate n true) =
      some ⟨n + 1, 0, 0, []⟩ := by
  induction n with
  | zero => simp [decodeUniformVerifierProgram]
  | succ n ih => simp [decodeUniformVerifierProgram]

/-- A query description is legal when all wires are in range, the target is absent from the
address list, and the address list has no duplicates. -/
private def queryDescriptionLegal (q : ℕ) (addresses : List ℕ) (target : ℕ) : Prop :=
  target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup

/-- A program is legal when its witness fits in its register, its output wire is in range, and
every fixed gate or oracle query has a legal wire description. -/
def uniformProgramLegal (p : UniformVerifierProgram) : Prop :=
  p.witnessBits ≤ p.qubits ∧ p.outputWire < p.qubits ∧
    ∀ instruction ∈ p.instructions,
      match instruction with
      | .fixed gate => finiteCodeLegal p.qubits gate = true
      | .queryS addresses target | .queryU addresses target =>
          queryDescriptionLegal p.qubits addresses target

/-- Extracts the register bits at the listed address wires in list order, using the supplied
range proofs. -/
private def readQueryAddress {q : ℕ} (x : Reg q) (addresses : List ℕ)
    (haddr : ∀ a ∈ addresses, a < q) : Reg addresses.length :=
  fun i => x ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩

/-- Updating a target wire outside the address list leaves the extracted query address
unchanged. -/
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

/-- Updates the target bit by exclusive-or with the oracle value on the extracted address,
leaving all other register bits unchanged. -/
private def queryAddressUpdate {q : ℕ} (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (htarget : target < q)
    (haddr : ∀ a ∈ addresses, a < q) :
    Reg q → Reg q := fun x =>
      Function.update x ⟨target, htarget⟩
        (x ⟨target, htarget⟩ ^^ oracle addresses.length
          (readQueryAddress x addresses haddr))

/-- The oracle target update is an involution when the target is absent from the address list. -/
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

/-- The matrix `permMatrix` associated with the oracle target update on registers, assuming the
address and target wires are in range. -/
private noncomputable def validQueryMatrix {q : ℕ} (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (htarget : target < q)
    (haddr : ∀ a ∈ addresses, a < q) :
    Matrix (Reg q) (Reg q) ℂ :=
  permMatrix (queryAddressUpdate oracle addresses target htarget haddr)

/-- The oracle update matrix is unitary when the target is absent from the address list and all
referenced wires are in range. -/
private theorem validQueryMatrix_unitary {q : ℕ} (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (htarget : target < q)
    (haddr : ∀ a ∈ addresses, a < q) (hdisjoint : target ∉ addresses) :
    validQueryMatrix oracle addresses target htarget haddr ∈
      Matrix.unitaryGroup (Reg q) ℂ :=
  permMatrix_unitary
    (queryAddressUpdate_involutive oracle addresses target htarget haddr hdisjoint)

/-- The oracle query matrix for a legal query description, with the identity matrix used for an
illegal description. -/
private noncomputable def uniformQueryMatrix (q : ℕ) (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) : Matrix (Reg q) (Reg q) ℂ := by
  classical
  exact if h : queryDescriptionLegal q addresses target then
    validQueryMatrix oracle addresses target h.1 h.2.1
  else 1

/-- A uniform oracle query matrix is unitary whenever its query description is legal. -/
private theorem uniformQueryMatrix_unitary (q : ℕ) (oracle : ∀ ell, Reg ell → Bool)
    (addresses : List ℕ) (target : ℕ) (h : queryDescriptionLegal q addresses target) :
    uniformQueryMatrix q oracle addresses target ∈ Matrix.unitaryGroup (Reg q) ℂ := by
  classical
  simp only [uniformQueryMatrix, dif_pos h]
  exact validQueryMatrix_unitary oracle addresses target h.1 h.2.1 h.2.2.1

/-- Interprets a verifier instruction as its fixed gate matrix or as the query matrix for oracle
`S` or `U`. -/
private noncomputable def uniformInstructionMatrix (q : ℕ)
    (S U : ∀ ell, Reg ell → Bool) : UniformVerifierInstruction →
      Matrix (Reg q) (Reg q) ℂ
  | .fixed gate => finiteCodeMatrix q gate
  | .queryS addresses target => uniformQueryMatrix q S addresses target
  | .queryU addresses target => uniformQueryMatrix q U addresses target

/-- Every instruction satisfying its corresponding legality condition has a unitary matrix
interpretation. -/
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

/-- Runs a Turing machine from a configuration for at most the supplied number of transitions,
returning the halted configuration if one is reached. It also checks for halting when the
fuel is zero. -/
private def runUntilHaltWithin {k : ℕ}
    (machine : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) :
    ℕ → Turing.TM0.Cfg (Option Bool) (Fin (k + 1)) →
      Option (Turing.TM0.Cfg (Option Bool) (Fin (k + 1)))
  | 0, cfg => if Turing.TM0.step machine cfg = none then some cfg else none
  | fuel + 1, cfg =>
      match Turing.TM0.step machine cfg with
      | none => some cfg
      | some next => runUntilHaltWithin machine fuel next

/-- Reads Boolean symbols from a tape until the first blank, returning failure if more symbols
remain after the supplied fuel is exhausted. -/
private def readOutputUntilBlank : ℕ → Turing.ListBlank (Option Bool) → Option (List Bool)
  | 0, tape => if tape.nth 0 = none then some [] else none
  | fuel + 1, tape =>
      match tape.nth 0 with
      | none => some []
      | some bit => (readOutputUntilBlank fuel tape.tail).map (bit :: ·)

/-- A finite-control Turing machine together with coefficients and degrees for polynomial bounds
on its running time and generated program resources. -/
structure UniformVerifierGenerator where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ
  programCoefficient : ℕ
  programDegree : ℕ

/-- The Turing machine input consisting of `n` copies of the nonblank true symbol. -/
private def unaryInput (n : ℕ) : List (Option Bool) :=
  List.replicate n (some true)

/-- The natural number polynomial resource bound `c * (n + 1) ^ d`. -/
def uniformPolynomialBound (c d n : ℕ) : ℕ := c * (n + 1) ^ d

/-- The generator's polynomial time allowance at input length `n`. -/
private def generatorFuel (g : UniformVerifierGenerator) (n : ℕ) : ℕ :=
  uniformPolynomialBound g.timeCoefficient g.timeDegree n

/-- The generator's polynomial bound on qubit count and instruction count at input length `n`. -/
private def generatorProgramBound (g : UniformVerifierGenerator) (n : ℕ) : ℕ :=
  uniformPolynomialBound g.programCoefficient g.programDegree n

/-- The generator's machine halts on unary input `n` at some time no greater than its time
allowance. -/
private def generatorHaltsInFuel (g : UniformVerifierGenerator) (n : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ generatorFuel g n ∧
    BitMachineHaltsAt g.machine (unaryInput n) t

/-- Runs the generator within its time allowance, reads a blank-terminated output of length at
most `n + generatorFuel g n + 1`, and decodes that output as a verifier program. Any failed
stage returns `none`. -/
def uniformGeneratedProgramAt (g : UniformVerifierGenerator) (n : ℕ) :
    Option UniformVerifierProgram :=
  (runUntilHaltWithin g.machine (generatorFuel g n)
    (Turing.TM0.init (unaryInput n))).bind fun cfg =>
      (readOutputUntilBlank (n + generatorFuel g n + 1) cfg.Tape.right₀).bind
        decodeUniformVerifierProgram

/-- At every input length, the generator halts within its time bound and produces a legal
program whose qubit count and instruction count satisfy its program bound. -/
def uniformGeneratorValid (g : UniformVerifierGenerator) : Prop :=
  ∀ n : ℕ, ∃ p : UniformVerifierProgram,
    uniformGeneratedProgramAt g n = some p ∧
      generatorHaltsInFuel g n ∧
      p.qubits ≤ generatorProgramBound g n ∧
      p.instructions.length ≤ generatorProgramBound g n ∧
      uniformProgramLegal p

/-- Embeds the available witness bits into the initial wires of a register and sets every later
wire to false. -/
private def zeroPaddedClassicalWitness (q witnessBits : ℕ)
    (w : Fin witnessBits → Bool) : Reg q := fun i =>
  if h : i.val < witnessBits then w ⟨i.val, h⟩ else false

/-- A state has zero amplitude on every basis register containing a true bit outside the witness
wires. -/
private def auxiliaryZeroSupported (q witnessBits : ℕ) (ψ : QState (Reg q)) : Prop :=
  ∀ x : Reg q,
    (∃ i : Fin q, witnessBits ≤ i.val ∧ x i = true) → ψ x = 0

/-- The finite event of basis registers whose designated in-range output wire is true. -/
private def outputTrueEvent (q outputWire : ℕ) (hout : outputWire < q) :
    Finset (Reg q) :=
  Finset.univ.filter fun x => x ⟨outputWire, hout⟩ = true

/-- The program's event that its output wire is true, or the empty event if that wire is out of
range. -/
def uniformProgramOutputEvent (p : UniformVerifierProgram) : Finset (Reg p.qubits) :=
  if h : p.outputWire < p.qubits then
    outputTrueEvent p.qubits p.outputWire h
  else ∅

/-- Applies the interpreted instruction matrices to a state in list order. -/
private noncomputable def runUniformInstructions (S U : ∀ ell, Reg ell → Bool)
    (q : ℕ) : List UniformVerifierInstruction → QState (Reg q) → QState (Reg q)
  | [], ψ => ψ
  | instruction :: rest, ψ =>
      runUniformInstructions S U q rest
        (ApplyGate (uniformInstructionMatrix q S U instruction) ψ)

/-- The final state obtained by executing a verifier program's instruction list with oracles `S`
and `U`. -/
noncomputable def uniformVerifierRun (S U : ∀ ell, Reg ell → Bool)
    (p : UniformVerifierProgram) (ψ : QState (Reg p.qubits)) : QState (Reg p.qubits) :=
  runUniformInstructions S U p.qubits p.instructions ψ

/-- Running a legal verifier program preserves normalization of the input state. -/
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

/-- A valid uniform generator provides legal verifiers that accept some normalized quantum
witness with zero auxiliary wires with probability at least `2 / 3` at every spectral
language member. At every nonmember, all such witnesses are accepted with probability at
most `1 / 3`. -/
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

/-- Every valid uniform generator has a length at which its generated verifier fails the
classical witness acceptance conditions. At a member all zero-padded classical witnesses
have acceptance probability below `2 / 3`, while at a nonmember some such witness has
acceptance probability above `1 / 3`. -/
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

/-- The one-control-state Turing machine that halts immediately for every scanned symbol. -/
private def immediateHaltMachine :
    Turing.TM0.Machine (Option Bool) (Fin 1) := fun _ _ => none

/-- The immediately halting generator with zero time allowance and program bound `n + 1`, whose
unchanged unary input decodes as a program with no instructions. -/
def zeroInstructionGenerator : UniformVerifierGenerator where
  controlBound := 0
  machine := immediateHaltMachine
  timeCoefficient := 0
  timeDegree := 1
  programCoefficient := 1
  programDegree := 1

/-- Reading the tape made from unary input `n` with fuel `n + 1` returns exactly `n` true bits. -/
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

/-- Reading the right tape of the initial unary input configuration with fuel `n + 1` returns
exactly `n` true bits. -/
private theorem readOutputUnaryInput (n : ℕ) :
    readOutputUntilBlank (n + 1)
      (Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (unaryInput n)).Tape.right₀ =
        some (List.replicate n true) := by
  simpa only [Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂,
    Turing.Tape.mk'_right₀] using readOutputUnaryList n

/-- At length `n`, the zero-instruction generator produces the program with `n + 1` qubits, no
witness bits, output wire zero, and no instructions. -/
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

/-- The zero-instruction generator satisfies all uniform generator validity requirements. -/
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

/-- The empty program produced by the zero-instruction generator has acceptance probability zero
on its zero-padded empty classical witness, independently of both oracles. -/
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

/-- If the spectral language has no member at any length, `OutUniformQCMASpectral` is false, as
witnessed by the valid zero-instruction generator. -/
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
