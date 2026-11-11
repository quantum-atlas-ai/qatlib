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

/-!
# Witness verifier programs and finite promises

`BitstringPromise` specifies disjoint finite sets of yes and no inputs. `WitnessVerifierProgram`
combines finite gate instructions and classical-oracle XOR queries with explicit witness, input,
and ancilla registers. `verifierInputDensity` initializes a witness matrix, and `acceptProb`
evaluates its output event; `IsWitnessDensity` allows trace at most one.

`WitnessVerifierFamily` describes a Turing-machine generator with polynomial time and
program-size parameters. The predicates `InQMA`, `InQCMA`, and `InBQPWitnessModel` express
bounded-error verification within this model, with oracle-free families required even in
`InQMAWith`. See [MarriottWatrous2005] for quantum-proof background.

## Main definitions

* `witnessFamilyValid`: successful, legal generation within the polynomial size bound.
* `InQMAWith`: quantum-witness verification with completeness and soundness thresholds.
* `padProgram`: insertion of additional witness wires with consistent wire relabeling.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

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

/-- A finite promise problem given by disjoint finite sets of yes and no Boolean strings. -/
structure BitstringPromise where
  yes : Finset (List Bool)
  no : Finset (List Bool)
  disjoint : Disjoint yes no

/-- Forms a finite promise problem whose yes set is `S` and whose no set is empty. -/
def langAsPromise (S : Finset (List Bool)) : BitstringPromise where
  yes := S
  no := ∅
  disjoint := by simp

/-- A verifier instruction consisting of either a fixed finite gate code or a classical-oracle
XOR query. -/
inductive WitnessInstruction where
  | fixed (gate : FiniteGateCode)
  | oracle (addresses : List ℕ) (target : ℕ)
  deriving DecidableEq, Repr

/-- A verifier program specifying witness, input, and ancilla widths, an output wire, and a list
of instructions. -/
structure WitnessVerifierProgram where
  witnessBits : ℕ
  inputBits : ℕ
  ancillaBits : ℕ
  outputWire : ℕ
  instructions : List WitnessInstruction
  deriving DecidableEq, Repr

/-- The total number of witness, input, and ancilla qubits in a verifier program. -/
def programQubits (p : WitnessVerifierProgram) : ℕ :=
  p.witnessBits + p.inputBits + p.ancillaBits

/-- Requires a fixed gate to be legal, or an oracle query to have distinct in-range addresses
and a separate in-range target. -/
def instructionLegal (q : ℕ) : WitnessInstruction → Prop
  | .fixed gate => finiteCodeLegal q gate = true
  | .oracle addresses target =>
      target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup

/-- Requires the output wire to be in range and every instruction to be legal on the program
register. -/
def witnessProgramLegal (p : WitnessVerifierProgram) : Prop :=
  p.outputWire < programQubits p ∧
    ∀ i ∈ p.instructions, instructionLegal (programQubits p) i

/-- States that every instruction of a verifier program is a fixed gate. -/
def oracleFree (p : WitnessVerifierProgram) : Prop :=
  p.instructions.all fun
    | .fixed _ => true
    | .oracle _ _ => false

/-- The empty fallback verifier with all register widths zero and output index zero. -/
def defaultVerifierProgram : WitnessVerifierProgram where
  witnessBits := 0
  inputBits := 0
  ancillaBits := 0
  outputWire := 0
  instructions := []

/-- A Boolean oracle accepting a Boolean register of any finite width. -/
abbrev ClassicalOracle := ∀ ell : ℕ, Reg ell → Bool

/-- Extracts the register bits at the supplied in-range addresses, preserving their list order. -/
def readAddress {q : ℕ} (x : Reg q) (addresses : List ℕ)
    (haddr : ∀ a ∈ addresses, a < q) : Reg addresses.length :=
  fun i => x ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩

/-- XORs the oracle value on the selected address bits into the target wire. -/
def xorQueryUpdate (A : ClassicalOracle) {q : ℕ} (addresses : List ℕ)
    (target : ℕ) (htarget : target < q) (haddr : ∀ a ∈ addresses, a < q) :
    Reg q → Reg q := fun x =>
  Function.update x ⟨target, htarget⟩
    (x ⟨target, htarget⟩ ^^ A addresses.length (readAddress x addresses haddr))

/-- The permutation matrix of a legal XOR query, with the identity used for an illegal query
description. -/
noncomputable def xorQueryMatrix (A : ClassicalOracle) (q : ℕ)
    (addresses : List ℕ) (target : ℕ) : Matrix (Reg q) (Reg q) ℂ := by
  classical
  exact if h : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧
      addresses.Nodup then
    permMatrix (xorQueryUpdate A addresses target h.1 h.2.1)
  else 1

/-- XORs the conjunction of a control bit and the addressed oracle value into the target wire. -/
noncomputable def controlledXorUpdate (A : ClassicalOracle) {q : ℕ}
    (addresses : List ℕ) (target control : ℕ) (htarget : target < q)
    (hcontrol : control < q) (haddr : ∀ a ∈ addresses, a < q) :
    Reg q → Reg q := fun x =>
  Function.update x ⟨target, htarget⟩
    (x ⟨target, htarget⟩ ^^ (x ⟨control, hcontrol⟩ &&
      A addresses.length (readAddress x addresses haddr)))

/-- The permutation matrix of the controlled XOR update when its wire checks hold, and the
identity otherwise. -/
noncomputable def controlledXorMatrix (A : ClassicalOracle) (q : ℕ)
    (addresses : List ℕ) (target control : ℕ) : Matrix (Reg q) (Reg q) ℂ := by
  classical
  exact if h : target < q ∧ control < q ∧ control ≠ target ∧
      (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup then
    permMatrix
      (controlledXorUpdate A addresses target control h.1 h.2.1 h.2.2.2.1)
  else 1

/-- An oracle that ANDs its last input bit with the original oracle on the preceding bits,
returning false at width zero. -/
def appendedControlOracle (A : ClassicalOracle) : ClassicalOracle := fun ell r =>
  match ell with
  | 0 => false
  | ℓ + 1 => r (Fin.last _) && A ℓ (fun i => r i.castSucc)

/-- Interprets a fixed gate or an XOR oracle instruction as a matrix on the full register. -/
noncomputable def instructionMatrix (A : ClassicalOracle) (q : ℕ) :
    WitnessInstruction → Matrix (Reg q) (Reg q) ℂ
  | .fixed gate => finiteCodeMatrix q gate
  | .oracle addresses target => xorQueryMatrix A q addresses target

/-- The reversed product of instruction matrices, so the first listed instruction acts first. -/
noncomputable def programMatrix (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  (p.instructions.map (instructionMatrix A (programQubits p))).reverse.prod

/-- Applies the verifier program matrix to a full-register state. -/
noncomputable def programRun (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (ψ : QState (Reg (programQubits p))) : QState (Reg (programQubits p)) :=
  programMatrix A p *ᵥ ψ

/-- Counts the oracle instructions in a verifier program. -/
def oracleQueryCount (p : WitnessVerifierProgram) : ℕ :=
  (p.instructions.filterMap fun
    | .fixed _ => none
    | .oracle _ _ => some ()).length

/-- Sums the number of address wires used by all oracle instructions in a verifier program. -/
def addressBitLedger (p : WitnessVerifierProgram) : ℕ :=
  (p.instructions.filterMap fun
    | .fixed _ => none
    | .oracle addresses _ => some addresses.length).sum

variable (p : WitnessVerifierProgram)

/-- Embeds a witness-wire index into the initial segment of the full program register. -/
def witnessWire (i : Fin p.witnessBits) : Fin (programQubits p) :=
  ⟨i.val, by simp only [programQubits]; omega⟩

/-- Embeds an input-wire index into the register segment immediately after the witness wires. -/
def inputWire (i : Fin p.inputBits) : Fin (programQubits p) :=
  ⟨p.witnessBits + i.val, by simp only [programQubits]; omega⟩

/-- Embeds an ancilla-wire index into the register segment after the witness and input wires. -/
def ancillaWire (i : Fin p.ancillaBits) : Fin (programQubits p) :=
  ⟨p.witnessBits + p.inputBits + i.val, by simp only [programQubits]; omega⟩

/-- Restricts a full-register configuration to its witness segment. -/
def witnessRestrict (z : Reg (programQubits p)) : Reg p.witnessBits :=
  fun i => z (witnessWire p i)

/-- Restricts a full-register configuration to its classical input segment. -/
def inputRestrict (z : Reg (programQubits p)) : Reg p.inputBits :=
  fun i => z (inputWire p i)

/-- States that every ancilla wire of a full-register configuration is false. -/
def ancillaZero (z : Reg (programQubits p)) : Prop :=
  ∀ i : Fin p.ancillaBits, z (ancillaWire p i) = false

variable {p}

/-- Reads a Boolean list into the program input register, truncating excess bits and filling
missing bits with false. -/
def listToInput (p : WitnessVerifierProgram) (x : List Bool) :
    Reg p.inputBits := fun i => x.getD i.val false

open Classical in

/-- Embeds a witness state into the full register with the prescribed classical input and zero
ancillas. -/
noncomputable def verifierInitialState (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (w : QState (Reg p.witnessBits)) :
    QState (Reg (programQubits p)) :=
  fun z => if inputRestrict p z = x ∧ ancillaZero p z then w (witnessRestrict p z) else 0

open Classical in

/-- Embeds a witness matrix into the full register with the prescribed classical input and zero
ancillas on both indices. -/
noncomputable def verifierInputDensity (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  Matrix.of fun z z' =>
    if inputRestrict p z = x ∧ inputRestrict p z' = x ∧
        ancillaZero p z ∧ ancillaZero p z' then
      σ (witnessRestrict p z) (witnessRestrict p z')
    else 0

/-- The configurations whose output wire is true, or the empty event if the output index is out
of range. -/
def programOutputEvent (p : WitnessVerifierProgram) :
    Finset (Reg (programQubits p)) :=
  if h : p.outputWire < programQubits p then
    Finset.univ.filter fun z => z ⟨p.outputWire, h⟩ = true
  else ∅

/-- The sum of real diagonal entries on the output event after initializing and evolving a
witness matrix. -/
noncomputable def acceptProb (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    ℝ :=
  ∑ z ∈ programOutputEvent p,
    ((programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) z z).re

/-- Requires a witness matrix to be Hermitian and positive semidefinite with trace at most one. -/
def IsWitnessDensity {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Prop :=
  σ.IsHermitian ∧ σ.PosSemidef ∧ Matrix.trace σ ≤ 1

/-- The outer-product matrix of a witness vector, without imposing normalization. -/
noncomputable def pureWitnessDensity {m : ℕ} (ψ : QState (Reg m)) :
    Matrix (Reg m) (Reg m) ℂ := outerProduct ψ

/-- The pure density matrix of a computational basis witness. -/
noncomputable def classicalWitnessDensity {m : ℕ} (w : Reg m) :
    Matrix (Reg m) (Reg m) ℂ := outerProduct (Ket w)

/-- Places a classical witness in the initial register segment and sets all remaining wires to
false. -/
def classicalWitnessEncoding (p : WitnessVerifierProgram) (w : Reg p.witnessBits) :
    Reg (programQubits p) := fun i =>
  if h : i.val < p.witnessBits then w ⟨i.val, h⟩ else false

/-- A Turing-machine verifier generator together with polynomial time and program-size bound
parameters. -/
structure WitnessVerifierFamily where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ
  programCoefficient : ℕ
  programDegree : ℕ

/-- The natural-number polynomial bound `c * (n + 1) ^ d`. -/
def witnessPolynomialBound (c d n : ℕ) : ℕ := c * (n + 1) ^ d

/-- Returns a halted Turing-machine configuration reachable within the given transition budget,
or no result when the budget is exhausted. -/
private def runUntilHaltWithin {k : ℕ}
    (machine : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) :
    ℕ → Turing.TM0.Cfg (Option Bool) (Fin (k + 1)) →
      Option (Turing.TM0.Cfg (Option Bool) (Fin (k + 1)))
  | 0, cfg => if Turing.TM0.step machine cfg = none then some cfg else none
  | fuel + 1, cfg =>
      match Turing.TM0.step machine cfg with
      | none => some cfg
      | some next => runUntilHaltWithin machine fuel next

/-- Reads Boolean tape symbols until a blank is reached, failing if the prefix exceeds the fuel
bound. -/
private def readOutputUntilBlank : ℕ → Turing.ListBlank (Option Bool) → Option (List Bool)
  | 0, tape => if tape.nth 0 = none then some [] else none
  | fuel + 1, tape =>
      match tape.nth 0 with
      | none => some []
      | some bit => (readOutputUntilBlank fuel tape.tail).map (bit :: ·)

/-- Parses a natural number encoded by true bits terminated by false, returning the unconsumed
suffix. -/
private def parseUnaryField : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseUnaryField rest).map fun (k, tail) => (k + 1, tail)

/-- Parses the specified number of unary natural-number fields and returns the remaining bits. -/
private def parseManyNatFields : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← parseUnaryField bits
      let (tail, finalBits) ← parseManyNatFields count rest
      pure (head :: tail, finalBits)

/-- Parses the operands of a fixed gate or oracle instruction from its numerical tag and
bitstring suffix. -/
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

/-- Parses a complete instruction list subject to a bound on the number of parsed instructions. -/
private def parseInstructionListFuel : ℕ → List Bool → Option (List WitnessInstruction)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, bits => do
      let (tag, rest) ← parseUnaryField bits
      let (instruction, tail) ← parseInstructionFields tag rest
      let instructions ← parseInstructionListFuel fuel tail
      pure (instruction :: instructions)

/-- Decodes verifier metadata and instructions from Boolean fields, with an all-true bitstring
encoding the empty verifier for that input length. -/
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

/-- Encodes a natural-number input as a list of `some true` tape symbols. -/
private def unaryInput (n : ℕ) : List (Option Bool) :=
  List.replicate n (some true)

variable (f : WitnessVerifierFamily)

/-- The generator's polynomial transition budget at input length `n`. -/
private def generatorFuel (f : WitnessVerifierFamily) (n : ℕ) : ℕ :=
  witnessPolynomialBound f.timeCoefficient f.timeDegree n

/-- The generator's polynomial bound on register width and instruction-list length at input
length `n`. -/
private def generatorProgramBound (f : WitnessVerifierFamily) (n : ℕ) : ℕ :=
  witnessPolynomialBound f.programCoefficient f.programDegree n

/-- Runs the generator on unary input within its time budget, reads its halted output, and
decodes a verifier program. -/
noncomputable def witnessProgramAt (f : WitnessVerifierFamily) (n : ℕ) :
    Option WitnessVerifierProgram :=
  (runUntilHaltWithin f.machine (generatorFuel f n)
    (Turing.TM0.init (unaryInput n))).bind fun cfg =>
      (readOutputUntilBlank (n + generatorFuel f n + 1) cfg.Tape.right₀).bind
        decodeWitnessVerifierProgram

/-- Returns the generated verifier at a given input length, using `defaultVerifierProgram` if
generation fails. -/
noncomputable def familyProgram (f : WitnessVerifierFamily) (n : ℕ) : WitnessVerifierProgram :=
  (witnessProgramAt f n).getD defaultVerifierProgram

/-- Requires successful generation at every length with the correct input width, polynomially
bounded qubits and instructions, and legal output and instructions. -/
def witnessFamilyValid (f : WitnessVerifierFamily) : Prop :=
  ∀ n : ℕ, ∃ p : WitnessVerifierProgram,
    witnessProgramAt f n = some p ∧
      p.inputBits = n ∧
      programQubits p ≤ generatorProgramBound f n ∧
      p.instructions.length ≤ generatorProgramBound f n ∧
      witnessProgramLegal p

variable {f}

/-- Membership witnessed by a valid oracle-free verifier family with quantum witnesses and
completeness and soundness thresholds `2 / 3` and `1 / 3`, evaluated using `A`. -/
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

/-- The quantum-witness promise predicate `InQMAWith` specialized to the constantly false
oracle. -/
def InQMA (L : BitstringPromise) : Prop := InQMAWith (fun _ _ => false) L

/-- Membership witnessed by a valid oracle-free verifier family using computational basis
witnesses, with completeness `2 / 3` and soundness `1 / 3`. -/
def InQCMA (L : BitstringPromise) : Prop :=
  ∃ f : WitnessVerifierFamily, witnessFamilyValid f ∧
    (∀ n, oracleFree (familyProgram f n)) ∧
    (∀ x ∈ L.yes, ∃ w : Reg (familyProgram f x.length).witnessBits,
      2 / 3 ≤ acceptProb (fun _ _ => false) (familyProgram f x.length)
          (listToInput _ x) (classicalWitnessDensity w)) ∧
    (∀ x ∈ L.no, ∀ w : Reg (familyProgram f x.length).witnessBits,
      acceptProb (fun _ _ => false) (familyProgram f x.length)
          (listToInput _ x) (classicalWitnessDensity w) ≤ 1 / 3)

/-- Membership witnessed by a valid oracle-free verifier family with zero witness width and
acceptance thresholds `2 / 3` and `1 / 3`. -/
def InBQPWitnessModel (L : BitstringPromise) : Prop :=
  ∃ f : WitnessVerifierFamily, witnessFamilyValid f ∧
    (∀ n, oracleFree (familyProgram f n) ∧ (familyProgram f n).witnessBits = 0) ∧
    (∀ x ∈ L.yes, 2 / 3 ≤ acceptProb (fun _ _ => false) (familyProgram f x.length)
        (listToInput _ x) 1) ∧
    (∀ x ∈ L.no, acceptProb (fun _ _ => false) (familyProgram f x.length)
        (listToInput _ x) 1 ≤ 1 / 3)

/-- Shifts a wire index by `k` exactly when it lies after the original witness segment. -/
def padWire (witnessBits k : ℕ) (w : ℕ) : ℕ :=
  if w < witnessBits then w else w + k

/-- Relabels every wire in a finite gate code to insert `k` extra witness wires. -/
def padFiniteCode (witnessBits k : ℕ) : FiniteGateCode → FiniteGateCode
  | .h w => .h (padWire witnessBits k w)
  | .x w => .x (padWire witnessBits k w)
  | .t w => .t (padWire witnessBits k w)
  | .tdg w => .tdg (padWire witnessBits k w)
  | .cx c t => .cx (padWire witnessBits k c) (padWire witnessBits k t)

/-- Adds `k` witness wires and shifts subsequent wire indices in the output and all
instructions. -/
def padProgram (p : WitnessVerifierProgram) (k : ℕ) : WitnessVerifierProgram where
  witnessBits := p.witnessBits + k
  inputBits := p.inputBits
  ancillaBits := p.ancillaBits
  outputWire := padWire p.witnessBits k p.outputWire
  instructions := p.instructions.map fun
    | .fixed gate => .fixed (padFiniteCode p.witnessBits k gate)
    | .oracle addresses target => .oracle (addresses.map (padWire p.witnessBits k))
        (padWire p.witnessBits k target)

/-- Extends a witness matrix by `k` additional witness bits fixed to zero on both matrix
indices. -/
noncomputable def extendWitnessDensity {m : ℕ}
    (σ : Matrix (Reg m) (Reg m) ℂ) (k : ℕ) :
    Matrix (Reg (m + k)) (Reg (m + k)) ℂ :=
  Matrix.of fun u u' =>
    if (∀ j : Fin k, u (Fin.natAdd m j) = false) ∧
        (∀ j : Fin k, u' (Fin.natAdd m j) = false) then
      σ (fun i => u (Fin.castAdd k i)) (fun i => u' (Fin.castAdd k i))
    else 0

/-- Extends a classical witness by `k` false bits. -/
def padClassicalWitness {m : ℕ} (w : Reg m) (k : ℕ) : Reg (m + k) :=
  fun i => if h : i.val < m then w ⟨i.val, h⟩ else false

/-- The one-control-state Turing machine that halts immediately on every configuration. -/
private def immediateHaltMachine :
    Turing.TM0.Machine (Option Bool) (Fin 1) := fun _ _ => none

/-- The immediately halting family whose unchanged unary input decodes to an empty verifier with
one ancilla. -/
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

/-- Translates a uniform verifier to a witness program with no input register, merging both
oracle labels and treating the remaining qubits as ancillas. -/
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
