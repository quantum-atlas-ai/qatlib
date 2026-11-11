/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
import Qatlib.Concepts.WalshMoment.Forrelation.UniformVerifierDefs
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Uniform witness families and their resource ledgers

This module defines `BitLanguage` as disjoint Boolean tests for yes and no instances, together
with unary encodings of witness verifier instructions and programs. `UniformWitnessFamily`
packages an input-indexed legal program generator, a witness width depending on input length,
and polynomial bounds on instruction count, qubits, and `programBitLedger`. The explicit family
`cnotWitnessFamily` uses one witness bit and one controlled-NOT instruction.

The density wrappers `uniformDensity` and `uniformAcceptProb` align witness widths with
generated programs. The local predicates `InUniformQMA`, `InUniformQCMA`, and `InUniformBQP`
express completeness at least two thirds and soundness at most one third using quantum,
classical, or zero-bit witnesses. `SharedOracleUniformFamily` separately packages a common
oracle and an oracle-call count bound. The density formalism follows [NielsenChuang2010], and
the quantum-proof setting is discussed by [MarriottWatrous2005].

## Main statements

* `encodeWitnessProgram` encodes register widths, the output wire, and instructions as Boolean
  lists.
- `UniformWitnessFamily` records width consistency, legality, and polynomial resource bounds.
* `cnotWitnessFamily_oracleFree` verifies that the concrete family contains no oracle
  instructions.
* `InUniformQMA`, `InUniformQCMA`, and `InUniformBQP` define the three witness acceptance
  conditions.
* `oracleAccessLedger` and `SharedOracleUniformFamily` record oracle access lengths and the
  shared-oracle family data.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025
open Matrix

set_option autoImplicit false

/-- A promise problem on Boolean lists specified by disjoint Boolean tests for yes and no
instances. -/
structure BitLanguage where

  yes : List Bool → Bool

  no : List Bool → Bool

  disjoint : ∀ x : List Bool, ¬ (yes x = true ∧ no x = true)

/-- Converts a finite bitstring promise to Boolean membership tests, retaining disjointness of
its yes and no instances. -/
def BitstringPromise.toBitLanguage (L : BitstringPromise) : BitLanguage where
  yes := fun x => decide (x ∈ L.yes)
  no := fun x => decide (x ∈ L.no)
  disjoint := by
    intro x hx
    rcases hx with ⟨hy, hn⟩
    have hmem : x ∈ L.yes := by simpa only [decide_eq_true_eq] using hy
    have hmem' : x ∈ L.no := by simpa only [decide_eq_true_eq] using hn
    exact (Finset.disjoint_left.mp L.disjoint hmem) hmem'

/-- Encodes `k` as `k` copies of `true` followed by one terminating `false`. -/
def unaryNat (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- Assigns tags zero through five to Hadamard, X, T, T-adjoint, controlled-NOT, and oracle
instructions, respectively. -/
def witnessInstructionTag : WitnessInstruction → ℕ
  | .fixed (.h _) => 0
  | .fixed (.x _) => 1
  | .fixed (.t _) => 2
  | .fixed (.tdg _) => 3
  | .fixed (.cx _ _) => 4
  | .oracle _ _ => 5

/-- Encodes an instruction's wire indices as unary fields, including the address count before an
oracle instruction's address list. -/
def encodeWitnessFields : WitnessInstruction → List Bool
  | .fixed (.h w) => unaryNat w
  | .fixed (.x w) => unaryNat w
  | .fixed (.t w) => unaryNat w
  | .fixed (.tdg w) => unaryNat w
  | .fixed (.cx c t) => unaryNat c ++ unaryNat t
  | .oracle addresses target =>
      unaryNat addresses.length ++ (addresses.map unaryNat).flatten ++ unaryNat target

/-- Encodes a witness instruction by concatenating its unary tag with its encoded fields. -/
def encodeWitnessInstruction (i : WitnessInstruction) : List Bool :=
  unaryNat (witnessInstructionTag i) ++ encodeWitnessFields i

/-- Encodes a witness verifier program as unary register widths and output wire, followed by its
concatenated instruction encodings. -/
def encodeWitnessProgram (p : WitnessVerifierProgram) : List Bool :=
  unaryNat p.witnessBits ++ unaryNat p.inputBits ++ unaryNat p.ancillaBits
    ++ unaryNat p.outputWire ++ (p.instructions.map encodeWitnessInstruction).flatten

/-- Counts the instructions in a witness verifier program. -/
def programGateLedger (p : WitnessVerifierProgram) : ℕ := p.instructions.length

/-- Assigns each instruction a cost of `4 + 2 * programQubits p` and sums these costs over the
program. -/
def programBitLedger (p : WitnessVerifierProgram) : ℕ :=
  (p.instructions.map fun _ => 4 + 2 * programQubits p).sum

/-- An input-indexed family of legal witness verifier programs with consistent register widths
and polynomial bounds on instructions, qubits, and the bit ledger. -/
structure UniformWitnessFamily where

  witnessWidth : ℕ → ℕ

  generator : List Bool → WitnessVerifierProgram

  gateCoefficient : ℕ

  gateDegree : ℕ

  bitCoefficient : ℕ

  bitDegree : ℕ

  spaceCoefficient : ℕ

  spaceDegree : ℕ

  generatorWidths : ∀ x : List Bool,
    (generator x).witnessBits = witnessWidth x.length ∧
      (generator x).inputBits = x.length

  generatorLegal : ∀ x : List Bool, witnessProgramLegal (generator x)

  generatorGateBound : ∀ x : List Bool,
    (generator x).instructions.length ≤
      witnessPolynomialBound gateCoefficient gateDegree x.length

  generatorSpaceBound : ∀ x : List Bool,
    programQubits (generator x) ≤
      witnessPolynomialBound spaceCoefficient spaceDegree x.length

  generatorBitBound : ∀ x : List Bool,
    programBitLedger (generator x) ≤
      witnessPolynomialBound bitCoefficient bitDegree x.length

/-- Requires every program generated by the family to contain no oracle instructions. -/
def UniformWitnessFamily.OracleFree (f : UniformWitnessFamily) : Prop :=
  ∀ x : List Bool, oracleFree (f.generator x)

/-- Requires the family's witness width to be zero at every input length. -/
def UniformWitnessFamily.NoWitness (f : UniformWitnessFamily) : Prop :=
  ∀ n : ℕ, f.witnessWidth n = 0

/-- A family with one witness bit and one ancilla that applies a controlled-NOT from the witness
to the output ancilla, with explicit polynomial resource bounds. -/
def cnotWitnessFamily : UniformWitnessFamily where
  witnessWidth := fun _ => 1
  generator := fun x =>
    { witnessBits := 1, inputBits := x.length, ancillaBits := 1,
      outputWire := x.length + 1, instructions := [.fixed (.cx 0 (x.length + 1))] }
  gateCoefficient := 1
  gateDegree := 1
  bitCoefficient := 12
  bitDegree := 1
  spaceCoefficient := 2
  spaceDegree := 1
  generatorWidths := by
    intro x
    exact ⟨rfl, rfl⟩
  generatorLegal := by
    intro x
    constructor
    · show x.length + 1 < 1 + x.length + 1
      omega
    · intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      show instructionLegal (1 + x.length + 1) (.fixed (.cx 0 (x.length + 1)))
      show finiteCodeLegal (1 + x.length + 1) (.cx 0 (x.length + 1)) = true
      simp [finiteCodeLegal]
  generatorGateBound := by
    intro x
    show (1 : ℕ) ≤ witnessPolynomialBound 1 1 x.length
    show (1 : ℕ) ≤ 1 * (x.length + 1) ^ 1
    simp
  generatorSpaceBound := by
    intro x
    show (1 + x.length + 1 : ℕ) ≤ witnessPolynomialBound 2 1 x.length
    show (1 + x.length + 1 : ℕ) ≤ 2 * (x.length + 1) ^ 1
    simp
    omega
  generatorBitBound := by
    intro x
    show programBitLedger
        { witnessBits := 1, inputBits := x.length, ancillaBits := 1,
          outputWire := x.length + 1, instructions := [.fixed (.cx 0 (x.length + 1))] }
        ≤ witnessPolynomialBound 12 1 x.length
    show (4 + 2 * (1 + x.length + 1) : ℕ) ≤ 12 * (x.length + 1) ^ 1
    simp
    omega

/-- Every program generated by `cnotWitnessFamily` is oracle-free. -/
theorem cnotWitnessFamily_oracleFree : cnotWitnessFamily.OracleFree := by
  intro x
  show (cnotWitnessFamily.generator x).instructions.all
    (fun | .fixed _ => true | .oracle _ _ => false) = true
  simp [cnotWitnessFamily, oracleFree]

/-- Transports a witness matrix from the family's prescribed witness width to the equal witness
width of the generated program. -/
noncomputable def uniformDensity (f : UniformWitnessFamily) (x : List Bool)
    (σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ) :
    Matrix (Reg (f.generator x).witnessBits) (Reg (f.generator x).witnessBits) ℂ :=
  cast (congrArg (fun m => Matrix (Reg m) (Reg m) ℂ) (f.generatorWidths x).1.symm) σ

/-- Evaluates the generated verifier's acceptance value on input `x` after transporting the
witness matrix to the program's register type. -/
noncomputable def uniformAcceptProb (f : UniformWitnessFamily) (A : ClassicalOracle)
    (x : List Bool)
    (σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ) : ℝ :=
  acceptProb A (f.generator x) (listToInput (f.generator x) x) (uniformDensity f x σ)

/-- Forms the pure witness density matrix of a state at the family's witness width for input
`x`. -/
noncomputable def uniformPureDensity (f : UniformWitnessFamily) (x : List Bool)
    (ψ : QState (Reg (f.witnessWidth x.length))) :
    Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ :=
  pureWitnessDensity ψ

/-- Forms the computational-basis density matrix of a classical witness at the family's witness
width for input `x`. -/
noncomputable def uniformClassicalDensity (f : UniformWitnessFamily) (x : List Bool)
    (w : Reg (f.witnessWidth x.length)) :
    Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ :=
  classicalWitnessDensity w

/-- Requires an oracle-free uniform witness family accepting some valid quantum witness with
probability at least two thirds on yes instances and every valid witness with probability at
most one third on no instances. -/
def InUniformQMA (L : BitLanguage) : Prop :=
  ∃ f : UniformWitnessFamily, f.OracleFree ∧
    (∀ x : List Bool, L.yes x = true →
      ∃ σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ,
        IsWitnessDensity σ ∧
          2 / 3 ≤ uniformAcceptProb f (fun _ _ => false) x σ) ∧
    (∀ x : List Bool, L.no x = true →
      ∀ σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ,
        IsWitnessDensity σ →
          uniformAcceptProb f (fun _ _ => false) x σ ≤ 1 / 3)

/-- Requires an oracle-free uniform witness family accepting some classical witness with
probability at least two thirds on yes instances and every classical witness with
probability at most one third on no instances. -/
def InUniformQCMA (L : BitLanguage) : Prop :=
  ∃ f : UniformWitnessFamily, f.OracleFree ∧
    (∀ x : List Bool, L.yes x = true →
      ∃ w : Reg (f.witnessWidth x.length),
        2 / 3 ≤ uniformAcceptProb f (fun _ _ => false) x
          (uniformClassicalDensity f x w)) ∧
    (∀ x : List Bool, L.no x = true →
      ∀ w : Reg (f.witnessWidth x.length),
        uniformAcceptProb f (fun _ _ => false) x
          (uniformClassicalDensity f x w) ≤ 1 / 3)

/-- Requires an oracle-free uniform family with zero witness width whose identity witness matrix
gives acceptance at least two thirds on yes instances and at most one third on no instances. -/
def InUniformBQP (L : BitLanguage) : Prop :=
  ∃ f : UniformWitnessFamily, f.NoWitness ∧ f.OracleFree ∧
    (∀ x : List Bool, L.yes x = true →
      2 / 3 ≤ acceptProb (fun _ _ => false) (f.generator x)
        (listToInput (f.generator x) x) 1) ∧
    (∀ x : List Bool, L.no x = true →
      acceptProb (fun _ _ => false) (f.generator x)
        (listToInput (f.generator x) x) 1 ≤ 1 / 3)

/-- Lists the address-register lengths of oracle instructions in program order, omitting fixed
gates. -/
def oracleAccessLedger (p : WitnessVerifierProgram) : List ℕ :=
  (p.instructions.filterMap fun
    | .fixed _ => none
    | .oracle addresses _ => some addresses.length)

/-- Counts the address wires together with one additional control wire. -/
def controlledAccessLength (addresses : List ℕ) : ℕ := addresses.length + 1

/-- An empty one-qubit verifier program with zero witness bits and output wire zero. -/
def defaultUniformVerifierProgram : UniformVerifierProgram where
  qubits := 1
  witnessBits := 0
  outputWire := 0
  instructions := []

/-- A family of legal witness verifier programs using one shared classical oracle, with
witness-width consistency and an oracle-call count bounded by the instruction count. -/
structure SharedOracleUniformFamily where

  witnessWidth : ℕ → ℕ

  generator : List Bool → WitnessVerifierProgram

  oracle : ClassicalOracle

  generatorWidths : ∀ x : List Bool,
    (generator x).witnessBits = witnessWidth x.length

  generatorLegal : ∀ x : List Bool, witnessProgramLegal (generator x)

  accessBound : ∀ x : List Bool,
    (oracleAccessLedger (generator x)).length ≤ (generator x).instructions.length

end Qatlib.Concepts.LocalMachine.LocalTransport
