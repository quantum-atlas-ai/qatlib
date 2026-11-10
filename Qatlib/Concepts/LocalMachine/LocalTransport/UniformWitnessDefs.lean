/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
import Qatlib.Concepts.WalshMoment.Forrelation.UniformVerifierDefs
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
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

structure BitLanguage where

  yes : List Bool → Bool

  no : List Bool → Bool

  disjoint : ∀ x : List Bool, ¬ (yes x = true ∧ no x = true)

def BitstringPromise.toBitLanguage (L : BitstringPromise) : BitLanguage where
  yes := fun x => decide (x ∈ L.yes)
  no := fun x => decide (x ∈ L.no)
  disjoint := by
    intro x hx
    rcases hx with ⟨hy, hn⟩
    have hmem : x ∈ L.yes := by simpa only [decide_eq_true_eq] using hy
    have hmem' : x ∈ L.no := by simpa only [decide_eq_true_eq] using hn
    exact (Finset.disjoint_left.mp L.disjoint hmem) hmem'

def unaryNat (k : ℕ) : List Bool := List.replicate k true ++ [false]

def witnessInstructionTag : WitnessInstruction → ℕ
  | .fixed (.h _) => 0
  | .fixed (.x _) => 1
  | .fixed (.t _) => 2
  | .fixed (.tdg _) => 3
  | .fixed (.cx _ _) => 4
  | .oracle _ _ => 5

def encodeWitnessFields : WitnessInstruction → List Bool
  | .fixed (.h w) => unaryNat w
  | .fixed (.x w) => unaryNat w
  | .fixed (.t w) => unaryNat w
  | .fixed (.tdg w) => unaryNat w
  | .fixed (.cx c t) => unaryNat c ++ unaryNat t
  | .oracle addresses target =>
      unaryNat addresses.length ++ (addresses.map unaryNat).flatten ++ unaryNat target

def encodeWitnessInstruction (i : WitnessInstruction) : List Bool :=
  unaryNat (witnessInstructionTag i) ++ encodeWitnessFields i

def encodeWitnessProgram (p : WitnessVerifierProgram) : List Bool :=
  unaryNat p.witnessBits ++ unaryNat p.inputBits ++ unaryNat p.ancillaBits
    ++ unaryNat p.outputWire ++ (p.instructions.map encodeWitnessInstruction).flatten

def programGateLedger (p : WitnessVerifierProgram) : ℕ := p.instructions.length

def programBitLedger (p : WitnessVerifierProgram) : ℕ :=
  (p.instructions.map fun _ => 4 + 2 * programQubits p).sum

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

def UniformWitnessFamily.OracleFree (f : UniformWitnessFamily) : Prop :=
  ∀ x : List Bool, oracleFree (f.generator x)

def UniformWitnessFamily.NoWitness (f : UniformWitnessFamily) : Prop :=
  ∀ n : ℕ, f.witnessWidth n = 0

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

theorem cnotWitnessFamily_oracleFree : cnotWitnessFamily.OracleFree := by
  intro x
  show (cnotWitnessFamily.generator x).instructions.all
    (fun | .fixed _ => true | .oracle _ _ => false) = true
  simp [cnotWitnessFamily, oracleFree]

noncomputable def uniformDensity (f : UniformWitnessFamily) (x : List Bool)
    (σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ) :
    Matrix (Reg (f.generator x).witnessBits) (Reg (f.generator x).witnessBits) ℂ :=
  cast (congrArg (fun m => Matrix (Reg m) (Reg m) ℂ) (f.generatorWidths x).1.symm) σ

noncomputable def uniformAcceptProb (f : UniformWitnessFamily) (A : ClassicalOracle)
    (x : List Bool)
    (σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ) : ℝ :=
  acceptProb A (f.generator x) (listToInput (f.generator x) x) (uniformDensity f x σ)

noncomputable def uniformPureDensity (f : UniformWitnessFamily) (x : List Bool)
    (ψ : QState (Reg (f.witnessWidth x.length))) :
    Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ :=
  pureWitnessDensity ψ

noncomputable def uniformClassicalDensity (f : UniformWitnessFamily) (x : List Bool)
    (w : Reg (f.witnessWidth x.length)) :
    Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ :=
  classicalWitnessDensity w

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

def InUniformBQP (L : BitLanguage) : Prop :=
  ∃ f : UniformWitnessFamily, f.NoWitness ∧ f.OracleFree ∧
    (∀ x : List Bool, L.yes x = true →
      2 / 3 ≤ acceptProb (fun _ _ => false) (f.generator x)
        (listToInput (f.generator x) x) 1) ∧
    (∀ x : List Bool, L.no x = true →
      acceptProb (fun _ _ => false) (f.generator x)
        (listToInput (f.generator x) x) 1 ≤ 1 / 3)

def oracleAccessLedger (p : WitnessVerifierProgram) : List ℕ :=
  (p.instructions.filterMap fun
    | .fixed _ => none
    | .oracle addresses _ => some addresses.length)

def controlledAccessLength (addresses : List ℕ) : ℕ := addresses.length + 1

def defaultUniformVerifierProgram : UniformVerifierProgram where
  qubits := 1
  witnessBits := 0
  outputWire := 0
  instructions := []

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
