/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitnessDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness

open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025
open Matrix
open scoped ComplexOrder

set_option autoImplicit false

def modelParseUnaryField : List Bool → Option (ℕ × List Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.parseUnaryField").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelParseManyNatFields : ℕ → List Bool → Option (List ℕ × List Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.parseManyNatFields").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelParseInstructionFields : ℕ → List Bool → Option (WitnessInstruction × List Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.parseInstructionFields").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelParseInstructionListFuel : ℕ → List Bool → Option (List WitnessInstruction) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.parseInstructionListFuel").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

theorem modelParseUnaryField_nil : modelParseUnaryField [] = none := rfl

theorem modelParseUnaryField_false (rest : List Bool) :
    modelParseUnaryField (false :: rest) = some (0, rest) := rfl

theorem modelParseUnaryField_true (rest : List Bool) :
    modelParseUnaryField (true :: rest) =
      (modelParseUnaryField rest).map (fun (k, tail) => (k + 1, tail)) := rfl

theorem modelParseManyNatFields_zero (bits : List Bool) :
    modelParseManyNatFields 0 bits = some ([], bits) := rfl

theorem modelParseManyNatFields_succ (count : ℕ) (bits : List Bool) :
    modelParseManyNatFields (count + 1) bits =
      (modelParseUnaryField bits).bind fun (head, rest) =>
        (modelParseManyNatFields count rest).bind fun (tail, finalBits) =>
          some (head :: tail, finalBits) := by
  rfl

end Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness

namespace Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness

open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025
open Matrix
open scoped ComplexOrder

set_option autoImplicit false

theorem modelParseUnaryField_unaryNat (k : ℕ) (rest : List Bool) :
    modelParseUnaryField (unaryNat k ++ rest) = some (k, rest) := by
  induction k with
  | zero =>
      show modelParseUnaryField (false :: rest) = some (0, rest)
      exact modelParseUnaryField_false rest
  | succ k ih =>
      have hrep : List.replicate (k + 1) true = true :: List.replicate k true := by
        simp [List.replicate_succ]
      have hword : unaryNat (k + 1) ++ rest = true :: (unaryNat k ++ rest) := by
        simp [unaryNat, hrep, List.append_assoc]
      rw [hword, modelParseUnaryField_true, ih]
      rfl

theorem modelParseManyNatFields_concat (addrs : List ℕ) (rest : List Bool) :
    modelParseManyNatFields addrs.length ((addrs.map unaryNat).flatten ++ rest)
      = some (addrs, rest) := by
  induction addrs with
  | nil =>
      show modelParseManyNatFields 0 rest = some ([], rest)
      exact modelParseManyNatFields_zero rest
  | cons a as ih =>
      have hlen : (a :: as).length = as.length + 1 := by simp
      have hword : ((a :: as).map unaryNat).flatten ++ rest
          = unaryNat a ++ ((as.map unaryNat).flatten ++ rest) := by
        simp [List.map_cons, List.flatten_cons, List.append_assoc]
      rw [hlen, hword, modelParseManyNatFields_succ,
        modelParseUnaryField_unaryNat]
      simp only [Option.bind_some]
      rw [ih]
      rfl

theorem modelParseInstructionFields_h (bits : List Bool) :
    modelParseInstructionFields 0 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (.fixed (.h w), rest) := by
  rfl

theorem modelParseInstructionFields_x (bits : List Bool) :
    modelParseInstructionFields 1 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (.fixed (.x w), rest) := by
  rfl

theorem modelParseInstructionFields_t (bits : List Bool) :
    modelParseInstructionFields 2 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (.fixed (.t w), rest) := by
  rfl

theorem modelParseInstructionFields_tdg (bits : List Bool) :
    modelParseInstructionFields 3 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (.fixed (.tdg w), rest) := by
  rfl

theorem modelParseInstructionFields_cx (bits : List Bool) :
    modelParseInstructionFields 4 bits =
      (modelParseUnaryField bits).bind fun (c, rest) =>
        (modelParseUnaryField rest).bind fun (t, tail) =>
          some (.fixed (.cx c t), tail) := by
  rfl

theorem modelParseInstructionFields_oracle (bits : List Bool) :
    modelParseInstructionFields 5 bits =
      (modelParseUnaryField bits).bind fun (count, rest) =>
        (modelParseManyNatFields count rest).bind fun (addresses, rest') =>
          (modelParseUnaryField rest').bind fun (target, tail) =>
            some (.oracle addresses target, tail) := by
  rfl

theorem modelParseInstructionListFuel_nil (fuel : ℕ) :
    modelParseInstructionListFuel fuel [] = some [] := by
  cases fuel with
  | zero => rfl
  | succ k => rfl

theorem modelParseInstructionListFuel_cons (fuel : ℕ) (b : Bool) (bits : List Bool) :
    modelParseInstructionListFuel (fuel + 1) (b :: bits) =
      (modelParseUnaryField (b :: bits)).bind fun (tag, rest) =>
        (modelParseInstructionFields tag rest).bind fun (instr, tail) =>
          (modelParseInstructionListFuel fuel tail).bind fun instructions =>
            some (instr :: instructions) := by
  rfl

theorem modelParseInstructionFields_encode (i : WitnessInstruction) (rest : List Bool) :
    modelParseInstructionFields (witnessInstructionTag i) (encodeWitnessFields i ++ rest)
      = some (i, rest) := by
  cases i with
  | fixed gate =>
      cases gate with
      | h w =>
          simp only [witnessInstructionTag, encodeWitnessFields, List.append_assoc]
          rw [modelParseInstructionFields_h, modelParseUnaryField_unaryNat]
          simp only [Option.bind_some]
      | x w =>
          simp only [witnessInstructionTag, encodeWitnessFields, List.append_assoc]
          rw [modelParseInstructionFields_x, modelParseUnaryField_unaryNat]
          simp only [Option.bind_some]
      | t w =>
          simp only [witnessInstructionTag, encodeWitnessFields, List.append_assoc]
          rw [modelParseInstructionFields_t, modelParseUnaryField_unaryNat]
          simp only [Option.bind_some]
      | tdg w =>
          simp only [witnessInstructionTag, encodeWitnessFields, List.append_assoc]
          rw [modelParseInstructionFields_tdg, modelParseUnaryField_unaryNat]
          simp only [Option.bind_some]
      | cx c t =>
          simp only [witnessInstructionTag, encodeWitnessFields, List.append_assoc]
          rw [modelParseInstructionFields_cx, modelParseUnaryField_unaryNat]
          simp only [Option.bind_some]
          rw [modelParseUnaryField_unaryNat]
          simp only [Option.bind_some]
  | oracle addresses target =>
      simp only [witnessInstructionTag, encodeWitnessFields, List.append_assoc]
      rw [modelParseInstructionFields_oracle, modelParseUnaryField_unaryNat]
      simp only [Option.bind_some]
      rw [modelParseManyNatFields_concat]
      simp only [Option.bind_some]
      rw [modelParseUnaryField_unaryNat]
      simp only [Option.bind_some]

theorem modelParseInstructionListFuel_ge (instrs : List WitnessInstruction) :
    ∀ (fuel : ℕ), fuel ≥ (instrs.map encodeWitnessInstruction).flatten.length →
      modelParseInstructionListFuel fuel ((instrs.map encodeWitnessInstruction).flatten)
        = some instrs := by
  induction instrs with
  | nil =>
      intro fuel _
      exact modelParseInstructionListFuel_nil fuel
  | cons i is ih =>
      intro fuel hfuel
      have henc : encodeWitnessInstruction i ≠ [] := by
        cases i with
        | fixed gate =>
            cases gate <;>
              simp [encodeWitnessInstruction, encodeWitnessFields, unaryNat]
        | oracle addresses target =>
            simp [encodeWitnessInstruction, encodeWitnessFields, unaryNat]
      obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil henc
      have hlen : ((i :: is).map encodeWitnessInstruction).flatten.length
          = (encodeWitnessInstruction i).length
            + ((is.map encodeWitnessInstruction).flatten).length := by
        simp [List.map_cons, List.flatten_cons, List.length_append]
      have hlen2 : (encodeWitnessInstruction i).length
          = (witnessInstructionTag i + 1) + (encodeWitnessFields i).length := by
        simp [encodeWitnessInstruction, unaryNat, List.length_append]
        omega
      have hfields : (encodeWitnessFields i).length ≥ 1 := by
        cases i with
        | fixed gate =>
            cases gate <;> simp [encodeWitnessFields, unaryNat] <;> omega
        | oracle addresses target =>
            simp [encodeWitnessFields, unaryNat]
            omega
      have htwo : (encodeWitnessInstruction i).length ≥ 2 := by
        rw [hlen2]
        omega
      have hwordne : ((i :: is).map encodeWitnessInstruction).flatten ≠ [] := by
        intro h
        have hzero : (encodeWitnessInstruction i).length
            + ((is.map encodeWitnessInstruction).flatten).length = 0 := by
          rw [← hlen, h]
          simp
        omega
      have hsplit : ((i :: is).map encodeWitnessInstruction).flatten
          = encodeWitnessInstruction i ++ ((is.map encodeWitnessInstruction).flatten) := by
        simp [List.map_cons, List.flatten_cons]
      have hwordcons : ((i :: is).map encodeWitnessInstruction).flatten
          = hd :: (tl ++ ((is.map encodeWitnessInstruction).flatten)) := by
        rw [hsplit, hcons]
        rfl
      have hrest : hd :: (tl ++ ((is.map encodeWitnessInstruction).flatten))
          = encodeWitnessInstruction i ++ ((is.map encodeWitnessInstruction).flatten) := by
        rw [hcons]
        rfl
      rw [hwordcons]
      have hk : fuel = (fuel - 1) + 1 := by omega
      rw [hk]
      rw [modelParseInstructionListFuel_cons]
      rw [hrest]
      simp only [encodeWitnessInstruction, List.append_assoc]
      rw [modelParseUnaryField_unaryNat]
      simp only [Option.bind_some]
      rw [modelParseInstructionFields_encode]
      simp only [Option.bind_some]
      have hlt : fuel - 1 ≥ ((is.map encodeWitnessInstruction).flatten).length := by
        omega
      rw [ih (fuel - 1) hlt]
      rfl

theorem modelParseInstructionListFuel_word (instrs : List WitnessInstruction) :
    modelParseInstructionListFuel ((instrs.map encodeWitnessInstruction).flatten).length
      ((instrs.map encodeWitnessInstruction).flatten) = some instrs :=
  modelParseInstructionListFuel_ge instrs _ (Nat.le_refl _)

theorem encodeWitnessProgram_notAllTrue (p : WitnessVerifierProgram) :
    ¬ (encodeWitnessProgram p).all id := by
  have hfalse : false ∈ encodeWitnessProgram p := by
    simp [encodeWitnessProgram, unaryNat]
  intro h
  have hall := List.all_eq_true.mp h false hfalse
  simp at hall

theorem decode_encodeWitnessProgram (p : WitnessVerifierProgram) :
    decodeWitnessVerifierProgram (encodeWitnessProgram p) = some p := by
  have hnotall := encodeWitnessProgram_notAllTrue p
  show (if (encodeWitnessProgram p).all id then
      some ⟨0, (encodeWitnessProgram p).length, 1, 0, []⟩ else
      (modelParseUnaryField (encodeWitnessProgram p)).bind fun (witnessBits, rest) =>
      (modelParseUnaryField rest).bind fun (inputBits, rest') =>
      (modelParseUnaryField rest').bind fun (ancillaBits, rest'') =>
      (modelParseUnaryField rest'').bind fun (outputWire, instructionsBits) =>
      (modelParseInstructionListFuel instructionsBits.length instructionsBits).bind fun instructions =>
        some ⟨witnessBits, inputBits, ancillaBits, outputWire, instructions⟩) = some p
  rw [if_neg hnotall]
  simp only [encodeWitnessProgram, List.append_assoc]
  rw [modelParseUnaryField_unaryNat]
  simp only [Option.bind_some]
  rw [modelParseUnaryField_unaryNat]
  simp only [Option.bind_some]
  rw [modelParseUnaryField_unaryNat]
  simp only [Option.bind_some]
  rw [modelParseUnaryField_unaryNat]
  simp only [Option.bind_some]
  rw [modelParseInstructionListFuel_word]
  rfl

theorem uniformGeneratorWitnessWidth (f : UniformWitnessFamily) (x : List Bool) :
    (f.generator x).witnessBits = f.witnessWidth x.length :=
  (f.generatorWidths x).1

theorem uniformGeneratorInputWidth (f : UniformWitnessFamily) (x : List Bool) :
    (f.generator x).inputBits = x.length :=
  (f.generatorWidths x).2

theorem uniformCleanInitialization (f : UniformWitnessFamily) (x : List Bool)
    (σ : Matrix (Reg (f.generator x).witnessBits) (Reg (f.generator x).witnessBits) ℂ)
    (hherm : σ.IsHermitian) (hpsd : σ.PosSemidef) :
    (verifierInputDensity (f.generator x) (listToInput (f.generator x) x) σ).IsHermitian ∧
      (verifierInputDensity (f.generator x) (listToInput (f.generator x) x) σ).PosSemidef ∧
      Matrix.trace (verifierInputDensity (f.generator x) (listToInput (f.generator x) x) σ)
        = Matrix.trace σ :=
  cleanInitialization (f.generator x) (listToInput (f.generator x) x) σ hherm hpsd

theorem uniformAcceptProb_born (f : UniformWitnessFamily) (A : ClassicalOracle)
    (x : List Bool) (w : QState (Reg (f.generator x).witnessBits)) :
    acceptProb A (f.generator x) (listToInput (f.generator x) x) (pureWitnessDensity w)
      = MeasureProb
          (programRun A (f.generator x)
            (verifierInitialState (f.generator x) (listToInput (f.generator x) x) w))
          (programOutputEvent (f.generator x)) :=
  acceptProb_born A (f.generator x) (listToInput (f.generator x) x) w

theorem uniformAcceptProb_bounds (f : UniformWitnessFamily) (A : ClassicalOracle)
    (x : List Bool)
    (σ : Matrix (Reg (f.generator x).witnessBits) (Reg (f.generator x).witnessBits) ℂ)
    (hd : IsWitnessDensity σ) :
    0 ≤ acceptProb A (f.generator x) (listToInput (f.generator x) x) σ ∧
      acceptProb A (f.generator x) (listToInput (f.generator x) x) σ ≤ 1 :=
  ⟨acceptProb_nonneg A (f.generator x) (listToInput (f.generator x) x) σ hd,
    acceptProb_le_one A (f.generator x) (listToInput (f.generator x) x) σ hd⟩

theorem cnotWitnessFamily_nonDegenerate (x : List Bool) :
    (cnotWitnessFamily.generator x).instructions.length = 1 ∧
      (cnotWitnessFamily.generator x).witnessBits = 1 ∧
        (cnotWitnessFamily.generator x).inputBits = x.length := by
  refine ⟨rfl, rfl, rfl⟩

theorem cnotWitnessFamily_program (x : List Bool) :
    witnessProgramLegal (cnotWitnessFamily.generator x) ∧
      oracleFree (cnotWitnessFamily.generator x) ∧
        (cnotWitnessFamily.generator x).instructions =
          [.fixed (.cx 0 (x.length + 1))] := by
  refine ⟨cnotWitnessFamily.generatorLegal x, cnotWitnessFamily_oracleFree x, rfl⟩

theorem cnotWitnessFamily_ledgers (x : List Bool) :
    (cnotWitnessFamily.generator x).instructions.length
        ≤ witnessPolynomialBound cnotWitnessFamily.gateCoefficient
            cnotWitnessFamily.gateDegree x.length ∧
      programQubits (cnotWitnessFamily.generator x)
        ≤ witnessPolynomialBound cnotWitnessFamily.spaceCoefficient
            cnotWitnessFamily.spaceDegree x.length ∧
      programBitLedger (cnotWitnessFamily.generator x)
        ≤ witnessPolynomialBound cnotWitnessFamily.bitCoefficient
            cnotWitnessFamily.bitDegree x.length :=
  ⟨cnotWitnessFamily.generatorGateBound x, cnotWitnessFamily.generatorSpaceBound x,
    cnotWitnessFamily.generatorBitBound x⟩

theorem cnotWitnessFamily_decoding (x : List Bool) :
    decodeWitnessVerifierProgram
        (encodeWitnessProgram (cnotWitnessFamily.generator x))
      = some (cnotWitnessFamily.generator x) :=
  decode_encodeWitnessProgram (cnotWitnessFamily.generator x)

theorem verifierInputDensity_add (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ₁ σ₂ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    verifierInputDensity p x (σ₁ + σ₂)
      = verifierInputDensity p x σ₁ + verifierInputDensity p x σ₂ := by
  apply Matrix.ext
  intro z z'
  simp only [verifierInputDensity, Matrix.of_apply, Matrix.add_apply]
  by_cases h : inputRestrict p z = x ∧ inputRestrict p z' = x ∧
      ancillaZero p z ∧ ancillaZero p z'
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h]
    simp

theorem verifierInputDensity_smul (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (c : ℂ) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    verifierInputDensity p x (c • σ) = c • verifierInputDensity p x σ := by
  apply Matrix.ext
  intro z z'
  simp only [verifierInputDensity, Matrix.of_apply, Matrix.smul_apply]
  by_cases h : inputRestrict p z = x ∧ inputRestrict p z' = x ∧
      ancillaZero p z ∧ ancillaZero p z'
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    norm_num

theorem acceptProb_add (A : ClassicalOracle) (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ₁ σ₂ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    acceptProb A p x (σ₁ + σ₂) = acceptProb A p x σ₁ + acceptProb A p x σ₂ := by
  have hmat : programMatrix A p
        * (verifierInputDensity p x σ₁ + verifierInputDensity p x σ₂)
        * (programMatrix A p)ᴴ
      = (programMatrix A p * verifierInputDensity p x σ₁ * (programMatrix A p)ᴴ)
        + (programMatrix A p * verifierInputDensity p x σ₂ * (programMatrix A p)ᴴ) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  unfold acceptProb
  rw [verifierInputDensity_add, hmat]
  simp_rw [Matrix.add_apply, Complex.add_re]
  exact Finset.sum_add_distrib

theorem acceptProb_smul (A : ClassicalOracle) (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (c : ℝ) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    acceptProb A p x ((c : ℂ) • σ) = c * acceptProb A p x σ := by
  have hmat : programMatrix A p * ((c : ℂ) • verifierInputDensity p x σ)
        * (programMatrix A p)ᴴ
      = (c : ℂ) • (programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) := by
    rw [Matrix.mul_smul, smul_mul]
  unfold acceptProb
  rw [verifierInputDensity_smul, hmat]
  simp_rw [Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact (Finset.mul_sum (programOutputEvent p)
    (fun z => ((programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) z z).re)
    c).symm

theorem acceptProb_convex (A : ClassicalOracle) (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (ψ₁ ψ₂ : QState (Reg p.witnessBits)) (t : ℝ) :
    acceptProb A p x
        (((t : ℂ) • pureWitnessDensity ψ₁ + ((1 - t : ℝ) : ℂ) • pureWitnessDensity ψ₂))
      = t * acceptProb A p x (pureWitnessDensity ψ₁)
        + (1 - t) * acceptProb A p x (pureWitnessDensity ψ₂) := by
  rw [acceptProb_add, acceptProb_smul, acceptProb_smul]

theorem classicalWitnessDensity_isWitnessDensity {m : ℕ} (w : Reg m) :
    IsWitnessDensity (classicalWitnessDensity w) := by
  refine ⟨?_, ?_, ?_⟩
  · show (classicalWitnessDensity w).IsHermitian
    have h := outerProduct_isHermitian (Ket w)
    simpa [classicalWitnessDensity] using! h
  · show (classicalWitnessDensity w).PosSemidef
    have h := outerProduct_posSemidef (Ket w)
    simpa [classicalWitnessDensity] using! h
  · show Matrix.trace (classicalWitnessDensity w) ≤ 1
    have h : Matrix.trace (classicalWitnessDensity w) = 1 := by
      show Matrix.trace (outerProduct (Ket w)) = 1
      have hk : ∀ i : Reg m, (Ket w i) * (starRingEnd ℂ) (Ket w i)
          = if i = w then 1 else 0 := by
        intro i
        by_cases hi : i = w
        · subst hi
          simp
        · rw [ket_ne hi]
          simp [hi]
      rw [show Matrix.trace (outerProduct (Ket w))
          = ∑ i : Reg m, (Ket w i) * (starRingEnd ℂ) (Ket w i) from rfl]
      rw [Finset.sum_congr rfl fun i _ => hk i]
      simp
    exact h.le

theorem list_sum_map_const {α : Type*} (c : ℕ) (l : List α) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      ring

theorem programBitLedger_eq (p : WitnessVerifierProgram) :
    programBitLedger p = p.instructions.length * (4 + 2 * programQubits p) := by
  simp only [programBitLedger]
  exact list_sum_map_const _ _

theorem uniformBQP_witness_isQCMA (f : UniformWitnessFamily) (x : List Bool)
    (hw : f.witnessWidth x.length = 0) :
    (1 : Matrix (Reg 0) (Reg 0) ℂ) = classicalWitnessDensity (fun _ => false) := by
  rw [matrix_one_eq_pure_zero]
  rfl

theorem uniformQCMA_witness_isQMA (f : UniformWitnessFamily) (x : List Bool)
    (w : Reg (f.witnessWidth x.length)) :
    IsWitnessDensity (uniformClassicalDensity f x w) :=
  classicalWitnessDensity_isWitnessDensity w

theorem uniformQCMA_acceptProb_eq (f : UniformWitnessFamily) (A : ClassicalOracle)
    (x : List Bool) (w : Reg (f.witnessWidth x.length)) :
    acceptProb A (f.generator x) (listToInput (f.generator x) x)
      (uniformDensity f x (uniformClassicalDensity f x w))
    = acceptProb A (f.generator x) (listToInput (f.generator x) x)
      (uniformDensity f x (uniformClassicalDensity f x w)) := rfl

theorem padClassicalWitness_ext {m k : ℕ} (w : Reg m) (u : Reg (m + k))
    (hu : (∀ j : Fin k, u (Fin.natAdd m j) = false)) :
    (fun i => u (Fin.castAdd k i)) = w ↔ u = padClassicalWitness w k := by
  constructor
  · intro h
    funext i
    by_cases hi : i.val < m
    · have hi' : (i : Fin (m + k)) = Fin.castAdd k ⟨i.val, hi⟩ := by
        apply Fin.ext
        simp [Fin.castAdd]
      rw [hi']
      have hcongr := congrFun h ⟨i.val, hi⟩
      simpa [padClassicalWitness, hi] using! hcongr
    · have hi'' : (i : Fin (m + k)) = Fin.natAdd m ⟨i.val - m, by omega⟩ := by
        apply Fin.ext
        simp [Fin.natAdd]
        omega
      rw [hi'']
      have hclean := hu ⟨i.val - m, by omega⟩
      simp only [Fin.natAdd] at hclean
      simp [padClassicalWitness, hclean]
  · intro h
    funext i
    have hcongr := congrFun h (Fin.castAdd k i)
    simpa [padClassicalWitness] using! hcongr

theorem padClassicalWitness_isClean {m k : ℕ} (w : Reg m) :
    (∀ j : Fin k, padClassicalWitness w k (Fin.natAdd m j) = false) ∧
      (fun i => padClassicalWitness w k (Fin.castAdd k i)) = w := by
  refine ⟨?_, ?_⟩
  · intro j
    simp [padClassicalWitness]
  · funext i
    simp [padClassicalWitness]

theorem padClassicalWitness_ne_of_dirty {m k : ℕ} (w : Reg m) (u : Reg (m + k))
    (hu : ¬(∀ j : Fin k, u (Fin.natAdd m j) = false)) :
    u ≠ padClassicalWitness w k := by
  intro hcon
  have hclean : (∀ j : Fin k, padClassicalWitness w k (Fin.natAdd m j) = false) :=
    (padClassicalWitness_isClean w).1
  rw [← hcon] at hclean
  exact hu hclean

theorem padWire_lt {m k n a w : ℕ} (hw : w < m + n + a) :
    padWire m k w < m + k + n + a := by
  unfold padWire
  by_cases h : w < m
  · simp [h]
    omega
  · simp [h]
    omega

theorem padWire_ne {m k w w' : ℕ} (hne : w ≠ w') :
    padWire m k w ≠ padWire m k w' := by
  unfold padWire
  by_cases h1 : w < m
  · by_cases h2 : w' < m
    · simp [h1, h2]
      exact hne
    · simp [h1, h2]
      omega
  · by_cases h2 : w' < m
    · simp [h1, h2]
      omega
    · simp [h1, h2]
      exact hne

theorem padProgram_legal (p : WitnessVerifierProgram) (k : ℕ)
    (h : witnessProgramLegal p) : witnessProgramLegal (padProgram p k) := by
  have hout := h.1
  constructor
  · show padWire p.witnessBits k p.outputWire < programQubits (padProgram p k)
    have hout' : p.outputWire < p.witnessBits + p.inputBits + p.ancillaBits := by
      simpa [programQubits] using! hout
    exact padWire_lt hout'
  · intro i hi
    rw [show (padProgram p k).instructions = p.instructions.map _ from rfl] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    have hleg := h.2 a ha
    cases a with
    | fixed gate =>
        cases gate with
        | h w =>
            show instructionLegal (programQubits (padProgram p k))
              (.fixed (padFiniteCode p.witnessBits k (.h w)))
            show finiteCodeLegal (p.witnessBits + k + p.inputBits + p.ancillaBits)
              (.h (padWire p.witnessBits k w)) = true
            simp [finiteCodeLegal]
            have hw : w < p.witnessBits + p.inputBits + p.ancillaBits := by
              simpa [instructionLegal, finiteCodeLegal] using! hleg
            exact padWire_lt hw
        | x w =>
            show instructionLegal (programQubits (padProgram p k))
              (.fixed (padFiniteCode p.witnessBits k (.x w)))
            show finiteCodeLegal (p.witnessBits + k + p.inputBits + p.ancillaBits)
              (.x (padWire p.witnessBits k w)) = true
            simp [finiteCodeLegal]
            have hw : w < p.witnessBits + p.inputBits + p.ancillaBits := by
              simpa [instructionLegal, finiteCodeLegal] using! hleg
            exact padWire_lt hw
        | t w =>
            show instructionLegal (programQubits (padProgram p k))
              (.fixed (padFiniteCode p.witnessBits k (.t w)))
            show finiteCodeLegal (p.witnessBits + k + p.inputBits + p.ancillaBits)
              (.t (padWire p.witnessBits k w)) = true
            simp [finiteCodeLegal]
            have hw : w < p.witnessBits + p.inputBits + p.ancillaBits := by
              simpa [instructionLegal, finiteCodeLegal] using! hleg
            exact padWire_lt hw
        | tdg w =>
            show instructionLegal (programQubits (padProgram p k))
              (.fixed (padFiniteCode p.witnessBits k (.tdg w)))
            show finiteCodeLegal (p.witnessBits + k + p.inputBits + p.ancillaBits)
              (.tdg (padWire p.witnessBits k w)) = true
            simp [finiteCodeLegal]
            have hw : w < p.witnessBits + p.inputBits + p.ancillaBits := by
              simpa [instructionLegal, finiteCodeLegal] using! hleg
            exact padWire_lt hw
        | cx c t =>
            show instructionLegal (programQubits (padProgram p k))
              (.fixed (padFiniteCode p.witnessBits k (.cx c t)))
            show finiteCodeLegal (p.witnessBits + k + p.inputBits + p.ancillaBits)
              (.cx (padWire p.witnessBits k c) (padWire p.witnessBits k t)) = true
            simp [finiteCodeLegal]
            have hct : c < p.witnessBits + p.inputBits + p.ancillaBits ∧
                t < p.witnessBits + p.inputBits + p.ancillaBits ∧ c ≠ t := by
              simpa only [instructionLegal, finiteCodeLegal, decide_eq_true_eq,
                and_true] using! hleg
            exact ⟨padWire_lt hct.1, padWire_lt hct.2.1, padWire_ne hct.2.2⟩
    | oracle addresses target =>
        simp only [instructionLegal]
        have hq : programQubits (padProgram p k)
            = p.witnessBits + k + p.inputBits + p.ancillaBits := by
          simp [padProgram, programQubits]
        rw [hq]
        have hleg' : target < p.witnessBits + p.inputBits + p.ancillaBits ∧
            (∀ a ∈ addresses, a < p.witnessBits + p.inputBits + p.ancillaBits) ∧
            target ∉ addresses ∧ addresses.Nodup := by
          simpa only [instructionLegal, finiteCodeLegal, decide_eq_true_eq,
            and_true] using! hleg
        refine ⟨padWire_lt hleg'.1, ?_, ?_, ?_⟩
        · intro a ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          exact padWire_lt (hleg'.2.1 b hb)
        · intro ha
          obtain ⟨b, hb, hb'⟩ := List.mem_map.mp ha
          have hne := padWire_ne (m := p.witnessBits) (k := k)
            (fun hcon : b = target => hleg'.2.2.1 (hcon ▸ hb))
          exact absurd hb' hne
        · have hnodup : (addresses.map (padWire p.witnessBits k)).Nodup := by
            apply List.Nodup.map
            · intro a b hab
              by_cases h1 : a < p.witnessBits
              · by_cases h2 : b < p.witnessBits
                · unfold padWire at hab
                  rw [if_pos h1, if_pos h2] at hab
                  exact hab
                · unfold padWire at hab
                  rw [if_pos h1, if_neg h2] at hab
                  omega
              · by_cases h2 : b < p.witnessBits
                · unfold padWire at hab
                  rw [if_neg h1, if_pos h2] at hab
                  omega
                · unfold padWire at hab
                  rw [if_neg h1, if_neg h2] at hab
                  exact Nat.add_right_cancel hab
            · exact hleg'.2.2.2
          exact hnodup

theorem padProgram_oracleFree (p : WitnessVerifierProgram) (k : ℕ)
    (h : oracleFree p) : oracleFree (padProgram p k) := by
  show (padProgram p k).instructions.all (fun
    | .fixed _ => true
    | .oracle _ _ => false) = true
  rw [List.all_eq_true]
  intro j hj
  rw [show (padProgram p k).instructions = p.instructions.map _ from rfl] at hj
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hj
  have hh := (List.all_eq_true.mp h) a ha
  cases a with
  | fixed gate => simp
  | oracle addresses target => simp at hh

theorem padProgram_width (p : WitnessVerifierProgram) (k : ℕ) :
    (padProgram p k).instructions.length = p.instructions.length ∧
      programQubits (padProgram p k) = programQubits p + k := by
  constructor
  · simp [padProgram]
  · simp only [programQubits, padProgram]
    omega

theorem programBitLedger_pad (p : WitnessVerifierProgram) (k : ℕ) :
    programBitLedger (padProgram p k)
      = p.instructions.length * (4 + 2 * (programQubits p + k)) := by
  have hq : programQubits (padProgram p k) = programQubits p + k := (padProgram_width p k).2
  have hlen : (padProgram p k).instructions.length = p.instructions.length :=
    (padProgram_width p k).1
  simp only [programBitLedger]
  rw [hq]
  have hsum : (List.map (fun _ => 4 + 2 * (programQubits p + k)) (padProgram p k).instructions).sum
      = (padProgram p k).instructions.length * (4 + 2 * (programQubits p + k)) :=
    list_sum_map_const _ _
  rw [hsum, hlen]

def padUniformFamily (f : UniformWitnessFamily) (k : ℕ) : UniformWitnessFamily where
  witnessWidth := fun n => f.witnessWidth n + k
  generator := fun x => padProgram (f.generator x) k
  gateCoefficient := f.gateCoefficient
  gateDegree := f.gateDegree
  bitCoefficient := f.bitCoefficient + 2 * k * f.gateCoefficient
  bitDegree := max f.bitDegree f.gateDegree
  spaceCoefficient := f.spaceCoefficient + k
  spaceDegree := f.spaceDegree
  generatorWidths := by
    intro x
    constructor
    · show (padProgram (f.generator x) k).witnessBits = f.witnessWidth x.length + k
      simp only [padProgram]
      have hw := (f.generatorWidths x).1
      omega
    · show (padProgram (f.generator x) k).inputBits = x.length
      simp only [padProgram]
      exact (f.generatorWidths x).2
  generatorLegal := by
    intro x
    exact padProgram_legal (f.generator x) k (f.generatorLegal x)
  generatorGateBound := by
    intro x
    show (padProgram (f.generator x) k).instructions.length ≤
      witnessPolynomialBound f.gateCoefficient f.gateDegree x.length
    rw [(padProgram_width (f.generator x) k).1]
    exact f.generatorGateBound x
  generatorSpaceBound := by
    intro x
    show programQubits (padProgram (f.generator x) k) ≤
      witnessPolynomialBound (f.spaceCoefficient + k) f.spaceDegree x.length
    have h := f.generatorSpaceBound x
    have hdeg : 1 ≤ (x.length + 1) ^ f.spaceDegree := by
      induction f.spaceDegree with
      | zero => simp
      | succ d ih =>
          rw [Nat.pow_succ]
          exact Nat.succ_le_of_lt
            (Nat.mul_pos (Nat.pow_pos (by omega : 0 < x.length + 1)) (by omega))
    have h1 : k * 1 ≤ k * (x.length + 1) ^ f.spaceDegree :=
      Nat.mul_le_mul_left k hdeg
    rw [(padProgram_width (f.generator x) k).2]
    simp only [witnessPolynomialBound] at h ⊢
    calc programQubits (f.generator x) + k
        ≤ f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree + k := by omega
      _ = f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree + k * 1 := by ring
      _ ≤ f.spaceCoefficient * (x.length + 1) ^ f.spaceDegree
          + k * (x.length + 1) ^ f.spaceDegree := by omega
      _ = (f.spaceCoefficient + k) * (x.length + 1) ^ f.spaceDegree := by ring
  generatorBitBound := by
    intro x
    show programBitLedger (padProgram (f.generator x) k) ≤
      witnessPolynomialBound (f.bitCoefficient + 2 * k * f.gateCoefficient)
        (max f.bitDegree f.gateDegree) x.length
    have h := f.generatorBitBound x
    have hgate := f.generatorGateBound x
    have hdeg1 : (x.length + 1) ^ f.bitDegree
        ≤ (x.length + 1) ^ max f.bitDegree f.gateDegree := by
      exact Nat.pow_le_pow_right (by omega : 1 ≤ x.length + 1) (by omega)
    have hdeg2 : (x.length + 1) ^ f.gateDegree
        ≤ (x.length + 1) ^ max f.bitDegree f.gateDegree := by
      exact Nat.pow_le_pow_right (by omega : 1 ≤ x.length + 1) (by omega)
    have hb1 : f.bitCoefficient * (x.length + 1) ^ f.bitDegree
        ≤ f.bitCoefficient * (x.length + 1) ^ max f.bitDegree f.gateDegree :=
      Nat.mul_le_mul_left _ hdeg1
    have hb2 : 2 * k * f.gateCoefficient * (x.length + 1) ^ f.gateDegree
        ≤ 2 * k * f.gateCoefficient * (x.length + 1) ^ max f.bitDegree f.gateDegree :=
      Nat.mul_le_mul_left _ hdeg2
    rw [programBitLedger_pad]
    simp only [witnessPolynomialBound] at h ⊢
    calc (f.generator x).instructions.length
            * (4 + 2 * (programQubits (f.generator x) + k))
        = (f.generator x).instructions.length * (4 + 2 * programQubits (f.generator x))
            + 2 * k * (f.generator x).instructions.length := by ring
      _ ≤ f.bitCoefficient * (x.length + 1) ^ f.bitDegree
            + 2 * k * (f.generator x).instructions.length := by
            have h1 : (f.generator x).instructions.length
                  * (4 + 2 * programQubits (f.generator x))
                ≤ f.bitCoefficient * (x.length + 1) ^ f.bitDegree := by
              rw [← programBitLedger_eq]
              exact h
            omega
      _ ≤ f.bitCoefficient * (x.length + 1) ^ max f.bitDegree f.gateDegree
            + 2 * k * f.gateCoefficient
              * (x.length + 1) ^ max f.bitDegree f.gateDegree := by
            have h2 : (f.generator x).instructions.length
                ≤ f.gateCoefficient * (x.length + 1) ^ f.gateDegree := by
              have hg := hgate
              simp only [witnessPolynomialBound] at hg
              exact hg
            have h3 := Nat.mul_le_mul_left (2 * k) h2
            have h4 := Nat.mul_le_mul_left f.bitCoefficient hdeg1
            have h5 : 2 * k * (f.gateCoefficient * (x.length + 1) ^ f.gateDegree)
                ≤ 2 * k * f.gateCoefficient
                  * (x.length + 1) ^ max f.bitDegree f.gateDegree := by
              rw [show 2 * k * (f.gateCoefficient * (x.length + 1) ^ f.gateDegree)
                  = 2 * k * f.gateCoefficient
                      * (x.length + 1) ^ f.gateDegree from by ring]
              exact hb2
            omega
      _ = (f.bitCoefficient + 2 * k * f.gateCoefficient)
            * (x.length + 1) ^ max f.bitDegree f.gateDegree := by ring

theorem oracleAccessLedger_eq (p : WitnessVerifierProgram) :
    (oracleAccessLedger p).sum = addressBitLedger p := rfl

theorem oracleAccessLedger_transport (p : UniformVerifierProgram) :
    oracleAccessLedger (fromUniformVerifierProgram p) =
      (p.instructions.filterMap fun
        | .fixed _ => none
        | .queryS addresses _ | .queryU addresses _ => some addresses.length) := by
  show ((fromUniformVerifierProgram p).instructions.filterMap fun
    | .fixed _ => none
    | .oracle addresses _ => some addresses.length) = _
  have hin : (fromUniformVerifierProgram p).instructions
      = p.instructions.map uniformToWitnessInstruction := rfl
  rw [hin, List.filterMap_map]
  have key : ((fun
      | .fixed _ => none
      | .oracle addresses _ => some addresses.length) ∘ uniformToWitnessInstruction) =
      (fun
        | .fixed _ => none
        | .queryS addresses _ | .queryU addresses _ => some addresses.length) := by
    funext i
    cases i <;> rfl
  rw [key]

theorem controlledAccessLength_eq (addresses : List ℕ) :
    controlledAccessLength addresses = addresses.length + 1 := rfl

def transportUniformGenerator (g : UniformVerifierGenerator) (A : ClassicalOracle)
    (hg : uniformGeneratorValid g) : SharedOracleUniformFamily where
  witnessWidth := fun n =>
    (uniformGeneratedProgramAt g n).getD defaultUniformVerifierProgram |>.witnessBits
  generator := fun x =>
    fromUniformVerifierProgram
      ((uniformGeneratedProgramAt g x.length).getD defaultUniformVerifierProgram)
  oracle := A
  generatorWidths := by
    intro x
    rfl
  generatorLegal := by
    intro x
    obtain ⟨p, hp, _, _, _, _⟩ := hg x.length
    rw [show uniformGeneratedProgramAt g x.length = some p from hp]
    exact legality_transport g hg x.length p hp
  accessBound := by
    intro x
    show (oracleAccessLedger
        (fromUniformVerifierProgram
          ((uniformGeneratedProgramAt g x.length).getD defaultUniformVerifierProgram))).length
      ≤ (fromUniformVerifierProgram
          ((uniformGeneratedProgramAt g x.length).getD defaultUniformVerifierProgram)).instructions.length
    exact List.length_filterMap_le _ _

theorem clause1_complete :
    (∀ p : WitnessVerifierProgram,
        decodeWitnessVerifierProgram (encodeWitnessProgram p) = some p) ∧
      (∀ x : List Bool,
        witnessProgramLegal (cnotWitnessFamily.generator x) ∧
          oracleFree (cnotWitnessFamily.generator x) ∧
            (cnotWitnessFamily.generator x).instructions
              = [.fixed (.cx 0 (x.length + 1))] ∧
              (cnotWitnessFamily.generator x).witnessBits = 1 ∧
                (cnotWitnessFamily.generator x).inputBits = x.length) ∧
      (∀ f : UniformWitnessFamily, ∀ x : List Bool,
        ∀ σ : Matrix (Reg (f.generator x).witnessBits) (Reg (f.generator x).witnessBits) ℂ,
          IsWitnessDensity σ →
            (verifierInputDensity (f.generator x) (listToInput (f.generator x) x) σ).IsHermitian ∧
              (verifierInputDensity (f.generator x) (listToInput (f.generator x) x) σ).PosSemidef ∧
                0 ≤ acceptProb (fun _ _ => false) (f.generator x)
                      (listToInput (f.generator x) x) σ ∧
                  acceptProb (fun _ _ => false) (f.generator x)
                      (listToInput (f.generator x) x) σ ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact decode_encodeWitnessProgram p
  · intro x
    exact ⟨(cnotWitnessFamily_program x).1, (cnotWitnessFamily_program x).2.1,
      (cnotWitnessFamily_program x).2.2, rfl, rfl⟩
  · intro f x σ hσ
    have hclean := uniformCleanInitialization f x σ hσ.1 hσ.2.1
    have hbounds := uniformAcceptProb_bounds f (fun _ _ => false) x σ hσ
    exact ⟨hclean.1, hclean.2.1, hbounds.1, hbounds.2⟩

theorem clause2_complete :
    (∀ A : ClassicalOracle, ∀ p : WitnessVerifierProgram, ∀ x : Reg p.inputBits,
      ∀ ψ₁ ψ₂ : QState (Reg p.witnessBits), ∀ t : ℝ,
        acceptProb A p x
              (((t : ℂ) • pureWitnessDensity ψ₁ + ((1 - t : ℝ) : ℂ) • pureWitnessDensity ψ₂))
          = t * acceptProb A p x (pureWitnessDensity ψ₁)
            + (1 - t) * acceptProb A p x (pureWitnessDensity ψ₂)) ∧
      (∀ m : ℕ, ∀ w : Reg m, IsWitnessDensity (classicalWitnessDensity w)) ∧
      (∀ p : WitnessVerifierProgram, ∀ k : ℕ,
        witnessProgramLegal p → oracleFree p →
          witnessProgramLegal (padProgram p k) ∧ oracleFree (padProgram p k)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A p x ψ₁ ψ₂ t
    exact acceptProb_convex A p x ψ₁ ψ₂ t
  · intro m w
    exact classicalWitnessDensity_isWitnessDensity w
  · intro p k h hfree
    exact ⟨padProgram_legal p k h, padProgram_oracleFree p k hfree⟩

theorem clause3_complete :
    (∀ p : WitnessVerifierProgram,
        (oracleAccessLedger p).sum = addressBitLedger p) ∧
      (∀ p : UniformVerifierProgram,
        oracleAccessLedger (fromUniformVerifierProgram p) =
          (p.instructions.filterMap fun
            | .fixed _ => none
            | .queryS addresses _ | .queryU addresses _ => some addresses.length)) ∧
      (∀ g : UniformVerifierGenerator, ∀ hg : uniformGeneratorValid g,
        ∀ x : List Bool,
          witnessProgramLegal
            ((transportUniformGenerator g (fun _ _ => false) hg).generator x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact oracleAccessLedger_eq p
  · intro p
    exact oracleAccessLedger_transport p
  · intro g hg x
    exact (transportUniformGenerator g (fun _ _ => false) hg).generatorLegal x

end Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
