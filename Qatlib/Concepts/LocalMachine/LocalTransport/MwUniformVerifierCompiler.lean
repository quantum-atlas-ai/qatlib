/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwActualTwoProjectors
import Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitnessDefs

/-!
# Uniform compilation of alternating verifier measurements

`MwLetter` and `mwWord` describe verifier instruction words interleaved with acceptance and
clean-workspace measurements. `acceptSegment` runs a verifier, measures acceptance, and runs the
inverse instructions, implementing the pulled-back acceptance projector used in the
amplification framework of [MarriottWatrous2005].

The module identifies compiled executions with alternating two-projector states, expresses
record weights in a projector-support basis, and proves word-length and generator-ledger bounds
for uniform witness families.

## Main statements

* `run_acceptSegment`: realize a pulled-back acceptance measurement.
* `compiled_record_mixture`: express outcome-record weights as a finite weighted sum.
* `frontier1`: combine execution, record-weight, and uniform resource statements.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.LocalMachine.LocalTransport.MwUniformVerifierCompiler

open Matrix Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib
open scoped Classical BigOperators
set_option warningAsError false

set_option autoImplicit false
noncomputable section

/-- A verifier-word letter consisting of a witness instruction, an acceptance measurement, or a
clean-workspace measurement. -/
inductive MwLetter where
  | gate (instruction : WitnessInstruction)
  | accept
  | clean
  deriving DecidableEq, Repr

/-- Replace a fixed gate by its adjoint code and retain a classical oracle instruction as its
own inverse. -/
def inverseInstruction : WitnessInstruction → WitnessInstruction
  | .fixed gate => .fixed (finiteCodeAdjoint gate)
  | .oracle addresses target => .oracle addresses target

/-- Reverse an instruction list and replace each instruction by its inverse. -/
def inverseInstructions (instructions : List WitnessInstruction) : List WitnessInstruction :=
  instructions.reverse.map inverseInstruction

/-- The reverse product of the matrices of an instruction list on the verifier workspace. -/
noncomputable def instructionProduct (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (instructions : List WitnessInstruction) : Matrix (Reg (programQubits p)) (Reg (programQubits p)) ℂ :=
  (instructions.map (instructionMatrix A (programQubits p))).reverse.prod

/-- Run the verifier instructions, measure acceptance, and then run the inverse instructions. -/
noncomputable def acceptSegment (p : WitnessVerifierProgram) : List MwLetter :=
  p.instructions.map MwLetter.gate ++ [MwLetter.accept] ++
    (inverseInstructions p.instructions).map MwLetter.gate

/-- The one-letter word measuring the clean-workspace projector. -/
def cleanSegment : List MwLetter := [MwLetter.clean]

/-- Build the specified number of alternating acceptance and clean-measurement segments,
starting with the selected segment type. -/
def alternatingWord (p : WitnessVerifierProgram) (acceptFirst : Bool) : ℕ → List MwLetter
  | 0 => []
  | n + 1 =>
      (if acceptFirst then acceptSegment p else cleanSegment) ++
        alternatingWord p (!acceptFirst) n

/-- The alternating verifier word starting with an acceptance segment. -/
noncomputable def mwWord (p : WitnessVerifierProgram) (rounds : ℕ) : List MwLetter :=
  alternatingWord p true rounds

/-- Execute a verifier word with a prescribed measurement-outcome list, returning the
unnormalized branch state or `none` when the record length is incompatible. -/
noncomputable def runWord (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) : List MwLetter → List Bool →
      QState (Reg (programQubits p)) → Option (QState (Reg (programQubits p)))
  | [], [], ψ => some ψ
  | .gate instruction :: rest, outcomes, ψ =>
      runWord A p x rest outcomes (instructionMatrix A (programQubits p) instruction *ᵥ ψ)
  | .accept :: rest, outcome :: outcomes, ψ =>
      runWord A p x rest outcomes
        (selected (Projector (programOutputEvent p)) outcome *ᵥ ψ)
  | .clean :: rest, outcome :: outcomes, ψ =>
      runWord A p x rest outcomes
        (selected (cleanProjector (witnessEmbed p x)) outcome *ᵥ ψ)
  | _, _, _ => none

/-- The total squared amplitude of a returned branch state, with value zero for a failed
execution. -/
noncomputable def runRecordProbability {H : Type} [Fintype H] [DecidableEq H] :
    Option (QState H) → ℝ
  | none => 0
  | some ψ => MeasureProb ψ Finset.univ

/-- For a legal instruction, the matrix of its inverse instruction is its conjugate transpose. -/
theorem inverseInstruction_spec (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (instruction : WitnessInstruction)
    (hlegal : instructionLegal (programQubits p) instruction) :
    instructionMatrix A (programQubits p) (inverseInstruction instruction) =
      (instructionMatrix A (programQubits p) instruction)ᴴ := by
  cases instruction with
  | fixed gate =>
      exact (finiteCodeAdjoint_spec (programQubits p) gate hlegal).2
  | oracle addresses target =>
      exact (xorQueryMatrix_selfAdjoint A (programQubits p) addresses target hlegal).symm

/-- The conjugate transpose of a matrix-list product is the product of the reversed list of
conjugate transposes. -/
private theorem conjTranspose_list_prod {H : Type} [Fintype H] [DecidableEq H]
    (xs : List (Matrix H H ℂ)) : xs.prodᴴ = (xs.reverse.map fun x => xᴴ).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.prod_cons, Matrix.conjTranspose_mul, List.reverse_cons,
        List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one, ih]

/-- For a list of legal instructions, the inverse list has matrix product equal to the conjugate
transpose of the original product. -/
theorem inverseInstructions_spec (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (instructions : List WitnessInstruction)
    (hlegal : ∀ instruction ∈ instructions, instructionLegal (programQubits p) instruction) :
    instructionProduct A p (inverseInstructions instructions) =
      (instructionProduct A p instructions)ᴴ := by
  simp only [instructionProduct, inverseInstructions, List.map_map, List.map_reverse,
    List.reverse_reverse, Function.comp_def, conjTranspose_list_prod]
  apply congrArg List.prod
  apply List.map_congr_left
  intro instruction hi
  exact inverseInstruction_spec A p instruction (hlegal instruction hi)

/-- Selecting either outcome of a pulled-back acceptance projector equals conjugating the
corresponding output-event projector by the unitary. -/
theorem selected_pulledAccept {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (S : Finset H) (hU : U ∈ unitaryGroup H ℂ) (outcome : Bool) :
    selected (pulledAccept U S) outcome = Uᴴ * selected (Projector S) outcome * U := by
  have hleft : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  cases outcome with
  | false =>
      simp only [selected, Bool.false_eq_true, if_false, pulledAccept]
      calc
        1 - Uᴴ * Projector S * U = Uᴴ * U - Uᴴ * Projector S * U := by rw [hleft]
        _ = Uᴴ * (1 - Projector S) * U := by noncomm_ring
  | true => simp [selected, pulledAccept]

/-- Executing a consecutive block of gate letters applies its instruction product before
continuing with the remaining word. -/
theorem run_gateBlock (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (instructions : List WitnessInstruction)
    (tail : List MwLetter) (outcomes : List Bool) (ψ : QState (Reg (programQubits p))) :
    runWord A p x (instructions.map MwLetter.gate ++ tail) outcomes ψ =
      runWord A p x tail outcomes (instructionProduct A p instructions *ᵥ ψ) := by
  induction instructions generalizing ψ with
  | nil => simp [instructionProduct]
  | cons instruction rest ih =>
      simp only [List.map_cons, List.cons_append, runWord]
      rw [ih]
      simp [instructionProduct, Matrix.mulVec_mulVec]

/-- For a legal verifier, executing an acceptance segment applies the selected outcome of the
pulled-back acceptance projector before the remaining word. -/
theorem run_acceptSegment (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (hlegal : witnessProgramLegal p)
    (tail : List MwLetter) (outcome : Bool) (outcomes : List Bool)
    (ψ : QState (Reg (programQubits p))) :
    runWord A p x (acceptSegment p ++ tail) (outcome :: outcomes) ψ =
      runWord A p x tail outcomes
        (selected (pulledAccept (programMatrix A p) (programOutputEvent p)) outcome *ᵥ ψ) := by
  simp only [acceptSegment, List.append_assoc]
  rw [run_gateBlock]
  simp only [List.singleton_append, runWord]
  rw [run_gateBlock]
  rw [inverseInstructions_spec A p p.instructions hlegal.2]
  rw [selected_pulledAccept (programMatrix A p) (programOutputEvent p)
    (programMatrix_unitary A p) outcome]
  simp only [programMatrix, instructionProduct, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Encoding a measurement record with `outcomeRecord` preserves its length. -/
theorem outcomeRecord_length (previous : Bool) (outcomes : List Bool) :
    (outcomeRecord previous outcomes).length = outcomes.length := by
  induction outcomes generalizing previous with
  | nil => rfl
  | cons outcome rest ih => simp [outcomeRecord, ih]

/-- For a legal verifier and an outcome list of the prescribed length, the alternating word
returns the corresponding alternating two-projector state. -/
theorem run_alternatingWord (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (hlegal : witnessProgramLegal p) :
    ∀ (acceptFirst previous : Bool) (rounds : ℕ) (outcomes : List Bool)
      (ψ : QState (Reg (programQubits p))), outcomes.length = rounds →
      runWord A p x (alternatingWord p acceptFirst rounds) outcomes ψ =
        some (alternatingState
          (if acceptFirst then pulledAccept (programMatrix A p) (programOutputEvent p)
            else cleanProjector (witnessEmbed p x))
          (if acceptFirst then cleanProjector (witnessEmbed p x)
            else pulledAccept (programMatrix A p) (programOutputEvent p))
          previous outcomes ψ) := by
  intro acceptFirst previous rounds
  induction rounds generalizing acceptFirst previous with
  | zero =>
      intro outcomes ψ hlength
      have ho : outcomes = [] := List.length_eq_zero_iff.mp hlength
      subst outcomes
      cases acceptFirst <;> rfl
  | succ rounds ih =>
      intro outcomes ψ hlength
      cases outcomes with
      | nil => simp at hlength
      | cons outcome outcomes =>
          have hlength' : outcomes.length = rounds := by simpa using! hlength
          cases acceptFirst with
          | false =>
              simp only [alternatingWord, Bool.not_false, cleanSegment, alternatingState]
              exact ih true outcome outcomes _ hlength'
          | true =>
              simp only [alternatingWord, Bool.not_true, if_true, alternatingState]
              rw [run_acceptSegment A p x hlegal]
              exact ih false outcome outcomes _ hlength'

/-- Executing `mwWord` with a record of length `rounds` gives the alternating state of the
pulled-back acceptance and clean-workspace projectors. -/
theorem run_mwWord (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (hlegal : witnessProgramLegal p)
    (rounds : ℕ) (outcomes : List Bool) (ψ : QState (Reg (programQubits p)))
    (hlength : outcomes.length = rounds) :
    runWord A p x (mwWord p rounds) outcomes ψ =
      some (alternatingState (pulledAccept (programMatrix A p) (programOutputEvent p))
        (cleanProjector (witnessEmbed p x)) true outcomes ψ) := by
  exact run_alternatingWord A p x hlegal true true rounds outcomes ψ hlength

/-- The record weight of a compiled verifier execution equals the total squared amplitude of its
alternating two-projector state. -/
theorem run_mwRecordProbability (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (hlegal : witnessProgramLegal p)
    (rounds : ℕ) (outcomes : List Bool) (ψ : QState (Reg (programQubits p)))
    (hlength : outcomes.length = rounds) :
    runRecordProbability (runWord A p x (mwWord p rounds) outcomes ψ) =
      MeasureProb (alternatingState (pulledAccept (programMatrix A p) (programOutputEvent p))
        (cleanProjector (witnessEmbed p x)) true outcomes ψ) Finset.univ := by
  rw [run_mwWord A p x hlegal rounds outcomes ψ hlength, runRecordProbability]

/-- An acceptance segment has twice the verifier instruction length plus one measurement letter. -/
theorem acceptSegment_length (p : WitnessVerifierProgram) :
    (acceptSegment p).length = 2 * p.instructions.length + 1 := by
  simp [acceptSegment, inverseInstructions, Nat.two_mul]
  omega

/-- An alternating word of `rounds` segments has length at most `(2 * p.instructions.length + 2)
* rounds`. -/
theorem alternatingWord_length_le (p : WitnessVerifierProgram) (acceptFirst : Bool) (rounds : ℕ) :
    (alternatingWord p acceptFirst rounds).length ≤
      (2 * p.instructions.length + 2) * rounds := by
  induction rounds generalizing acceptFirst with
  | zero => simp [alternatingWord]
  | succ rounds ih =>
      simp only [alternatingWord, List.length_append]
      cases acceptFirst with
      | false =>
          simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, cleanSegment,
            List.length_singleton]
          rw [Nat.mul_succ]
          have h := ih true
          omega
      | true =>
          simp only [Bool.not_true, if_true, acceptSegment_length]
          rw [Nat.mul_succ]
          have h := ih false
          omega

/-- The Marriott-Watrous word has length at most `(2 * p.instructions.length + 2) * rounds`. -/
theorem mwWord_length_le (p : WitnessVerifierProgram) (rounds : ℕ) :
    (mwWord p rounds).length ≤ (2 * p.instructions.length + 2) * rounds := by
  exact alternatingWord_length_le p true rounds

/-- A uniform family's compiled verifier word obeys the stated polynomial length bound in input
length plus measurement rounds. -/
theorem uniform_word_length (f : UniformWitnessFamily) (x : List Bool) (rounds : ℕ) :
    (mwWord (f.generator x) rounds).length ≤
      witnessPolynomialBound (2 * f.gateCoefficient + 2) (f.gateDegree + 1)
        (x.length + rounds) := by
  have hlength := mwWord_length_le (f.generator x) rounds
  have hgates := f.generatorGateBound x
  simp only [witnessPolynomialBound] at hgates ⊢
  let B := x.length + rounds + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hr : rounds ≤ B := by dsimp [B]; omega
  have hn : x.length + 1 ≤ B := by dsimp [B]; omega
  have hm : (f.generator x).instructions.length ≤ f.gateCoefficient * B ^ f.gateDegree := by
    exact hgates.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn f.gateDegree))
  have hpow : B ≤ B ^ (f.gateDegree + 1) := Nat.le_pow (by omega)
  calc
    (mwWord (f.generator x) rounds).length
        ≤ (2 * (f.generator x).instructions.length + 2) * rounds := hlength
    _ ≤ (2 * (f.generator x).instructions.length + 2) * B :=
      Nat.mul_le_mul_left _ hr
    _ ≤ (2 * (f.gateCoefficient * B ^ f.gateDegree) + 2) * B := by
      exact Nat.mul_le_mul_right _ (by omega)
    _ = 2 * f.gateCoefficient * B ^ (f.gateDegree + 1) + 2 * B := by
      rw [Nat.pow_succ]
      ring
    _ ≤ 2 * f.gateCoefficient * B ^ (f.gateDegree + 1) + 2 * B ^ (f.gateDegree + 1) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpow) _
    _ = (2 * f.gateCoefficient + 2) * B ^ (f.gateDegree + 1) := by ring

/-- The generated verifier's bit ledger obeys the family's polynomial bound evaluated at input
length plus measurement rounds. -/
theorem uniform_generator_clock (f : UniformWitnessFamily) (x : List Bool) (rounds : ℕ) :
    programBitLedger (f.generator x) ≤
      witnessPolynomialBound f.bitCoefficient f.bitDegree (x.length + rounds) := by
  have hclock := f.generatorBitBound x
  simp only [witnessPolynomialBound] at hclock ⊢
  exact hclock.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega : x.length + 1 ≤ x.length + rounds + 1) f.bitDegree))

/-- For a legal verifier, an isometric basis of the clean-projector range gives each encoded
outcome-record weight as a finite sum of squared basis amplitudes times `recordWeight`
factors. -/
theorem compiled_record_mixture (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (hlegal : witnessProgramLegal p) (rounds : ℕ) :
    let E := witnessEmbed p x
    let Q := cleanProjector E
    ∃ (B : Matrix (Reg (programQubits p))
      (CSProjectorSupport Q (cleanProjector_projector E (witnessEmbed_conjTranspose_mul p x))) ℂ)
      (t : CSProjectorSupport Q (cleanProjector_projector E
        (witnessEmbed_conjTranspose_mul p x)) → ℝ),
      (∀ j, t j ∈ Set.Icc 0 1) ∧ Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B ∧ B * Bᴴ = Q ∧
      (∀ (w : QState (Reg p.witnessBits)) (z : List Bool), z.length = rounds →
        runRecordProbability (runWord A p x (mwWord p rounds) (outcomeRecord true z) (E *ᵥ w)) =
          ∑ j, ‖(Bᴴ *ᵥ (E *ᵥ w)) j‖ ^ 2 * recordWeight (t j) z) ∧
      (∀ ψ : QState (Reg (programQubits p)),
        ∃ w : QState (Reg p.witnessBits), Q *ᵥ ψ = E *ᵥ w) := by
  (try dsimp only)
  let U := programMatrix A p
  let E := witnessEmbed p x
  let Q := cleanProjector E
  have hU : U ∈ unitaryGroup (Reg (programQubits p)) ℂ := programMatrix_unitary A p
  have hE : Eᴴ * E = 1 := witnessEmbed_conjTranspose_mul p x
  obtain ⟨B, t, ht, hB, hBQ, hlaw, hclean⟩ :=
    Qatlib.Concepts.QueryComplexity.DegreeMethod.MwActualTwoProjectors.frontier1
      U (programOutputEvent p) E hU hE
  refine ⟨B, t, ht, hB, hBQ, ?_, hclean⟩
  intro w z hlength
  have hrun := run_mwWord A p x hlegal rounds (outcomeRecord true z) (E *ᵥ w)
    (by rw [outcomeRecord_length, hlength])
  rw [hrun]
  exact hlaw w z

/-- For a uniform witness family, combine the compiled alternating-measurement semantics,
projector-support record-weight formula, and polynomial word and ledger bounds. The
alternating verifier construction follows the framework of [MarriottWatrous2005]. -/
theorem frontier1 (f : UniformWitnessFamily) (A : ClassicalOracle)
    (x : List Bool) (rounds : ℕ) :
    let p := f.generator x
    let input := listToInput p x
    let U := programMatrix A p
    let E := witnessEmbed p input
    let P := pulledAccept U (programOutputEvent p)
    let Q := cleanProjector E
    (∀ (w : QState (Reg p.witnessBits)) (z : List Bool), z.length = rounds →
      runWord A p input (mwWord p rounds) z (E *ᵥ w) =
        some (alternatingState P Q true z (E *ᵥ w))) ∧
    (∃ (B : Matrix (Reg (programQubits p))
      (CSProjectorSupport Q (cleanProjector_projector E
        (witnessEmbed_conjTranspose_mul p input))) ℂ)
      (t : CSProjectorSupport Q (cleanProjector_projector E
        (witnessEmbed_conjTranspose_mul p input)) → ℝ),
      (∀ j, t j ∈ Set.Icc 0 1) ∧ Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B ∧ B * Bᴴ = Q ∧
      (∀ (w : QState (Reg p.witnessBits)) (z : List Bool), z.length = rounds →
        runRecordProbability (runWord A p input (mwWord p rounds) (outcomeRecord true z) (E *ᵥ w)) =
          ∑ j, ‖(Bᴴ *ᵥ (E *ᵥ w)) j‖ ^ 2 * recordWeight (t j) z) ∧
      (∀ ψ : QState (Reg (programQubits p)),
        ∃ w : QState (Reg p.witnessBits), Q *ᵥ ψ = E *ᵥ w)) ∧
    ((mwWord p rounds).length ≤
      witnessPolynomialBound (2 * f.gateCoefficient + 2) (f.gateDegree + 1)
        (x.length + rounds)) ∧
    (programBitLedger p ≤
      witnessPolynomialBound f.bitCoefficient f.bitDegree (x.length + rounds)) := by
  (try dsimp only)
  refine ⟨?_,?_,?_,?_⟩
  · intro w z hlength
    exact run_mwWord A (f.generator x) (listToInput (f.generator x) x)
      (f.generatorLegal x) rounds z (witnessEmbed (f.generator x) (listToInput (f.generator x) x) *ᵥ w)
      hlength
  · exact compiled_record_mixture A (f.generator x) (listToInput (f.generator x) x)
      (f.generatorLegal x) rounds
  · exact uniform_word_length f x rounds
  · exact uniform_generator_clock f x rounds

end
end Qatlib.Concepts.LocalMachine.LocalTransport.MwUniformVerifierCompiler
