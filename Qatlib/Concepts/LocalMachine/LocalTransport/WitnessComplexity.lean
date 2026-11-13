/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
import Lean
import Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationSepa

/-!
# Witness verifier semantics and transport

Witness verifiers are interpreted as unitary matrices with clean classical input and ancilla
initialization. `witnessEmbed` identifies the witness subspace, while `acceptProb_born`,
`acceptProb_nonneg`, and `acceptProb_le_one` relate density-matrix acceptance to Born
probabilities and their bounds. Quantum-proof background is given in [MarriottWatrous2005].

The module also verifies concrete empty and single-X programs and transports uniform verifier
instructions to the witness model. Controlled XOR queries are represented by appending a control
bit to the oracle address.

## Main statements

* `g1`: initialization, acceptance semantics, probability bounds, and concrete verifier
  examples.
* `controlledXor_eq_appended`: controlled access as a query to the appended-control oracle.
* `g3`: oracle access identities and uniform-program transport properties.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationSepa

namespace Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity

open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025
open Matrix
open scoped ComplexOrder

/-- Reads a Boolean tape prefix up to its first blank, returning no result if the fuel bound is
exceeded. -/
def modelReadOutput : (fuel : ℕ) → (tape : Turing.ListBlank (Option Bool)) → Option (List Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.readOutputUntilBlank").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

/-- Encodes `n` as a tape input consisting of `n` copies of `some true`. -/
def modelUnaryInput : (n : ℕ) → List (Option Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.unaryInput").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

/-- Returns the polynomial time allowance for generating the verifier at input length `n`. -/
def modelGenFuel : (f : WitnessVerifierFamily) → (n : ℕ) → ℕ := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.generatorFuel").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

/-- Runs a Turing machine for at most the given number of transitions and returns its halted
configuration when one is reached. -/
def modelRunHalt : {k : ℕ} → Turing.TM0.Machine (Option Bool) (Fin (k + 1)) → ℕ → Turing.TM0.Cfg (Option Bool) (Fin (k + 1)) → Option (Turing.TM0.Cfg (Option Bool) (Fin (k + 1))) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.runUntilHaltWithin").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

/-- Executes a list of uniform verifier instructions using the two supplied Boolean oracles. -/
noncomputable def uniformRunInstr : (S U : ∀ ell, Reg ell → Bool) → (q : ℕ) → List UniformVerifierInstruction → QState (Reg q) → QState (Reg q) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.WalshMoment.Forrelation.UniformVerifierDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.WalshMoment.Forrelation.runUniformInstructions").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

/-- Returns the matrix of a uniform verifier instruction on `q` qubits with the supplied
oracles. -/
noncomputable def uniformInstrMatrix : (q : ℕ) → (S U : ∀ ell, Reg ell → Bool) → UniformVerifierInstruction → Matrix (Reg q) (Reg q) ℂ := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.WalshMoment.Forrelation.UniformVerifierDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.WalshMoment.Forrelation.uniformInstructionMatrix").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

/-- Requires in-range, distinct address wires and an in-range target outside the address list. -/
def modelQueryLegal : (q : ℕ) → (addresses : List ℕ) → (target : ℕ) → Prop := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.WalshMoment.Forrelation.UniformVerifierDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.WalshMoment.Forrelation.queryDescriptionLegal").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

/-- An all-true bitstring of length `n` decodes to the empty verifier with no witness, `n` input
bits, and one ancilla. -/
theorem decode_allTrue (n : ℕ) : decodeWitnessVerifierProgram (List.replicate n true) =
    some ⟨0, n, 1, 0, []⟩ := by
  unfold decodeWitnessVerifierProgram
  simp

/-- Reading a unary tape with fuel `n + 1` returns the list of `n` true bits. -/
theorem modelReadOutput_unary (n : ℕ) :
    modelReadOutput (n + 1) (Turing.ListBlank.mk (List.replicate n (some true))) =
      some (List.replicate n true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have step : modelReadOutput (n + 2)
        (Turing.ListBlank.mk (some true :: List.replicate n (some true))) =
        (modelReadOutput (n + 1) (Turing.ListBlank.mk (List.replicate n (some true)))).map
          (true :: ·) := rfl
    rw [show List.replicate (n + 1) (some true) = some true :: List.replicate n (some true) from rfl,
      show List.replicate (n + 1) true = true :: List.replicate n true from rfl, step, ih]
    rfl

/-- At length `n`, `zeroVerifierFamily` generates the empty verifier with no witness, `n` input
bits, and one ancilla. -/
theorem zeroVerifierFamily_program (n : ℕ) :
    witnessProgramAt zeroVerifierFamily n = some ⟨0, n, 1, 0, []⟩ := by
  have hf : modelGenFuel zeroVerifierFamily n = 0 := by
    show (0 : ℕ) * (n + 1) ^ 1 = 0
    exact Nat.zero_mul _
  have hrun : modelRunHalt zeroVerifierFamily.machine (modelGenFuel zeroVerifierFamily n)
      (Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (modelUnaryInput n))
      = some (Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (modelUnaryInput n)) := by
    rw [hf]
    rfl
  have h1 : (Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (modelUnaryInput n)).Tape.right₀
      = Turing.ListBlank.mk (List.replicate n (some true)) := by
    simp only [Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_right₀]
    rfl
  have hread : modelReadOutput (n + modelGenFuel zeroVerifierFamily n + 1)
      ((Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (modelUnaryInput n)).Tape.right₀)
      = some (List.replicate n true) := by
    rw [hf, h1]
    exact modelReadOutput_unary n
  have hdec : decodeWitnessVerifierProgram (List.replicate n true) = some ⟨0, n, 1, 0, []⟩ :=
    decode_allTrue n
  have hall :
      (modelRunHalt zeroVerifierFamily.machine (modelGenFuel zeroVerifierFamily n)
        (Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (modelUnaryInput n))).bind
        (fun cfg => (modelReadOutput (n + modelGenFuel zeroVerifierFamily n + 1)
          cfg.Tape.right₀).bind decodeWitnessVerifierProgram)
      = some ⟨0, n, 1, 0, []⟩ := by
    rw [hrun]
    change (modelReadOutput (n + modelGenFuel zeroVerifierFamily n + 1)
      ((Turing.TM0.init (Γ := Option Bool) (Λ := Fin 1) (modelUnaryInput n)).Tape.right₀)).bind
      decodeWitnessVerifierProgram = some ⟨0, n, 1, 0, []⟩
    rw [hread]
    exact hdec
  exact hall

/-- The immediately halting verifier generator satisfies `witnessFamilyValid`. -/
theorem zeroVerifierFamily_valid : witnessFamilyValid zeroVerifierFamily := by
  intro n
  refine ⟨⟨0, n, 1, 0, []⟩, zeroVerifierFamily_program n, rfl, ?_, ?_, ?_⟩
  · show programQubits ⟨0, n, 1, 0, []⟩ ≤
      witnessPolynomialBound zeroVerifierFamily.programCoefficient
        zeroVerifierFamily.programDegree n
    show (0 + n + 1 : ℕ) ≤ 1 * (n + 1) ^ 1
    simp
  · show (List.nil : List WitnessInstruction).length ≤
      witnessPolynomialBound zeroVerifierFamily.programCoefficient
        zeroVerifierFamily.programDegree n
    show (0 : ℕ) ≤ 1 * (n + 1) ^ 1
    simp
  · refine ⟨?_, ?_⟩
    · show 0 < programQubits ⟨0, n, 1, 0, []⟩
      show (0:ℕ) < 0 + n + 1
      omega
    · intro i hi
      simp at hi

/-- Combines the explicit generated program of `zeroVerifierFamily` with validity of the family. -/
theorem zeroVerifierFamily_at (n : ℕ) :
    witnessProgramAt zeroVerifierFamily n = some ⟨0, n, 1, 0, []⟩ ∧
      witnessFamilyValid zeroVerifierFamily :=
  ⟨zeroVerifierFamily_program n, zeroVerifierFamily_valid⟩

/-- Updating a target wire outside the address list leaves the extracted address unchanged. -/
theorem readAddress_update {q : ℕ} (x : Reg q) (addresses : List ℕ) (target : ℕ)
    (htarget : target < q) (haddr : ∀ a ∈ addresses, a < q) (hdisjoint : target ∉ addresses)
    (b : Bool) :
    readAddress (Function.update x ⟨target, htarget⟩ b) addresses haddr =
      readAddress x addresses haddr := by
  funext i
  have hne : addresses.get i ≠ target := fun he => hdisjoint (by rw [← he]; exact List.get_mem _ _)
  have hneFin : (⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩ : Fin q) ≠
      ⟨target, htarget⟩ := fun he => hne (congrArg Fin.val he)
  show Function.update x ⟨target, htarget⟩ b
    ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩ =
      x ⟨addresses.get i, haddr _ (List.get_mem addresses i)⟩
  rw [Function.update_of_ne hneFin]

/-- An XOR oracle update is involutive when the target is distinct from all address wires. -/
theorem xorQueryUpdate_involutive {q : ℕ} (A : ClassicalOracle) (addresses : List ℕ)
    (target : ℕ) (htarget : target < q) (haddr : ∀ a ∈ addresses, a < q)
    (hdisjoint : target ∉ addresses) :
    Function.Involutive (xorQueryUpdate A addresses target htarget haddr) := by
  intro x
  funext i
  by_cases hi : i = ⟨target, htarget⟩
  · subst hi
    simp only [xorQueryUpdate, Function.update_self]
    rw [readAddress_update x addresses target htarget haddr hdisjoint
      (x ⟨target, htarget⟩ ^^ A addresses.length (readAddress x addresses haddr))]
    simp
  · simp [xorQueryUpdate, Function.update, hi]

/-- The XOR oracle query matrix is unitary for a legal query. -/
theorem xorQueryMatrix_unitary (A : ClassicalOracle) (q : ℕ) (addresses : List ℕ)
    (target : ℕ) (h : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup) :
    xorQueryMatrix A q addresses target ∈ unitaryGroup (Reg q) ℂ := by
  classical
  simp only [xorQueryMatrix, dif_pos h]
  exact permMatrix_unitary
    (xorQueryUpdate_involutive A addresses target h.1 h.2.1 h.2.2.1)

/-- The XOR oracle query matrix is self-adjoint for a legal query. -/
theorem xorQueryMatrix_selfAdjoint (A : ClassicalOracle) (q : ℕ) (addresses : List ℕ)
    (target : ℕ) (h : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup) :
    (xorQueryMatrix A q addresses target)ᴴ = xorQueryMatrix A q addresses target := by
  classical
  simp only [xorQueryMatrix, dif_pos h]
  exact permMatrix_conjTranspose
    (xorQueryUpdate_involutive A addresses target h.1 h.2.1 h.2.2.1)

/-- Every witness instruction has a unitary matrix, including the identity interpretation of
illegal query descriptions. -/
theorem instructionMatrix_unitary (A : ClassicalOracle) (q : ℕ) (i : WitnessInstruction) :
    instructionMatrix A q i ∈ unitaryGroup (Reg q) ℂ := by
  cases i with
  | fixed gate =>
    unfold instructionMatrix
    cases gate with
    | h w =>
      by_cases hw : w < q
      · simp [finiteCodeMatrix, hw]
        exact wireGate_unitary q ⟨w, hw⟩ Hadamard hadamard_unitary
      · simp [finiteCodeMatrix, hw]
    | x w =>
      by_cases hw : w < q
      · simp [finiteCodeMatrix, hw]
        exact wireGate_unitary q ⟨w, hw⟩ PauliX pauliX_unitary
      · simp [finiteCodeMatrix, hw]
    | t w =>
      by_cases hw : w < q
      · simp [finiteCodeMatrix, hw]
        exact wireGate_unitary q ⟨w, hw⟩ tGate tGate_mem_unitary
      · simp [finiteCodeMatrix, hw]
    | tdg w =>
      by_cases hw : w < q
      · simp [finiteCodeMatrix, hw]
        exact wireGate_unitary q ⟨w, hw⟩ tGateAdj tGateAdj_mem_unitary
      · simp [finiteCodeMatrix, hw]
    | cx c t =>
      by_cases hct : c < q ∧ t < q ∧ c ≠ t
      · simp [finiteCodeMatrix, hct]
        have hne : (⟨c, hct.1⟩ : Fin q) ≠ ⟨t, hct.2.1⟩ := fun hh => hct.2.2 (congrArg Fin.val hh)
        exact cnotGate_unitary q ⟨c, hct.1⟩ ⟨t, hct.2.1⟩ hne
      · simp [finiteCodeMatrix, hct]
  | oracle addresses target =>
    by_cases h : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup
    · simpa [instructionMatrix] using xorQueryMatrix_unitary A q addresses target h
    · simp only [instructionMatrix, xorQueryMatrix]
      rw [dif_neg h]
      exact Submonoid.one_mem (Matrix.unitaryGroup (Reg q) ℂ)

/-- The matrix of every witness verifier program is unitary. -/
theorem programMatrix_unitary (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    programMatrix A p ∈ unitaryGroup (Reg (programQubits p)) ℂ := by
  unfold programMatrix
  induction p.instructions with
  | nil => exact Submonoid.one_mem (Matrix.unitaryGroup (Reg (programQubits p)) ℂ)
  | cons i rest ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one]
    exact Submonoid.mul_mem (Matrix.unitaryGroup (Reg (programQubits p)) ℂ) ih
      (instructionMatrix_unitary A (programQubits p) i)

/-- Multiplying a verifier program matrix on the left by its adjoint gives the identity. -/
theorem conjTranspose_programMatrix_mul_self (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    (programMatrix A p)ᴴ * programMatrix A p = 1 := by
  have h := programMatrix_unitary A p
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose] at h
  exact h

/-- Multiplying a verifier program matrix on the right by its adjoint gives the identity. -/
theorem programMatrix_mul_conjTranspose_self (A : ClassicalOracle) (p : WitnessVerifierProgram) :
    programMatrix A p * (programMatrix A p)ᴴ = 1 := by
  have h := programMatrix_unitary A p
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose] at h
  exact h

/-- Combines a witness register and a fixed classical input into a full configuration with zero
ancillas. -/
def embedConfig (p : WitnessVerifierProgram) (x : Reg p.inputBits) (w : Reg p.witnessBits) :
    Reg (programQubits p) := fun i =>
  if h : i.val < p.witnessBits then w ⟨i.val, h⟩
  else if h2 : i.val < p.witnessBits + p.inputBits then
    x ⟨i.val - p.witnessBits, by omega⟩
  else false

/-- Restricting an embedded configuration to its witness wires recovers the witness. -/
theorem witnessRestrict_embedConfig (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (w : Reg p.witnessBits) : witnessRestrict p (embedConfig p x w) = w := by
  funext i
  simp only [witnessRestrict, witnessWire, embedConfig]
  rw [dif_pos i.isLt]

/-- Restricting an embedded configuration to its input wires recovers the input. -/
theorem inputRestrict_embedConfig (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (w : Reg p.witnessBits) : inputRestrict p (embedConfig p x w) = x := by
  funext i
  simp only [inputRestrict, inputWire, embedConfig]
  rw [dif_neg]
  · rw [dif_pos]
    · simp
    · omega
  · omega

/-- Every embedded configuration has all ancilla wires set to false. -/
theorem ancillaZero_embedConfig (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (w : Reg p.witnessBits) : ancillaZero p (embedConfig p x w) := by
  intro i
  simp only [ancillaWire, embedConfig]
  rw [dif_neg, dif_neg]
  all_goals omega

/-- For a fixed input, the embedding of witness configurations is injective. -/
theorem embedConfig_injective (p : WitnessVerifierProgram) (x : Reg p.inputBits) :
    Function.Injective (embedConfig p x) := by
  intro w w' h
  have := congrArg (witnessRestrict p) h
  simpa [witnessRestrict_embedConfig] using this

/-- A configuration with the prescribed input and zero ancillas is the embedding of its witness
restriction. -/
theorem eq_embedConfig_of_clean (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (h : inputRestrict p z = x ∧ ancillaZero p z) :
    z = embedConfig p x (witnessRestrict p z) := by
  funext i
  have hq : (i : ℕ) < p.witnessBits + p.inputBits + p.ancillaBits := by
    simpa [programQubits] using i.isLt
  by_cases hi : i.val < p.witnessBits
  · simp only [embedConfig, dif_pos hi]
    rfl
  · by_cases hj : i.val < p.witnessBits + p.inputBits
    · have hlt : p.witnessBits + (i.val - p.witnessBits) < programQubits p := by
        simp only [programQubits]
        omega
      have hval : p.witnessBits + (i.val - p.witnessBits) = i.val := by omega
      have key : (⟨p.witnessBits + (i.val - p.witnessBits), hlt⟩ : Fin (programQubits p)) = i :=
        Fin.eq_of_val_eq (show (⟨p.witnessBits + (i.val - p.witnessBits), hlt⟩ :
          Fin (programQubits p)).val = i.val from hval)
      have hx := congrArg (fun t : Reg p.inputBits =>
        t ⟨i.val - p.witnessBits, by omega⟩) h.1
      simp only [inputRestrict, inputWire] at hx
      have hxi : z i = x ⟨i.val - p.witnessBits, by omega⟩ :=
        calc z i = z ⟨p.witnessBits + (i.val - p.witnessBits), hlt⟩ := (congrArg z key).symm
          _ = x ⟨i.val - p.witnessBits, by omega⟩ := hx
      simp only [embedConfig, dif_neg hi, dif_pos hj]
      exact hxi
    · have hlt : p.witnessBits + p.inputBits + (i.val - (p.witnessBits + p.inputBits))
          < programQubits p := by
        simp only [programQubits]
        omega
      have hval : p.witnessBits + p.inputBits + (i.val - (p.witnessBits + p.inputBits)) = i.val := by
        omega
      have key :
          (⟨p.witnessBits + p.inputBits + (i.val - (p.witnessBits + p.inputBits)), hlt⟩ :
            Fin (programQubits p)) = i :=
        Fin.eq_of_val_eq
          (show (⟨p.witnessBits + p.inputBits + (i.val - (p.witnessBits + p.inputBits)), hlt⟩ :
            Fin (programQubits p)).val = i.val from hval)
      have haz := h.2 ⟨i.val - (p.witnessBits + p.inputBits), by omega⟩
      simp only [ancillaWire] at haz
      have hzi : z i = false :=
        calc z i = z ⟨p.witnessBits + p.inputBits + (i.val - (p.witnessBits + p.inputBits)), hlt⟩ :=
            (congrArg z key).symm
          _ = false := haz
      simp only [embedConfig, dif_neg hi, dif_neg hj]
      exact hzi

/-- A configuration with an incorrect input or a nonzero ancilla differs from every witness
embedding for that input. -/
theorem ne_embedConfig_of_not_clean (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (w : Reg p.witnessBits)
    (h : ¬ (inputRestrict p z = x ∧ ancillaZero p z)) : z ≠ embedConfig p x w := by
  intro he
  apply h
  rw [he]
  exact ⟨inputRestrict_embedConfig p x w, ancillaZero_embedConfig p x w⟩

/-- The matrix embedding witness amplitudes into configurations with fixed classical input and
zero ancillas. -/
noncomputable def witnessEmbed (p : WitnessVerifierProgram) (x : Reg p.inputBits) :
    Matrix (Reg (programQubits p)) (Reg p.witnessBits) ℂ :=
  Matrix.of fun z w => if z = embedConfig p x w then (1 : ℂ) else 0

/-- An entry of `witnessEmbed` is one exactly at the corresponding embedded configuration and
zero elsewhere. -/
theorem witnessEmbed_apply (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (w : Reg p.witnessBits) :
    witnessEmbed p x z w = if z = embedConfig p x w then (1 : ℂ) else 0 := rfl

/-- A clean configuration selects exactly its witness restriction in the corresponding embedding
row. -/
theorem witnessEmbed_row_of_clean (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (h : inputRestrict p z = x ∧ ancillaZero p z) :
    ∀ w : Reg p.witnessBits,
      witnessEmbed p x z w = if w = witnessRestrict p z then (1 : ℂ) else 0 := by
  intro w
  rw [witnessEmbed_apply]
  by_cases hw : w = witnessRestrict p z
  · rw [if_pos hw, if_pos]
    rw [hw]
    exact eq_embedConfig_of_clean p x z h
  · rw [if_neg hw, if_neg]
    intro he
    apply hw
    have h1 := congrArg (witnessRestrict p) he
    have h2 : witnessRestrict p z = w := by simpa [witnessRestrict_embedConfig] using h1
    exact h2.symm

/-- Every entry in an embedding row vanishes when the configuration has an incorrect input or
nonzero ancillas. -/
theorem witnessEmbed_row_of_not_clean (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (h : ¬ (inputRestrict p z = x ∧ ancillaZero p z)) :
    ∀ w : Reg p.witnessBits, witnessEmbed p x z w = 0 := by
  intro w
  rw [witnessEmbed_apply, if_neg (ne_embedConfig_of_not_clean p x z w h)]

/-- Complex conjugation fixes the indicator of a decidable proposition. -/
theorem star_ite_one (p : Prop) [Decidable p] :
    star (if p then (1 : ℂ) else 0) = if p then (1 : ℂ) else 0 := by
  by_cases h : p <;> simp [h]

/-- A double finite sum with indicators selecting `a` and `b` evaluates to `g a b`. -/
theorem sum_embedded_pair {n : Type*} [Fintype n] [DecidableEq n] (g : n → n → ℂ) (a b : n) :
    (∑ k : n, ∑ l : n, (if k = a then (1 : ℂ) else 0) * g k l * (if l = b then 1 else 0)) =
      g a b := by
  have h1 : ∀ k : n,
      (∑ l : n, (if k = a then (1 : ℂ) else 0) * g k l * (if l = b then 1 else 0)) =
        (if k = a then (1 : ℂ) else 0) * g k b := by
    intro k
    calc ∑ l : n, (if k = a then (1 : ℂ) else 0) * g k l * (if l = b then 1 else 0)
        = ∑ l : n, (if k = a then (1 : ℂ) else 0) * (g k l * (if l = b then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro l _
          ring
      _ = (if k = a then (1 : ℂ) else 0) * ∑ l : n, g k l * (if l = b then 1 else 0) := by
          rw [Finset.mul_sum]
      _ = (if k = a then (1 : ℂ) else 0) * g k b := by
          congr 1
          rw [Finset.sum_eq_single b]
          · simp
          · intro l _ hl
            simp [hl]
          · intro hb
            exact absurd (Finset.mem_univ b) hb
  calc ∑ k : n, ∑ l : n, (if k = a then (1 : ℂ) else 0) * g k l * (if l = b then 1 else 0)
      = ∑ k : n, (if k = a then (1 : ℂ) else 0) * g k b := by
        apply Finset.sum_congr rfl
        intro k _
        exact h1 k
    _ = g a b := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro k _ hk
          simp [hk]
        · intro ha
          exact absurd (Finset.mem_univ a) ha

/-- Every entry of the witness embedding is fixed by complex conjugation. -/
theorem star_witnessEmbed (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (w : Reg p.witnessBits) :
    star (witnessEmbed p x z w) = witnessEmbed p x z w := by
  rw [witnessEmbed_apply]
  by_cases h : z = embedConfig p x w <;> simp [h]

/-- Initialization of a witness matrix equals conjugation by the witness embedding matrix. -/
theorem verifierInputDensity_eq_mul (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    verifierInputDensity p x σ =
      witnessEmbed p x * σ * (witnessEmbed p x)ᴴ := by
  apply Matrix.ext
  intro z z'
  have hR : (witnessEmbed p x * σ * (witnessEmbed p x)ᴴ) z z'
      = ∑ k, ∑ l, witnessEmbed p x z k * σ k l * star (witnessEmbed p x z' l) := by
    calc (witnessEmbed p x * σ * (witnessEmbed p x)ᴴ) z z'
        = ∑ k, (∑ l, witnessEmbed p x z l * σ l k) *
            star (witnessEmbed p x z' k) := by
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = ∑ k, ∑ l, (witnessEmbed p x z l * σ l k) *
            star (witnessEmbed p x z' k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
      _ = ∑ l, ∑ k, (witnessEmbed p x z l * σ l k) *
            star (witnessEmbed p x z' k) := Finset.sum_comm
      _ = ∑ k, ∑ l, witnessEmbed p x z k * σ k l *
            star (witnessEmbed p x z' l) := rfl
  rw [hR]
  simp only [verifierInputDensity, Matrix.of_apply, star_witnessEmbed]
  by_cases hz : inputRestrict p z = x ∧ ancillaZero p z
  · by_cases hz' : inputRestrict p z' = x ∧ ancillaZero p z'
    · rw [if_pos ⟨hz.1, hz'.1, hz.2, hz'.2⟩]
      simp_rw [witnessEmbed_row_of_clean p x z hz, witnessEmbed_row_of_clean p x z' hz']
      exact (sum_embedded_pair σ (witnessRestrict p z) (witnessRestrict p z')).symm
    · rw [if_neg (fun h => hz' ⟨h.2.1, h.2.2.2⟩)]
      simp_rw [witnessEmbed_row_of_not_clean p x z' (fun h => hz' h)]
      simp
  · rw [if_neg (fun h => hz ⟨h.1, h.2.2.1⟩)]
    simp_rw [witnessEmbed_row_of_not_clean p x z (fun h => hz h)]
    simp

/-- Each entry of the witness embedding is idempotent under multiplication. -/
theorem witnessEmbed_sq (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (w : Reg p.witnessBits) :
    witnessEmbed p x z w * witnessEmbed p x z w = witnessEmbed p x z w := by
  rw [witnessEmbed_apply]
  by_cases hz : z = embedConfig p x w
  · rw [if_pos hz]; ring
  · rw [if_neg hz]; ring

/-- Entries in distinct witness columns have zero product within any fixed row. -/
theorem witnessEmbed_mul_of_ne (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (z : Reg (programQubits p)) (w w' : Reg p.witnessBits) (h : w ≠ w') :
    witnessEmbed p x z w * witnessEmbed p x z w' = 0 := by
  rw [witnessEmbed_apply, witnessEmbed_apply]
  by_cases h1 : z = embedConfig p x w
  · rw [if_pos h1]
    by_cases h2 : z = embedConfig p x w'
    · exact (h (embedConfig_injective p x (h1.symm.trans h2))).elim
    · rw [if_neg h2]; ring
  · rw [if_neg h1]; ring

/-- The inner product of two witness embedding columns is their equality indicator. -/
theorem sum_witnessEmbed_col (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (w w' : Reg p.witnessBits) :
    (∑ z : Reg (programQubits p),
        star (witnessEmbed p x z w) * witnessEmbed p x z w') =
      if w = w' then (1 : ℂ) else 0 := by
  by_cases h : w = w'
  · rw [if_pos h]
    have hterm : ∀ z : Reg (programQubits p),
        star (witnessEmbed p x z w) * witnessEmbed p x z w' = witnessEmbed p x z w' := by
      intro z
      rw [h, star_witnessEmbed]
      exact witnessEmbed_sq p x z w'
    calc ∑ z : Reg (programQubits p),
            star (witnessEmbed p x z w) * witnessEmbed p x z w'
        = ∑ z : Reg (programQubits p), witnessEmbed p x z w' :=
          Finset.sum_congr rfl fun z _ => hterm z
      _ = 1 := by
        have hite : ∀ z : Reg (programQubits p),
            witnessEmbed p x z w' = if z = embedConfig p x w' then (1 : ℂ) else 0 :=
          fun z => witnessEmbed_apply p x z w'
        simp_rw [hite]
        rw [Finset.sum_ite_eq' Finset.univ (embedConfig p x w')]
        simp
  · rw [if_neg h]
    have hterm : ∀ z : Reg (programQubits p),
        star (witnessEmbed p x z w) * witnessEmbed p x z w' = 0 := by
      intro z
      rw [star_witnessEmbed]
      exact witnessEmbed_mul_of_ne p x z w w' h
    calc ∑ z : Reg (programQubits p),
            star (witnessEmbed p x z w) * witnessEmbed p x z w'
        = ∑ z : Reg (programQubits p), (0 : ℂ) :=
          Finset.sum_congr rfl fun z _ => hterm z
      _ = 0 := Finset.sum_const_zero

/-- The witness embedding is an isometry: its adjoint multiplied by itself is the identity. -/
theorem witnessEmbed_conjTranspose_mul (p : WitnessVerifierProgram) (x : Reg p.inputBits) :
    (witnessEmbed p x)ᴴ * witnessEmbed p x = 1 := by
  apply Matrix.ext
  intro w w'
  have hsum : ((witnessEmbed p x)ᴴ * witnessEmbed p x) w w'
      = ∑ z, star (witnessEmbed p x z w) * witnessEmbed p x z w' := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsum, sum_witnessEmbed_col]
  exact (Matrix.one_apply (i := w) (j := w')).symm

/-- Initializing a Hermitian witness matrix produces a Hermitian full-register matrix. -/
theorem verifierInputDensity_isHermitian (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) (h : σ.IsHermitian) :
    (verifierInputDensity p x σ).IsHermitian := by
  have hσ : σᴴ = σ := h
  show (verifierInputDensity p x σ)ᴴ = verifierInputDensity p x σ
  rw [verifierInputDensity_eq_mul]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hσ]
  rw [← Matrix.mul_assoc]

/-- Initializing a positive semidefinite witness matrix preserves positive semidefiniteness. -/
theorem verifierInputDensity_posSemidef (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) (h : σ.PosSemidef) :
    (verifierInputDensity p x σ).PosSemidef := by
  rw [verifierInputDensity_eq_mul]
  exact h.mul_mul_conjTranspose_same _

/-- Initializing a witness matrix preserves its trace. -/
theorem verifierInputDensity_trace (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    Matrix.trace (verifierInputDensity p x σ) = Matrix.trace σ := by
  rw [verifierInputDensity_eq_mul, Matrix.trace_mul_cycle, witnessEmbed_conjTranspose_mul,
    one_mul]

/-- Initialization preserves Hermiticity, positive semidefiniteness, and trace for a Hermitian
positive semidefinite witness. -/
theorem cleanInitialization (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hherm : σ.IsHermitian) (hpsd : σ.PosSemidef) :
    (verifierInputDensity p x σ).IsHermitian ∧
      (verifierInputDensity p x σ).PosSemidef ∧
      Matrix.trace (verifierInputDensity p x σ) = Matrix.trace σ :=
  ⟨verifierInputDensity_isHermitian p x σ hherm,
    verifierInputDensity_posSemidef p x σ hpsd,
    verifierInputDensity_trace p x σ⟩

/-- Initializing a pure witness density gives the outer product of the initialized witness
state. -/
theorem verifierInputDensity_pure (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (w : QState (Reg p.witnessBits)) :
    verifierInputDensity p x (pureWitnessDensity w) =
      outerProduct (verifierInitialState p x w) := by
  apply Matrix.ext
  intro z z'
  simp only [verifierInputDensity, Matrix.of_apply, pureWitnessDensity, outerProduct_apply,
    verifierInitialState]
  by_cases hz : inputRestrict p z = x ∧ ancillaZero p z
  · by_cases hz' : inputRestrict p z' = x ∧ ancillaZero p z'
    · rw [if_pos ⟨hz.1, hz'.1, hz.2, hz'.2⟩, if_pos hz, if_pos hz']
    · rw [if_neg (fun h => hz' ⟨h.2.1, h.2.2.2⟩), if_pos hz, if_neg hz']
      simp
  · by_cases hz' : inputRestrict p z' = x ∧ ancillaZero p z'
    · rw [if_neg (fun h => hz ⟨h.1, h.2.2.1⟩), if_neg hz, if_pos hz']
      simp
    · rw [if_neg (fun h => hz ⟨h.1, h.2.2.1⟩), if_neg hz, if_neg hz']
      simp

/-- The real part of a diagonal outer-product entry is the corresponding Born probability. -/
theorem re_outerProduct_self {m : Type*} [Fintype m] (φ : QState m) (z : m) :
    (outerProduct φ z z).re = BornProb φ z := by
  have hterm : φ z * (starRingEnd ℂ) (φ z) = ((‖φ z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [outerProduct_apply, BornProb]
  rw [hterm]
  exact Complex.ofReal_re _

/-- Taking the real part commutes with a finite sum of complex numbers. -/
theorem re_sum_complex {m : Type*} [Fintype m] (f : m → ℂ) :
    (∑ z, f z).re = ∑ z, (f z).re :=
  map_sum RCLike.reLm f Finset.univ

/-- Conjugating an outer product by a matrix gives the outer product of the transformed vector. -/
theorem outerProduct_mul_conjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    (U : Matrix m m ℂ) (ψ : QState m) :
    U * outerProduct ψ * Uᴴ = outerProduct (U *ᵥ ψ) := by
  apply Matrix.ext
  intro z z'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, outerProduct_apply,
    RCLike.star_def]
  show (∑ l, (∑ k, U z k * (ψ k * (starRingEnd ℂ) (ψ l))) * (starRingEnd ℂ) (U z' l))
      = (∑ k, U z k * ψ k) * (starRingEnd ℂ) (∑ l, U z' l * ψ l)
  have hconj : (starRingEnd ℂ) (∑ l, U z' l * ψ l)
      = ∑ l, (starRingEnd ℂ) (U z' l) * (starRingEnd ℂ) (ψ l) := by
    rw [map_sum (starRingEnd ℂ)]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact map_mul (starRingEnd ℂ) _ _
  rw [hconj, Finset.sum_mul_sum]
  calc ∑ l, (∑ k, U z k * (ψ k * (starRingEnd ℂ) (ψ l))) * (starRingEnd ℂ) (U z' l)
      = ∑ l, ∑ k, (U z k * (ψ k * (starRingEnd ℂ) (ψ l))) * (starRingEnd ℂ) (U z' l) := by
        apply Finset.sum_congr rfl
        intro l _
        exact Finset.sum_mul _ _ _
    _ = ∑ k, ∑ l, (U z k * (ψ k * (starRingEnd ℂ) (ψ l))) * (starRingEnd ℂ) (U z' l) :=
        Finset.sum_comm
    _ = ∑ k, ∑ l, (U z k * ψ k) * ((starRingEnd ℂ) (U z' l) * (starRingEnd ℂ) (ψ l)) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring

/-- Acceptance of a pure witness equals the Born probability of the output event after running
the verifier. -/
theorem acceptProb_born (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (w : QState (Reg p.witnessBits)) :
    acceptProb A p x (pureWitnessDensity w) =
      MeasureProb (programRun A p (verifierInitialState p x w)) (programOutputEvent p) := by
  have hU : programMatrix A p * verifierInputDensity p x (pureWitnessDensity w) *
      (programMatrix A p)ᴴ = outerProduct (programRun A p (verifierInitialState p x w)) := by
    rw [verifierInputDensity_pure]
    exact outerProduct_mul_conjTranspose (programMatrix A p) (verifierInitialState p x w)
  unfold acceptProb MeasureProb BornProb
  rw [hU]
  apply Finset.sum_congr rfl
  intro z _
  exact re_outerProduct_self _ _

/-- Acceptance is nonnegative for every witness density satisfying `IsWitnessDensity`. -/
theorem acceptProb_nonneg (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hd : IsWitnessDensity σ) :
    0 ≤ acceptProb A p x σ := by
  have hpsd : (programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ).PosSemidef :=
    (verifierInputDensity_posSemidef p x σ hd.2.1).mul_mul_conjTranspose_same _
  unfold acceptProb
  apply Finset.sum_nonneg
  intro z _
  exact (Complex.nonneg_iff.mp (hpsd.diag_nonneg (i := z))).1

/-- Acceptance is at most one for every witness density satisfying `IsWitnessDensity`. -/
theorem acceptProb_le_one (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hd : IsWitnessDensity σ) :
    acceptProb A p x σ ≤ 1 := by
  have hpsd : (programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ).PosSemidef :=
    (verifierInputDensity_posSemidef p x σ hd.2.1).mul_mul_conjTranspose_same _
  have hnonneg : ∀ z : Reg (programQubits p),
      0 ≤ ((programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) z z).re :=
    fun z => (Complex.nonneg_iff.mp (hpsd.diag_nonneg (i := z))).1
  have hsub : acceptProb A p x σ ≤
      ∑ z : Reg (programQubits p),
        ((programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) z z).re := by
    unfold acceptProb
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun z _ _ => hnonneg z
  have htrace : (Matrix.trace
        (programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ)).re =
      ∑ z : Reg (programQubits p),
        ((programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) z z).re := by
    rw [Matrix.trace]
    exact re_sum_complex _
  have htr : Matrix.trace
      (programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) =
      Matrix.trace σ := by
    rw [Matrix.trace_mul_cycle, conjTranspose_programMatrix_mul_self, one_mul]
    exact verifierInputDensity_trace p x σ
  have hre : (Matrix.trace σ).re ≤ 1 := by
    simpa [Complex.one_re] using (Complex.le_def.mp hd.2.2).1
  calc acceptProb A p x σ
      ≤ ∑ z : Reg (programQubits p),
          ((programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ) z z).re := hsub
    _ = (Matrix.trace
          (programMatrix A p * verifierInputDensity p x σ * (programMatrix A p)ᴴ)).re :=
      htrace.symm
    _ = (Matrix.trace σ).re := by rw [htr]
    _ ≤ 1 := hre

/-- Flips a single Boolean register wire and leaves every other wire unchanged. -/
def flipWire {q : ℕ} (w : Fin q) : Reg q → Reg q :=
  fun z => Function.update z w (!z w)

/-- Flipping the same register wire twice is the identity. -/
theorem flipWire_involutive {q : ℕ} (w : Fin q) : Function.Involutive (flipWire w) := by
  intro z
  funext i
  show Function.update (Function.update z w (!z w)) w
    (!(Function.update z w (!z w) w)) i = z i
  by_cases hi : i = w
  · rw [hi, Function.update_self, Function.update_self, Bool.not_not]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- A Pauli X gate on one wire equals the permutation matrix of that wire flip. -/
theorem wireGate_pauliX_permMatrix {q : ℕ} (w : Fin q) :
    wireGate q w PauliX = permMatrix (flipWire w) := by
  apply Matrix.ext
  intro z y
  have hpauli : ∀ a b : Bool, PauliX a b = if a = !b then (1 : ℂ) else 0 := by
    intro a b
    show permMatrix Bool.not a b = _
    simp only [permMatrix, Matrix.of_apply]
  rw [wireGate_apply]
  show (if ∀ k : Fin q, k ≠ w → z k = y k then PauliX (z w) (y w) else 0)
    = if z = flipWire w y then (1 : ℂ) else 0
  rw [hpauli]
  by_cases hall : ∀ k : Fin q, k ≠ w → z k = y k
  · rw [if_pos hall]
    by_cases hw : z w = !y w
    · rw [if_pos hw]
      have hz : z = flipWire w y := by
        funext i
        by_cases hi : i = w
        · rw [hi]
          show z w = Function.update y w (!y w) w
          rw [Function.update_self]
          exact hw
        · show z i = Function.update y w (!y w) i
          rw [Function.update_of_ne hi]
          exact hall i hi
      rw [if_pos hz]
    · rw [if_neg hw]
      have hz : z ≠ flipWire w y := by
        intro he
        apply hw
        have hwe := congrFun he w
        show z w = !y w
        rw [hwe]
        show Function.update y w (!y w) w = !y w
        rw [Function.update_self]
      rw [if_neg hz]
  · rw [if_neg hall]
    have hz : z ≠ flipWire w y := by
      intro he
      apply hall
      intro k hk
      have hke := congrFun he k
      show z k = y k
      rw [hke]
      show Function.update y w (!y w) k = y k
      rw [Function.update_of_ne hk]
    rw [if_neg hz]

/-- Initializing a computational basis witness gives the basis state of its embedded
configuration. -/
theorem verifierInitialState_ket (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (u : Reg p.witnessBits) :
    verifierInitialState p x (Qatlib.Foundations.PureStateMath.Ket u) = Qatlib.Foundations.PureStateMath.Ket (embedConfig p x u) := by
  funext z
  simp only [verifierInitialState, Qatlib.Foundations.PureStateMath.Ket]
  by_cases hclean : inputRestrict p z = x ∧ ancillaZero p z
  · by_cases hw : witnessRestrict p z = u
    · have hz : z = embedConfig p x u := by
        rw [← hw]
        exact eq_embedConfig_of_clean p x z hclean
      rw [if_pos hclean, if_pos hw, if_pos hz]
    · have hz : z ≠ embedConfig p x u := by
        intro he
        apply hw
        rw [he]
        exact witnessRestrict_embedConfig p x u
      rw [if_pos hclean, if_neg hw, if_neg hz]
  · have hz : z ≠ embedConfig p x u := ne_embedConfig_of_not_clean p x z u hclean
    rw [if_neg hclean, if_neg hz]

/-- The identity matrix on the empty witness register is the pure density of its unique basis
state. -/
theorem matrix_one_eq_pure_zero :
    (1 : Matrix (Reg 0) (Reg 0) ℂ) = pureWitnessDensity (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) := by
  have heq : ∀ (a b : Reg 0), a = b :=
    fun a b => funext fun k => (Nat.not_lt_zero k.val k.isLt).elim
  apply Matrix.ext
  intro i j
  rw [heq i j, ← heq (fun _ => false) j, Matrix.one_apply_eq]
  simp only [pureWitnessDensity, outerProduct_apply, ket_self]
  simp

/-- Measuring a basis state in an event containing that basis label has probability one. -/
theorem measureProb_ket_of_mem {q : Type*} [Fintype q] [DecidableEq q] (ρ : q) (E : Finset q)
    (h : ρ ∈ E) : MeasureProb (Qatlib.Foundations.PureStateMath.Ket ρ) E = 1 := by
  unfold MeasureProb
  simp only [bornProb_ket]
  rw [Finset.sum_ite_eq' E ρ]
  simp [h]

/-- A witness-free verifier that flips its sole ancilla, chosen as the output wire, after the
input register. -/
def xVerifierProgram (m : ℕ) : WitnessVerifierProgram :=
  ⟨0, m, 1, m, [WitnessInstruction.fixed (.x m)]⟩

/-- The single-X verifier is a legal witness verifier program. -/
theorem xVerifierProgram_legal (m : ℕ) : witnessProgramLegal (xVerifierProgram m) := by
  refine ⟨?_, ?_⟩
  · show m < programQubits (xVerifierProgram m)
    show m < 0 + m + 1
    omega
  · intro i hi
    simp only [xVerifierProgram, List.mem_singleton] at hi
    rw [hi]
    show instructionLegal (programQubits (xVerifierProgram m)) (WitnessInstruction.fixed (.x m))
    show finiteCodeLegal (0 + m + 1) (.x m) = true
    simp [finiteCodeLegal]

/-- The single-X verifier contains no oracle instructions. -/
theorem xVerifierProgram_oracleFree (m : ℕ) : oracleFree (xVerifierProgram m) := by
  show (List.all [WitnessInstruction.fixed (.x m)] fun
    | .fixed _ => true
    | .oracle _ _ => false) = true
  rfl

/-- The output ancilla of the initialized single-X verifier is false. -/
theorem xVerifierProgram_embed_ancilla (m : ℕ) (x : Reg m) (u : Reg 0) :
    (embedConfig (xVerifierProgram m) x u)
      (⟨m, by show m < programQubits (xVerifierProgram m); show m < 0 + m + 1; omega⟩) = false := by
  have hwb : (xVerifierProgram m).witnessBits = 0 := rfl
  have hsum : (xVerifierProgram m).witnessBits + (xVerifierProgram m).inputBits = m := by
    rw [hwb, show (xVerifierProgram m).inputBits = m from rfl, Nat.zero_add]
  simp only [embedConfig]
  split_ifs with h1 h2
  · have : m < (xVerifierProgram m).witnessBits := h1
    rw [hwb] at this
    exact absurd this (by omega)
  · have : m < (xVerifierProgram m).witnessBits + (xVerifierProgram m).inputBits := h2
    rw [hsum] at this
    exact absurd this (by omega)
  · rfl

/-- With the constantly false oracle, the single-X verifier matrix is the permutation that flips
its output ancilla. -/
theorem xVerifierProgram_programMatrix (m : ℕ) :
    programMatrix (fun _ _ => false) (xVerifierProgram m) =
      permMatrix (flipWire (⟨m, by
        show m < programQubits (xVerifierProgram m)
        show m < 0 + m + 1
        omega⟩ : Fin (programQubits (xVerifierProgram m)))) := by
  have hlt : m < programQubits (xVerifierProgram m) := by
    show m < 0 + m + 1
    omega
  have hstep : programMatrix (fun _ _ => false) (xVerifierProgram m) =
      finiteCodeMatrix (programQubits (xVerifierProgram m)) (.x m) := by
    show ([(WitnessInstruction.fixed (.x m))].map
        (instructionMatrix (fun _ _ => false) (programQubits (xVerifierProgram m)))).reverse.prod
      = _
    rw [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.prod_cons, List.prod_nil, mul_one]
    rfl
  rw [hstep]
  show (if h : m < programQubits (xVerifierProgram m) then
      wireGate (programQubits (xVerifierProgram m)) ⟨m, h⟩ PauliX else 1) = _
  rw [dif_pos hlt]
  exact wireGate_pauliX_permMatrix _

/-- The single-X verifier sends an initialized basis configuration to the basis state with its
output ancilla flipped. -/
theorem xVerifierProgram_run (m : ℕ) (x : Reg m) (u : Reg 0) :
    programRun (fun _ _ => false) (xVerifierProgram m)
      (Qatlib.Foundations.PureStateMath.Ket (embedConfig (xVerifierProgram m) x u)) =
      Qatlib.Foundations.PureStateMath.Ket (flipWire (⟨m, by
        show m < programQubits (xVerifierProgram m)
        show m < 0 + m + 1
        omega⟩ : Fin (programQubits (xVerifierProgram m)))
        (embedConfig (xVerifierProgram m) x u)) := by
  unfold programRun
  rw [xVerifierProgram_programMatrix]
  exact applyGate_permMatrix_ket (flipWire_involutive _) _

/-- Flipping the initialized output ancilla of the single-X verifier yields a configuration in
its acceptance event. -/
theorem xVerifierProgram_output_mem (m : ℕ) (x : Reg m) (u : Reg 0) :
    flipWire (⟨m, by
      show m < programQubits (xVerifierProgram m)
      show m < 0 + m + 1
      omega⟩ : Fin (programQubits (xVerifierProgram m)))
      (embedConfig (xVerifierProgram m) x u) ∈
      programOutputEvent (xVerifierProgram m) := by
  have hlt : (xVerifierProgram m).outputWire < programQubits (xVerifierProgram m) := by
    show m < 0 + m + 1
    omega
  simp only [programOutputEvent]
  rw [dif_pos hlt]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show Function.update (embedConfig (xVerifierProgram m) x u) ⟨m, _⟩
    (!(embedConfig (xVerifierProgram m) x u ⟨m, _⟩)) ⟨m, _⟩ = true
  rw [Function.update_self, xVerifierProgram_embed_ancilla]
  rfl

/-- The empty witness identity for the single-X verifier is the density of the unique empty
basis state. -/
theorem xVerifierProgram_one_eq_pure (m : ℕ) :
    (1 : Matrix (Reg (xVerifierProgram m).witnessBits) (Reg (xVerifierProgram m).witnessBits) ℂ)
      = pureWitnessDensity (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) :=
  matrix_one_eq_pure_zero

/-- The single-X verifier accepts every classical input with probability one. -/
theorem xVerifierProgram_acceptProb (m : ℕ) (x : Reg m) :
    acceptProb (fun _ _ => false) (xVerifierProgram m) x 1 = 1 := by
  rw [xVerifierProgram_one_eq_pure, acceptProb_born, verifierInitialState_ket,
    xVerifierProgram_run]
  exact measureProb_ket_of_mem _ _ (xVerifierProgram_output_mem m x _)

/-- Collects clean density initialization, pure-state acceptance semantics, probability bounds,
validity of the empty verifier family, and a legal oracle-free verifier accepting with
certainty. -/
theorem g1 :
  (∀ (p : WitnessVerifierProgram) (x : Reg p.inputBits)
      (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ),
    σ.IsHermitian → σ.PosSemidef →
      ((verifierInputDensity p x σ).IsHermitian ∧
        (verifierInputDensity p x σ).PosSemidef ∧
        Matrix.trace (verifierInputDensity p x σ) = Matrix.trace σ)) ∧
  (∀ (A : ClassicalOracle) (p : WitnessVerifierProgram)
      (hp : witnessProgramLegal p) (x : Reg p.inputBits)
      (w : QState (Reg p.witnessBits)), Normalized w →
    acceptProb A p x (pureWitnessDensity w) =
      MeasureProb (programRun A p (verifierInitialState p x w))
        (programOutputEvent p)) ∧
  (∀ (A : ClassicalOracle) (p : WitnessVerifierProgram)
      (hp : witnessProgramLegal p) (x : Reg p.inputBits)
      (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ),
    IsWitnessDensity σ →
      0 ≤ acceptProb A p x σ ∧ acceptProb A p x σ ≤ 1) ∧
  (∀ n : ℕ,
    witnessProgramAt zeroVerifierFamily n = some ⟨0, n, 1, 0, []⟩ ∧
      witnessFamilyValid zeroVerifierFamily) ∧
  (∀ m : ℕ,
    witnessProgramLegal ⟨0, m, 1, m, [WitnessInstruction.fixed (.x m)]⟩ ∧
      oracleFree ⟨0, m, 1, m, [WitnessInstruction.fixed (.x m)]⟩ ∧
      ∀ x : Reg m,
        acceptProb (fun _ _ => false) ⟨0, m, 1, m, [WitnessInstruction.fixed (.x m)]⟩ x 1
          = 1) :=
  ⟨fun p x σ hherm hpsd => cleanInitialization p x σ hherm hpsd,
    fun A p _ x w _ => acceptProb_born A p x w,
    fun A p _ x σ hd => ⟨acceptProb_nonneg A p x σ hd, acceptProb_le_one A p x σ hd⟩,
    fun n => zeroVerifierFamily_at n,
    fun m => ⟨xVerifierProgram_legal m, xVerifierProgram_oracleFree m,
      fun x => xVerifierProgram_acceptProb m x⟩⟩

/-- Translates a uniform instruction to a witness instruction by merging both oracle labels into
one. -/
def uniformToWitnessInstruction : UniformVerifierInstruction → WitnessInstruction
  | .fixed gate => .fixed gate
  | .queryS addresses target => .oracle addresses target
  | .queryU addresses target => .oracle addresses target

/-- A legal XOR oracle matrix is both unitary and self-adjoint. -/
theorem xorQueryMatrix_involution_access (A : ClassicalOracle) (q : ℕ) (addresses : List ℕ)
    (target : ℕ)
    (h : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup) :
    xorQueryMatrix A q addresses target ∈ Matrix.unitaryGroup (Reg q) ℂ ∧
      (xorQueryMatrix A q addresses target)ᴴ = xorQueryMatrix A q addresses target :=
  ⟨xorQueryMatrix_unitary A q addresses target h, xorQueryMatrix_selfAdjoint A q addresses target h⟩

/-- Translation of a uniform verifier preserves the sum of address lengths over its oracle
instructions. -/
theorem addressBitLedger_transport (p : UniformVerifierProgram) :
    addressBitLedger (fromUniformVerifierProgram p) =
      (p.instructions.filterMap fun
        | .fixed _ => none
        | .queryS addresses _ | .queryU addresses _ => some addresses.length).sum := by
  show ((fromUniformVerifierProgram p).instructions.filterMap fun
    | .fixed _ => none
    | .oracle addresses _ => some addresses.length).sum = _
  have hin : (fromUniformVerifierProgram p).instructions =
      p.instructions.map uniformToWitnessInstruction := rfl
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

/-- Every program produced by a valid uniform generator translates to a legal witness verifier. -/
theorem legality_transport (g : UniformVerifierGenerator) (hg : uniformGeneratorValid g) :
    ∀ n : ℕ, ∀ p : UniformVerifierProgram,
      uniformGeneratedProgramAt g n = some p →
        witnessProgramLegal (fromUniformVerifierProgram p) := by
  intro n p hgen
  obtain ⟨p', hgen', _, _, _, hlegal₀⟩ := hg n
  have hlegal : uniformProgramLegal p := by
    rw [← Option.some.inj (hgen'.symm.trans hgen)]
    exact hlegal₀
  have hw : p.witnessBits ≤ p.qubits := hlegal.1
  have hq : programQubits (fromUniformVerifierProgram p) = p.qubits := by
    show p.witnessBits + 0 + (p.qubits - p.witnessBits) = p.qubits
    omega
  refine ⟨?_, ?_⟩
  · show (fromUniformVerifierProgram p).outputWire < programQubits (fromUniformVerifierProgram p)
    rw [hq]
    show p.outputWire < p.qubits
    exact hlegal.2.1
  · intro i hi
    have hin : (fromUniformVerifierProgram p).instructions =
        p.instructions.map uniformToWitnessInstruction := rfl
    rw [hin] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hins := hlegal.2.2 j hj
    cases j with
    | fixed gate =>
      show instructionLegal (programQubits (fromUniformVerifierProgram p))
        (WitnessInstruction.fixed gate)
      rw [hq]
      show finiteCodeLegal p.qubits gate = true
      exact hins
    | queryS addresses target =>
      show instructionLegal (programQubits (fromUniformVerifierProgram p))
        (WitnessInstruction.oracle addresses target)
      rw [hq]
      show target < p.qubits ∧ (∀ a ∈ addresses, a < p.qubits) ∧ target ∉ addresses ∧
        addresses.Nodup
      exact hins
    | queryU addresses target =>
      show instructionLegal (programQubits (fromUniformVerifierProgram p))
        (WitnessInstruction.oracle addresses target)
      rw [hq]
      show target < p.qubits ∧ (∀ a ∈ addresses, a < p.qubits) ∧ target ∉ addresses ∧
        addresses.Nodup
      exact hins

/-- For an oracle-free program, acceptance agrees with its value under the constantly false
oracle. -/
theorem acceptProb_oracleFree (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hfree : oracleFree p) :
    acceptProb A p x σ = acceptProb (fun _ _ => false) p x σ := by
  have hall : ∀ i ∈ p.instructions, instructionMatrix A (programQubits p) i =
      instructionMatrix (fun _ _ => false) (programQubits p) i := by
    intro i hi
    have hmem : (p.instructions.all fun
        | .fixed _ => true
        | .oracle _ _ => false) = true := hfree
    have := List.all_eq_true.mp hmem i hi
    cases i with
    | fixed gate => rfl
    | oracle addresses target => simp at this
  have hmap : p.instructions.map (instructionMatrix A (programQubits p)) =
      p.instructions.map (instructionMatrix (fun _ _ => false) (programQubits p)) :=
    List.map_congr_left hall
  have hmat : programMatrix A p = programMatrix (fun _ _ => false) p := by
    unfold programMatrix
    rw [hmap]
  unfold acceptProb
  rw [hmat]

/-- Membership in `InQMA` implies `InQMAWith A` for any oracle, since these verifier families
are oracle-free. -/
theorem inQMA_inQMAWith (A : ClassicalOracle) (L : BitstringPromise) :
    InQMA L → InQMAWith A L := by
  intro h
  obtain ⟨f, hvalid, hfree, hyes, hno⟩ := h
  refine ⟨f, hvalid, hfree, ?_, ?_⟩
  · intro x hx
    obtain ⟨σ, hσ, happ⟩ := hyes x hx
    refine ⟨σ, hσ, ?_⟩
    rw [acceptProb_oracleFree A (familyProgram f x.length) (listToInput _ x) σ (hfree x.length)]
    exact happ
  · intro x hx σ hσ
    rw [acceptProb_oracleFree A (familyProgram f x.length) (listToInput _ x) σ (hfree x.length)]
    exact hno x hx σ hσ

/-- Establishes the imported spectral forrelation property `QmaVerifierSpectralForrelation`. -/
theorem forrelation_core : QmaVerifierSpectralForrelation :=
  qmaVerifierSpectralForrelation

/-- On an address followed by a control bit, `appendedControlOracle` returns the conjunction of
that control bit and the original oracle value. -/
theorem appendedControlOracle_readAddress {q : ℕ} (A : ClassicalOracle) (x : Reg q)
    (addresses : List ℕ) (control : ℕ) (haddr0 : ∀ a ∈ addresses, a < q) (hcontrol : control < q)
    (n : ℕ) (hn : n = addresses.length + 1) (r : Reg n)
    (hr : ∀ i : Fin n, r i =
      if h : i.val < addresses.length then
        x ⟨addresses.get ⟨i.val, h⟩, haddr0 _ (List.get_mem _ _)⟩
      else x ⟨control, hcontrol⟩) :
    appendedControlOracle A n r =
      (x ⟨control, hcontrol⟩ && A addresses.length (readAddress x addresses haddr0)) := by
  subst hn
  have hlast : r (Fin.last addresses.length) = x ⟨control, hcontrol⟩ := by
    rw [hr]
    have hneg : ¬(Fin.last addresses.length).val < addresses.length := by
      rw [Fin.val_last]
      exact Nat.lt_irrefl _
    rw [dif_neg hneg]
  have hcast : (fun i : Fin addresses.length => r i.castSucc)
      = readAddress x addresses haddr0 := by
    funext i
    rw [hr]
    have hi : (i.castSucc).val < addresses.length := by
      rw [Fin.val_castSucc]
      exact i.isLt
    rw [dif_pos hi]
    show x ⟨addresses.get ⟨i.castSucc.val, hi⟩, haddr0 _ (List.get_mem _ _)⟩ =
      x ⟨addresses.get i, haddr0 _ (List.get_mem addresses i)⟩
    rfl
  show (r (Fin.last addresses.length) && A addresses.length (fun i => r i.castSucc)) = _
  rw [hlast, hcast]

/-- A legal controlled XOR query equals an XOR query to `appendedControlOracle` with the control
appended to the address. -/
theorem controlledXor_eq_appended (A : ClassicalOracle) (q : ℕ) (addresses : List ℕ)
    (target control : ℕ)
    (h : target < q ∧ control < q ∧ control ≠ target ∧ control ∉ addresses ∧
      (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup) :
    controlledXorMatrix A q addresses target control =
      xorQueryMatrix (appendedControlOracle A) q (addresses ++ [control]) target := by
  classical
  have hctrl : target < q ∧ control < q ∧ control ≠ target ∧
      (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have hmem : ∀ a ∈ addresses ++ [control], a < q := by
    intro a ha
    rw [List.mem_append, List.mem_singleton] at ha
    cases ha with
    | inl h' => exact h.2.2.2.2.1 a h'
    | inr h' => rw [h']; exact h.2.1
  have hdisj : target ∉ addresses ++ [control] := by
    intro ha
    rw [List.mem_append, List.mem_singleton] at ha
    cases ha with
    | inl h' => exact h.2.2.2.2.2.1 h'
    | inr h' => exact h.2.2.1 h'.symm
  have hnd : (addresses ++ [control]).Nodup := by
    refine List.Nodup.append h.2.2.2.2.2.2 (List.nodup_singleton control) ?_
    rw [List.disjoint_singleton]
    exact h.2.2.2.1
  have hq : target < q ∧ (∀ a ∈ addresses ++ [control], a < q) ∧
      target ∉ addresses ++ [control] ∧ (addresses ++ [control]).Nodup :=
    ⟨h.1, hmem, hdisj, hnd⟩
  simp only [controlledXorMatrix, dif_pos hctrl, xorQueryMatrix, dif_pos hq]
  show permMatrix (controlledXorUpdate A addresses target control hctrl.1 hctrl.2.1
      hctrl.2.2.2.1) =
    permMatrix (xorQueryUpdate (appendedControlOracle A) (addresses ++ [control]) target
      hq.1 hq.2.1)
  congr 1
  funext x
  show Function.update x ⟨target, h.1⟩
      (x ⟨target, h.1⟩ ^^ (x ⟨control, h.2.1⟩ &&
        A addresses.length (readAddress x addresses h.2.2.2.2.1))) =
    Function.update x ⟨target, h.1⟩
      (x ⟨target, h.1⟩ ^^ appendedControlOracle A (addresses ++ [control]).length
        (readAddress x (addresses ++ [control]) hmem))
  congr 1
  congr 1
  exact (appendedControlOracle_readAddress A x addresses control h.2.2.2.2.1 h.2.1
    (addresses ++ [control]).length
    (by rw [List.length_append, List.length_singleton])
    (readAddress x (addresses ++ [control]) hmem)
    (fun i => by
      show readAddress x (addresses ++ [control]) hmem i =
        (if hlt : i.val < addresses.length then
          x ⟨addresses.get ⟨i.val, hlt⟩, h.2.2.2.2.1 _ (List.get_mem _ _)⟩
        else x ⟨control, h.2.1⟩)
      show x ⟨(addresses ++ [control]).get i, hmem _ (List.get_mem _ _)⟩ = _
      by_cases hi : i.val < addresses.length
      · rw [dif_pos hi]
        refine congrArg x ?_
        apply Fin.eq_of_val_eq
        show (addresses ++ [control]).get i = (addresses.get ⟨i.val, hi⟩ : ℕ)
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left hi
      · rw [dif_neg hi]
        have hlen : (addresses ++ [control]).length = addresses.length + 1 := by
          rw [List.length_append, List.length_singleton]
        refine congrArg x ?_
        apply Fin.eq_of_val_eq
        show (addresses ++ [control]).get i = (control : ℕ)
        rw [List.get_eq_getElem]
        exact List.getElem_concat_length (l := addresses) (a := control)
          (show i.val = addresses.length from by omega) i.isLt)).symm

/-- When both uniform oracle labels denote `A`, translation preserves each instruction matrix. -/
theorem uniformInstrMatrix_eq (n : ℕ) (A : ClassicalOracle) (i : UniformVerifierInstruction) :
    uniformInstrMatrix n A A i = instructionMatrix A n (uniformToWitnessInstruction i) := by
  cases i with
  | fixed gate => rfl
  | queryS addresses target =>
    rw [show uniformInstrMatrix n A A (UniformVerifierInstruction.queryS addresses target)
        = @dite (Matrix (Reg n) (Reg n) ℂ) (modelQueryLegal n addresses target)
            (Classical.propDecidable _)
            (fun h => (have h' : target < n ∧ (∀ a ∈ addresses, a < n) ∧
                target ∉ addresses ∧ addresses.Nodup := h;
              permMatrix (xorQueryUpdate A addresses target h'.1 h'.2.1))) (fun _ => 1)
        from rfl]
    simp only [uniformToWitnessInstruction, instructionMatrix, xorQueryMatrix]
    by_cases h : target < n ∧ (∀ a ∈ addresses, a < n) ∧ target ∉ addresses ∧ addresses.Nodup
    · have hL : modelQueryLegal n addresses target := h
      rw [dif_pos hL, dif_pos h]
    · have hL : ¬modelQueryLegal n addresses target := fun hh => h hh
      rw [dif_neg hL, dif_neg h]
  | queryU addresses target =>
    rw [show uniformInstrMatrix n A A (UniformVerifierInstruction.queryU addresses target)
        = @dite (Matrix (Reg n) (Reg n) ℂ) (modelQueryLegal n addresses target)
            (Classical.propDecidable _)
            (fun h => (have h' : target < n ∧ (∀ a ∈ addresses, a < n) ∧
                target ∉ addresses ∧ addresses.Nodup := h;
              permMatrix (xorQueryUpdate A addresses target h'.1 h'.2.1))) (fun _ => 1)
        from rfl]
    simp only [uniformToWitnessInstruction, instructionMatrix, xorQueryMatrix]
    by_cases h : target < n ∧ (∀ a ∈ addresses, a < n) ∧ target ∉ addresses ∧ addresses.Nodup
    · have hL : modelQueryLegal n addresses target := h
      rw [dif_pos hL, dif_pos h]
    · have hL : ¬modelQueryLegal n addresses target := fun hh => h hh
      rw [dif_neg hL, dif_neg h]

/-- Executing uniform instructions with both oracle labels equal to `A` is multiplication by
their reversed matrix product. -/
theorem uniformRunInstr_eq_prod (A : ClassicalOracle) (q : ℕ)
    (is : List UniformVerifierInstruction) (ψ : QState (Reg q)) :
    uniformRunInstr A A q is ψ =
      ((is.map (uniformInstrMatrix q A A)).reverse.prod) *ᵥ ψ := by
  induction is generalizing ψ with
  | nil =>
    show uniformRunInstr A A q [] ψ = (1 : Matrix (Reg q) (Reg q) ℂ) *ᵥ ψ
    rw [Matrix.one_mulVec]
    rfl
  | cons i rest ih =>
    show uniformRunInstr A A q rest (ApplyGate (uniformInstrMatrix q A A i) ψ)
      = ((i :: rest).map (uniformInstrMatrix q A A)).reverse.prod *ᵥ ψ
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one]
    rw [← Matrix.mulVec_mulVec]
    exact ih (ApplyGate (uniformInstrMatrix q A A i) ψ)

/-- Translation preserves uniform instruction execution across an equality of register widths,
with the corresponding state casts. -/
theorem run_transport_cast {m n : ℕ} (h : m = n)
    (is : List UniformVerifierInstruction) (A : ClassicalOracle) (ψ : QState (Reg m)) :
    ((is.map (fun i => instructionMatrix A m (uniformToWitnessInstruction i))).reverse.prod) *ᵥ ψ
      = cast (congrArg QState (congrArg Reg h)).symm
          (uniformRunInstr A A n is (cast (congrArg QState (congrArg Reg h)) ψ)) := by
  cases h
  rw [uniformRunInstr_eq_prod]
  have key : (fun i : UniformVerifierInstruction =>
      instructionMatrix A m (uniformToWitnessInstruction i)) = uniformInstrMatrix m A A := by
    funext i
    exact (uniformInstrMatrix_eq m A i).symm
  rw [key]
  rfl

/-- A legal uniform program with matching translated width has the same execution as its witness
translation when both oracles equal `A`. -/
theorem run_transport (A : ClassicalOracle) (p : UniformVerifierProgram)
    (_hp : uniformProgramLegal p)
    (ψ : QState (Reg (programQubits (fromUniformVerifierProgram p))))
    (hq : programQubits (fromUniformVerifierProgram p) = p.qubits) :
    programRun A (fromUniformVerifierProgram p) ψ =
      cast (congrArg QState (congrArg Reg hq)).symm
        (uniformVerifierRun A A p
          (cast (congrArg QState (congrArg Reg hq)) ψ)) := by
  show programMatrix A (fromUniformVerifierProgram p) *ᵥ ψ = _
  have hin : (fromUniformVerifierProgram p).instructions =
      p.instructions.map uniformToWitnessInstruction := rfl
  have hprod : programMatrix A (fromUniformVerifierProgram p)
      = ((p.instructions.map (fun i => instructionMatrix A
          (programQubits (fromUniformVerifierProgram p))
          (uniformToWitnessInstruction i))).reverse.prod) := by
    unfold programMatrix
    rw [hin, List.map_map]
    rfl
  rw [hprod]
  have hrun : uniformVerifierRun A A p (cast (congrArg QState (congrArg Reg hq)) ψ)
      = uniformRunInstr A A p.qubits p.instructions
          (cast (congrArg QState (congrArg Reg hq)) ψ) := rfl
  rw [hrun]
  exact run_transport_cast hq p.instructions A ψ

/-- Collects legal oracle-query identities, address accounting, execution and legality
transport, oracle-independent QMA membership, and the spectral forrelation property. -/
theorem g3 :
  (∀ (A : ClassicalOracle) (q : ℕ) (addresses : List ℕ) (target : ℕ)
      (h : target < q ∧ (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧
        addresses.Nodup),
    xorQueryMatrix A q addresses target ∈ Matrix.unitaryGroup (Reg q) ℂ ∧
      (xorQueryMatrix A q addresses target)ᴴ =
        xorQueryMatrix A q addresses target) ∧
  (∀ (A : ClassicalOracle) (q : ℕ) (addresses : List ℕ) (target control : ℕ)
      (h : target < q ∧ control < q ∧ control ≠ target ∧ control ∉ addresses ∧
        (∀ a ∈ addresses, a < q) ∧ target ∉ addresses ∧ addresses.Nodup),
    controlledXorMatrix A q addresses target control =
      xorQueryMatrix (appendedControlOracle A) q (addresses ++ [control]) target) ∧
  (∀ p : UniformVerifierProgram,
    addressBitLedger (fromUniformVerifierProgram p) =
      (p.instructions.filterMap fun
        | .fixed _ => none
        | .queryS addresses _ | .queryU addresses _ => some addresses.length).sum) ∧
  (∀ (A : ClassicalOracle) (p : UniformVerifierProgram)
      (hp : uniformProgramLegal p)
      (ψ : QState (Reg (programQubits (fromUniformVerifierProgram p))))
      (hq : programQubits (fromUniformVerifierProgram p) = p.qubits),
    programRun A (fromUniformVerifierProgram p) ψ =
      cast (congrArg QState (congrArg Reg hq)).symm
        (uniformVerifierRun A A p
          (cast (congrArg QState (congrArg Reg hq)) ψ))) ∧
  (∀ g : UniformVerifierGenerator, uniformGeneratorValid g →
    ∀ n : ℕ, ∀ p : UniformVerifierProgram,
      uniformGeneratedProgramAt g n = some p →
        witnessProgramLegal (fromUniformVerifierProgram p)) ∧
  (∀ (A : ClassicalOracle) (L : BitstringPromise), InQMA L → InQMAWith A L) ∧
  (QmaVerifierSpectralForrelation) :=
  ⟨fun A q addresses target h => xorQueryMatrix_involution_access A q addresses target h,
    fun A q addresses target control h => controlledXor_eq_appended A q addresses target control h,
    fun p => addressBitLedger_transport p,
    fun A p hp ψ hq => run_transport A p hp ψ hq,
    fun g hg n p hgen => legality_transport g hg n p hgen,
    fun A L h => inQMA_inQMAWith A L h,
    forrelation_core⟩
