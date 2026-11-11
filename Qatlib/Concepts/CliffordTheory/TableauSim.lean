/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerExt

/-!
# Tableau simulation of stabilizer programs

This module defines finite adaptive stabilizer programs in `Program` and their tableau execution
in `execute`. The physical semantics `physicalExecute` relates Clifford updates and Pauli
measurement branches to normalized states in tableau code spaces, with exact probabilities
determined by the consumed fair bits. These constructions use the stabilizer simulation
framework of [Gottesman1997] and [AaronsonGottesman2004].

Explicit Boolean expressions and instruction blocks compile the tableau updates to `rawRun`. The
cell and live execution relations realize the generated traces and provide time and space
estimates, keeping the abstract machine counters separate from the elementary event counts.

## Main statements

* `frontier1`: physical correctness, exact branch mass, and abstract resource bounds for valid
  programs.
* `measuredTableauCode_correct`: correctness of the compiled measurement update on encoded
  tableau bits.
* `rawPhysicalTime`: matching raw and physical executions with tape conservation and a trace
  length bound.
* `rawFrontier`: live execution of the raw trace and a space bound for every executable prefix.

## References

* [Gottesman, 1997][Gottesman1997]
* [Aaronson and Gottesman, 2004][AaronsonGottesman2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalshMoment.Forrelation

set_option autoImplicit false

namespace Qatlib.Concepts.CliffordTheory.TableauSim

open Qatlib
open Matrix

/-- Finite adaptive stabilizer programs with Clifford gates, random Pauli measurements,
deterministic outcomes, and termination. -/
inductive Program (n m : ℕ) where
  | halt
  | gate (g : CliffordGate n) (next : Program n m)
  | random (row : Fin m) (measured : PauliElem n)
      (onFalse onTrue : Program n m)
  | deterministic (measured : PauliElem n) (outcome : Bool) (next : Program n m)

namespace Program

/-- The maximum number of gate and measurement steps along a branch of a program. -/
def maxSteps {n m : ℕ} : Program n m → ℕ
  | .halt => 0
  | .gate _ next => 1 + next.maxSteps
  | .random _ _ onFalse onTrue => 1 + max onFalse.maxSteps onTrue.maxSteps
  | .deterministic _ _ next => 1 + next.maxSteps

/-- The maximum number of random measurement bits consumed along a branch of a program. -/
def maxFairBits {n m : ℕ} : Program n m → ℕ
  | .halt => 0
  | .gate _ next => next.maxFairBits
  | .random _ _ onFalse onTrue => 1 + max onFalse.maxFairBits onTrue.maxFairBits
  | .deterministic _ _ next => next.maxFairBits

/-- The maximum number of random and deterministic measurements along a branch of a program. -/
def maxMeasurements {n m : ℕ} : Program n m → ℕ
  | .halt => 0
  | .gate _ next => next.maxMeasurements
  | .random _ _ onFalse onTrue => 1 + max onFalse.maxMeasurements onTrue.maxMeasurements
  | .deterministic _ _ next => 1 + next.maxMeasurements

/-- Validity of a program relative to a tableau, requiring legal gates and the stabilizer
conditions for each measurement branch. -/
def Valid {n m : ℕ} (t : Tableau n m) : Program n m → Prop
  | .halt => True
  | .gate g next => legalGate g ∧ Valid (update g t) next
  | .random a p onFalse onTrue =>
      IsHermitianPauli p ∧ pauliAnticommutes (t a).decode p ∧
        Valid (measuredTableau t a p false) onFalse ∧
        Valid (measuredTableau t a p true) onTrue
  | .deterministic p b next =>
      IsHermitianPauli p ∧
        signedMeasuredPauli p b ∈ generatedSubgroup (tableauGenerators t) ∧ Valid t next

end Program

/-- The number `2 * n + 2` of bits used to encode an `n`-qubit tableau row. -/
def rowWidth (n : ℕ) : ℕ := 2 * n + 2

/-- The abstract gate cost `m * rowWidth n` for a tableau with `m` rows. -/
def gateClock (n m : ℕ) : ℕ := m * rowWidth n

/-- The abstract random measurement cost `(2 * m + 1) * rowWidth n`. -/
def randomClock (n m : ℕ) : ℕ := (2 * m + 1) * rowWidth n

/-- The abstract deterministic measurement cost `rowWidth n`. -/
def deterministicClock (n : ℕ) : ℕ := rowWidth n

/-- The uniform quadratic step bound `6 * (n + 1) ^ 2`. -/
def stepPolynomial (n : ℕ) : ℕ := 6 * (n + 1) ^ 2

/-- The abstract live space `(m + 2) * rowWidth n + recordCount`, including stored measurement
outcomes. -/
def liveSpace (n m recordCount : ℕ) : ℕ := (m + 2) * rowWidth n + recordCount

/-- The quadratic tableau space bound `4 * (n + 1) ^ 2`. -/
def spacePolynomial (n : ℕ) : ℕ := 4 * (n + 1) ^ 2

/-- A tableau simulation state with a random bit tape, measurement outcomes, and counters for
consumed bits, elapsed cost, and peak space. -/
structure Machine (n m : ℕ) where
  tableau : Tableau n m
  tape : List Bool
  outcomes : List Bool
  fairBits : ℕ
  elapsed : ℕ
  peakSpace : ℕ

/-- Initialize the simulator with a tableau and random tape, empty outcomes, zero time and bit
counters, and the initial live space. -/
def initial {n m : ℕ} (tableau : Tableau n m) (tape : List Bool) : Machine n m where
  tableau := tableau
  tape := tape
  outcomes := []
  fairBits := 0
  elapsed := 0
  peakSpace := liveSpace n m 0

/-- Return the stored measurement outcomes in chronological order. -/
def records {n m : ℕ} (s : Machine n m) : List Bool := s.outcomes.reverse

/-- Apply a Clifford gate to the tableau and update the abstract elapsed cost and peak space. -/
def gateStep {n m : ℕ} (s : Machine n m) (g : CliffordGate n) : Machine n m where
  tableau := update g s.tableau
  tape := s.tape
  outcomes := s.outcomes
  fairBits := s.fairBits
  elapsed := s.elapsed + gateClock n m
  peakSpace := max s.peakSpace (liveSpace n m s.outcomes.length)

/-- Update one tableau row for a Pauli measurement, replacing the pivot by the signed observable
and multiplying anticommuting nonpivot rows by the pivot. -/
def measureRow {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n) (b : Bool)
    (i : Fin m) : Row n :=
  if i = a₀ then Qatlib.Concepts.PauliClifford.PauliAlgebra.encode (signedMeasuredPauli p b)
  else if symplecticForm (symplecticVec (t i).decode.word) (symplecticVec p.word) = 0 then t i
  else (t i).mul (t a₀)

/-- The tableau obtained by applying `measureRow` to every row for a specified measurement
outcome. -/
def measureTableau {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n) (b : Bool) :
    Tableau n m :=
  fun i => measureRow t a₀ p b i

/-- The explicit rowwise measurement update agrees with `measuredTableau`. -/
theorem measureTableau_eq {n m : ℕ} (t : Tableau n m) (a₀ : Fin m) (p : PauliElem n)
    (b : Bool) : measureTableau t a₀ p b = measuredTableau t a₀ p b := by
  funext i
  by_cases hi : i = a₀
  · simp [measureTableau, measureRow, measuredTableau, measuredRow, hi]
  · by_cases hc : pauliCommute (t i).decode p
    · simp [measureTableau, measureRow, measuredTableau, measuredRow, hi,
        pauliCommute, symplecticVec]
    · simp [measureTableau, measureRow, measuredTableau, measuredRow, hi,
        pauliCommute, symplecticVec]

/-- Perform a random measurement update with a specified outcome and remaining tape, recording
one consumed fair bit and updating the resource counters. -/
def randomStep {n m : ℕ} (s : Machine n m) (a : Fin m) (p : PauliElem n)
    (b : Bool) (rest : List Bool) : Machine n m where
  tableau := measureTableau s.tableau a p b
  tape := rest
  outcomes := b :: s.outcomes
  fairBits := s.fairBits + 1
  elapsed := s.elapsed + randomClock n m
  peakSpace := max s.peakSpace (liveSpace n m (b :: s.outcomes).length)

/-- Record a deterministic outcome while updating the abstract elapsed cost and peak space. -/
def deterministicStep {n m : ℕ} (s : Machine n m) (b : Bool) : Machine n m where
  tableau := s.tableau
  tape := s.tape
  outcomes := b :: s.outcomes
  fairBits := s.fairBits
  elapsed := s.elapsed + deterministicClock n
  peakSpace := max s.peakSpace (liveSpace n m (b :: s.outcomes).length)

/-- Execute a finite tableau program using the supplied random tape, returning `none` when a
random measurement exhausts the tape. -/
def execute {n m : ℕ} : Program n m → Machine n m → Option (Machine n m)
  | .halt, s => some s
  | .gate g next, s => execute next (gateStep s g)
  | .random a p onFalse onTrue, s =>
      match s.tape with
      | [] => none
      | b :: rest =>
          match b with
          | false => execute onFalse (randomStep s a p false rest)
          | true => execute onTrue (randomStep s a p true rest)
  | .deterministic _ b next, s => execute next (deterministicStep s b)

/-- When `m ≤ n`, each abstract gate or measurement clock is bounded by `stepPolynomial n`. -/
theorem clocks_le_stepPolynomial {n m : ℕ} (hm : m ≤ n) :
    gateClock n m ≤ stepPolynomial n ∧
      randomClock n m ≤ stepPolynomial n ∧ deterministicClock n ≤ stepPolynomial n := by
  have hrow : rowWidth n = 2 * (n + 1) := by simp [rowWidth, Nat.mul_add]
  refine ⟨?_, ?_, ?_⟩
  · calc gateClock n m = m * rowWidth n := rfl
      _ ≤ n * rowWidth n := Nat.mul_le_mul_right _ hm
      _ ≤ stepPolynomial n := by rw [hrow, stepPolynomial]; nlinarith
  · calc randomClock n m = (2 * m + 1) * rowWidth n := rfl
      _ ≤ (2 * n + 1) * rowWidth n := by
        apply Nat.mul_le_mul_right
        omega
      _ ≤ stepPolynomial n := by rw [hrow, stepPolynomial]; nlinarith
  · rw [deterministicClock, hrow, stepPolynomial]
    nlinarith

/-- When `m ≤ n`, live space is bounded by `spacePolynomial n` plus the number of stored
outcomes. This is a tableau space estimate in the setting of [AaronsonGottesman2004]. -/
theorem liveSpace_le {n m recordCount : ℕ} (hm : m ≤ n) :
    liveSpace n m recordCount ≤ spacePolynomial n + recordCount := by
  have hrow : rowWidth n = 2 * (n + 1) := by simp [rowWidth, Nat.mul_add]
  have hmul : (m + 2) * rowWidth n ≤ (n + 2) * rowWidth n := by
    apply Nat.mul_le_mul_right
    omega
  unfold liveSpace spacePolynomial
  rw [hrow] at hmul ⊢
  nlinarith

/-- The tableau component of `gateStep` is the result of running the singleton gate word. -/
@[simp] theorem gateStep_tableau {n m : ℕ} (s : Machine n m) (g : CliffordGate n) :
    (gateStep s g).tableau = run [g] s.tableau := rfl

/-- A gate step increases elapsed cost by `gateClock n m`. -/
@[simp] theorem gateStep_elapsed {n m : ℕ} (s : Machine n m) (g : CliffordGate n) :
    (gateStep s g).elapsed = s.elapsed + gateClock n m := rfl

/-- A gate step preserves the consumed fair bit counter. -/
@[simp] theorem gateStep_fairBits {n m : ℕ} (s : Machine n m) (g : CliffordGate n) :
    (gateStep s g).fairBits = s.fairBits := rfl

/-- The tableau component of `randomStep` is the corresponding measured tableau. -/
@[simp] theorem randomStep_tableau {n m : ℕ} (s : Machine n m) (a : Fin m)
    (p : PauliElem n) (b : Bool) (rest : List Bool) :
    (randomStep s a p b rest).tableau = measuredTableau s.tableau a p b := by
  change measureTableau s.tableau a p b = measuredTableau s.tableau a p b
  exact measureTableau_eq s.tableau a p b

/-- A random step sets the random tape to the specified remaining tape. -/
@[simp] theorem randomStep_tape {n m : ℕ} (s : Machine n m) (a : Fin m)
    (p : PauliElem n) (b : Bool) (rest : List Bool) :
    (randomStep s a p b rest).tape = rest := rfl

/-- A random step increases the consumed fair bit counter by one. -/
@[simp] theorem randomStep_fairBits {n m : ℕ} (s : Machine n m) (a : Fin m)
    (p : PauliElem n) (b : Bool) (rest : List Bool) :
    (randomStep s a p b rest).fairBits = s.fairBits + 1 := rfl

/-- A random step increases elapsed cost by `randomClock n m`. -/
@[simp] theorem randomStep_elapsed {n m : ℕ} (s : Machine n m) (a : Fin m)
    (p : PauliElem n) (b : Bool) (rest : List Bool) :
    (randomStep s a p b rest).elapsed = s.elapsed + randomClock n m := rfl

/-- A deterministic measurement step preserves the tableau. -/
@[simp] theorem deterministicStep_tableau {n m : ℕ} (s : Machine n m) (b : Bool) :
    (deterministicStep s b).tableau = s.tableau := rfl

/-- A deterministic measurement step preserves the random tape. -/
@[simp] theorem deterministicStep_tape {n m : ℕ} (s : Machine n m) (b : Bool) :
    (deterministicStep s b).tape = s.tape := rfl

/-- A deterministic measurement step preserves the consumed fair bit counter. -/
@[simp] theorem deterministicStep_fairBits {n m : ℕ} (s : Machine n m) (b : Bool) :
    (deterministicStep s b).fairBits = s.fairBits := rfl

/-- A deterministic measurement step increases elapsed cost by `deterministicClock n`. -/
@[simp] theorem deterministicStep_elapsed {n m : ℕ} (s : Machine n m) (b : Bool) :
    (deterministicStep s b).elapsed = s.elapsed + deterministicClock n := rfl

/-- Execution succeeds whenever the tape contains at least the program's maximum required number
of fair bits. -/
theorem execute_some {n m : ℕ} (program : Program n m) :
    ∀ (s : Machine n m), program.maxFairBits ≤ s.tape.length →
      ∃ result, execute program s = some result := by
  induction program with
  | halt =>
      intro s _
      exact ⟨s, rfl⟩
  | gate g next ih =>
      intro s h
      simpa [execute] using! ih (gateStep s g) h
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s h
      cases htape : s.tape with
      | nil =>
          simp [htape, Program.maxFairBits] at h
      | cons b rest =>
          simp only [Program.maxFairBits, htape, List.length_cons] at h
          cases b with
          | false =>
              have hbudget : onFalse.maxFairBits ≤ rest.length := by
                have hmax := Nat.le_max_left onFalse.maxFairBits onTrue.maxFairBits
                omega
              obtain ⟨result, hr⟩ := ihFalse (randomStep s a p false rest) hbudget
              exact ⟨result, by simpa [execute, htape] using! hr⟩
          | true =>
              have hbudget : onTrue.maxFairBits ≤ rest.length := by
                have hmax := Nat.le_max_right onFalse.maxFairBits onTrue.maxFairBits
                omega
              obtain ⟨result, hr⟩ := ihTrue (randomStep s a p true rest) hbudget
              exact ⟨result, by simpa [execute, htape] using! hr⟩
  | deterministic p b next ih =>
      intro s h
      simpa [execute] using! ih (deterministicStep s b) h

/-- For `m ≤ n`, successful execution adds at most `program.maxSteps * stepPolynomial n` to
elapsed cost. -/
theorem execute_elapsed_le {n m : ℕ} (program : Program n m) (hm : m ≤ n) :
    ∀ {s result : Machine n m}, execute program s = some result →
      result.elapsed ≤ s.elapsed + program.maxSteps * stepPolynomial n := by
  induction program with
  | halt =>
      intro s result h
      cases h
      simp [Program.maxSteps]
  | gate g next ih =>
      intro s result h
      have h' : execute next (gateStep s g) = some result := by simpa [execute] using! h
      have hrec := ih h'
      have hclock := (clocks_le_stepPolynomial (n := n) (m := m) hm).1
      simp only [gateStep_elapsed] at hrec
      simp only [Program.maxSteps]
      nlinarith
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s result h
      cases htape : s.tape with
      | nil => simp [execute, htape] at h
      | cons b rest =>
          cases b with
          | false =>
              have h' : execute onFalse (randomStep s a p false rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihFalse h'
              have hclock := (clocks_le_stepPolynomial (n := n) (m := m) hm).2.1
              have hsteps : onFalse.maxSteps ≤ max onFalse.maxSteps onTrue.maxSteps :=
                Nat.le_max_left _ _
              simp only [randomStep_elapsed] at hrec
              simp only [Program.maxSteps]
              nlinarith
          | true =>
              have h' : execute onTrue (randomStep s a p true rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihTrue h'
              have hclock := (clocks_le_stepPolynomial (n := n) (m := m) hm).2.1
              have hsteps : onTrue.maxSteps ≤ max onFalse.maxSteps onTrue.maxSteps :=
                Nat.le_max_right _ _
              simp only [randomStep_elapsed] at hrec
              simp only [Program.maxSteps]
              nlinarith
  | deterministic p b next ih =>
      intro s result h
      have h' : execute next (deterministicStep s b) = some result := by simpa [execute] using! h
      have hrec := ih h'
      have hclock := (clocks_le_stepPolynomial (n := n) (m := m) hm).2.2
      simp only [deterministicStep_elapsed] at hrec
      simp only [Program.maxSteps]
      nlinarith

/-- Successful execution consumes at most `program.maxFairBits` additional fair bits. -/
theorem execute_fairBits_le {n m : ℕ} (program : Program n m) :
    ∀ {s result : Machine n m}, execute program s = some result →
      result.fairBits ≤ s.fairBits + program.maxFairBits := by
  induction program with
  | halt =>
      intro s result h
      cases h
      simp [Program.maxFairBits]
  | gate g next ih =>
      intro s result h
      have hrec := ih h
      simpa [Program.maxFairBits] using! hrec
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s result h
      cases htape : s.tape with
      | nil => simp [execute, htape] at h
      | cons b rest =>
          cases b with
          | false =>
              have h' : execute onFalse (randomStep s a p false rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihFalse h'
              have hmax : onFalse.maxFairBits ≤ max onFalse.maxFairBits onTrue.maxFairBits :=
                Nat.le_max_left _ _
              simp only [randomStep_fairBits] at hrec
              simp only [Program.maxFairBits]
              omega
          | true =>
              have h' : execute onTrue (randomStep s a p true rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihTrue h'
              have hmax : onTrue.maxFairBits ≤ max onFalse.maxFairBits onTrue.maxFairBits :=
                Nat.le_max_right _ _
              simp only [randomStep_fairBits] at hrec
              simp only [Program.maxFairBits]
              omega
  | deterministic p b next ih =>
      intro s result h
      have hrec := ih h
      simpa [Program.maxFairBits] using! hrec

/-- Successful execution appends at most `program.maxMeasurements` measurement outcomes. -/
theorem execute_outcomes_length_le {n m : ℕ} (program : Program n m) :
    ∀ {s result : Machine n m}, execute program s = some result →
      result.outcomes.length ≤ s.outcomes.length + program.maxMeasurements := by
  induction program with
  | halt =>
      intro s result h
      cases h
      simp [Program.maxMeasurements]
  | gate g next ih =>
      intro s result h
      have hrec := ih h
      simpa [Program.maxMeasurements, gateStep] using! hrec
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s result h
      cases htape : s.tape with
      | nil => simp [execute, htape] at h
      | cons b rest =>
          cases b with
          | false =>
              have h' : execute onFalse (randomStep s a p false rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihFalse h'
              have hmax : onFalse.maxMeasurements ≤ max onFalse.maxMeasurements onTrue.maxMeasurements :=
                Nat.le_max_left _ _
              simp only [randomStep, List.length_cons] at hrec
              simp only [Program.maxMeasurements]
              omega
          | true =>
              have h' : execute onTrue (randomStep s a p true rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihTrue h'
              have hmax : onTrue.maxMeasurements ≤ max onFalse.maxMeasurements onTrue.maxMeasurements :=
                Nat.le_max_right _ _
              simp only [randomStep, List.length_cons] at hrec
              simp only [Program.maxMeasurements]
              omega
  | deterministic p b next ih =>
      intro s result h
      have hrec := ih h
      simp only [deterministicStep, List.length_cons] at hrec
      simp only [Program.maxMeasurements]
      omega

/-- For `m ≤ n`, an initial peak space bound extends through successful execution with an
additional allowance of `program.maxMeasurements`. -/
theorem execute_peakSpace_le {n m : ℕ} (program : Program n m) (hm : m ≤ n) :
    ∀ {s result : Machine n m}, execute program s = some result →
      s.peakSpace ≤ spacePolynomial n + s.outcomes.length →
      result.peakSpace ≤ spacePolynomial n + s.outcomes.length + program.maxMeasurements := by
  induction program with
  | halt =>
      intro s result hrun hs
      cases hrun
      simpa [Program.maxMeasurements] using! hs
  | gate g next ih =>
      intro s result hrun hs
      have h' : execute next (gateStep s g) = some result := by simpa [execute] using! hrun
      have hstart : (gateStep s g).peakSpace ≤
          spacePolynomial n + (gateStep s g).outcomes.length := by
        simp only [gateStep]
        apply max_le hs
        exact liveSpace_le hm
      have hrec := ih h' hstart
      simpa [Program.maxMeasurements, gateStep] using! hrec
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s result hrun hs
      cases htape : s.tape with
      | nil => simp [execute, htape] at hrun
      | cons b rest =>
          cases b with
          | false =>
              have h' : execute onFalse (randomStep s a p false rest) = some result := by
                simpa [execute, htape] using! hrun
              have hstart : (randomStep s a p false rest).peakSpace ≤
                  spacePolynomial n + (randomStep s a p false rest).outcomes.length := by
                simp only [randomStep, List.length_cons]
                apply max_le
                · omega
                · exact liveSpace_le hm
              have hrec := ihFalse h' hstart
              have hmax : onFalse.maxMeasurements ≤
                  max onFalse.maxMeasurements onTrue.maxMeasurements := Nat.le_max_left _ _
              simp only [randomStep, List.length_cons, Program.maxMeasurements] at hrec ⊢
              omega
          | true =>
              have h' : execute onTrue (randomStep s a p true rest) = some result := by
                simpa [execute, htape] using! hrun
              have hstart : (randomStep s a p true rest).peakSpace ≤
                  spacePolynomial n + (randomStep s a p true rest).outcomes.length := by
                simp only [randomStep, List.length_cons]
                apply max_le
                · omega
                · exact liveSpace_le hm
              have hrec := ihTrue h' hstart
              have hmax : onTrue.maxMeasurements ≤
                  max onFalse.maxMeasurements onTrue.maxMeasurements := Nat.le_max_right _ _
              simp only [randomStep, List.length_cons, Program.maxMeasurements] at hrec ⊢
              omega
  | deterministic p b next ih =>
      intro s result hrun hs
      have h' : execute next (deterministicStep s b) = some result := by simpa [execute] using! hrun
      have hstart : (deterministicStep s b).peakSpace ≤
          spacePolynomial n + (deterministicStep s b).outcomes.length := by
        simp only [deterministicStep, List.length_cons]
        apply max_le
        · omega
        · exact liveSpace_le hm
      have hrec := ih h' hstart
      simp only [deterministicStep, List.length_cons, Program.maxMeasurements] at hrec ⊢
      omega

/-- For `m ≤ n`, the initial peak space is bounded by `spacePolynomial n` plus the initial
outcome count. -/
theorem initial_peakSpace_le {n m : ℕ} (tableau : Tableau n m) (tape : List Bool)
    (hm : m ≤ n) :
    (initial (n := n) (m := m) tableau tape).peakSpace ≤
      spacePolynomial n + (initial (n := n) (m := m) tableau tape).outcomes.length := by
  exact liveSpace_le hm

/-- Anticommuting Pauli elements have operator products related by a minus sign. -/
theorem op_anticommute_of_pauliAnticommutes {n : ℕ} {p q : PauliElem n}
    (hanti : pauliAnticommutes p q) : op p * op q = -(op q * op p) := by
  have hs := pauliWordOp_symplectic n p.word q.word
  have hform : symplecticForm (symplecticX p.word, symplecticZ p.word)
      (symplecticX q.word, symplecticZ q.word) = 1 :=
    symplecticForm_eq_one_of_anticommutes hanti
  rw [hform] at hs
  simp only [Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_val_one, pow_one,
      neg_one_smul] at hs
  simp only [op, Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul]
  module

/-- The projective branch of the positive Pauli projector is the projector associated with the
selected Boolean outcome. -/
theorem projectiveBranch_pauli {n : ℕ} (p : PauliElem n) (b : Bool) (ψ : QState (Reg n)) :
    ProjectiveBranch (pauliBranchProjector p true) b ψ = pauliBranchProjector p b *ᵥ ψ := by
  have hcompl : 1 - pauliBranchProjector p true = pauliBranchProjector p false := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact (pauliBranchProjector_add p).symm
  cases b with
  | false =>
      change (1 - pauliBranchProjector p true) *ᵥ ψ = pauliBranchProjector p false *ᵥ ψ
      rw [hcompl]
  | true => rfl

/-- The post-measurement state obtained by normalizing the selected Pauli projector branch. -/
noncomputable def branchState {n : ℕ} (p : PauliElem n) (b : Bool) (ψ : QState (Reg n)) :
    QState (Reg n) :=
  PostMeasure (pauliBranchProjector p b *ᵥ ψ) Finset.univ

/-- The total squared mass of a projected Pauli branch equals its projective branch mass. -/
theorem measureProb_pauliBranch {n : ℕ} (p : PauliElem n) (b : Bool) (ψ : QState (Reg n)) :
    MeasureProb (pauliBranchProjector p b *ᵥ ψ) Finset.univ =
      ProjectiveBranchMass (pauliBranchProjector p true) b ψ := by
  rw [← projectiveBranch_pauli]
  rfl

/-- A Pauli branch state is normalized whenever its branch mass is positive. -/
theorem normalized_branchState {n : ℕ} (p : PauliElem n) (b : Bool) (ψ : QState (Reg n))
    (hmass : 0 < ProjectiveBranchMass (pauliBranchProjector p true) b ψ) :
    Normalized (branchState p b ψ) := by
  apply normalized_postMeasure
  rwa [measureProb_pauliBranch]

/-- Normalizing a projected Pauli branch preserves membership in a tableau code space. -/
theorem branchState_mem {n m : ℕ} (p : PauliElem n) (b : Bool) (ψ : QState (Reg n))
    (t : Tableau n m) (hmem : pauliBranchProjector p b *ᵥ ψ ∈ codeSpace t) :
    branchState p b ψ ∈ codeSpace t := by
  have hcollapse : Collapse (pauliBranchProjector p b *ᵥ ψ) Finset.univ =
      pauliBranchProjector p b *ᵥ ψ := by
    funext x
    simp [collapse_apply]
  unfold branchState PostMeasure
  rw [hcollapse]
  exact (codeSpace t).smul_mem _ hmem

/-- A legal Clifford gate maps a normalized code-space state to a normalized state in the
updated tableau code space. -/
theorem gateStep_state {n m : ℕ} (s : Machine n m) (g : CliffordGate n)
    (hg : legalGate g) (ψ : QState (Reg n)) (hn : Normalized ψ)
    (hψ : ψ ∈ codeSpace s.tableau) :
    Normalized (Uword [g] *ᵥ ψ) ∧
      Uword [g] *ᵥ ψ ∈ codeSpace (gateStep s g).tableau := by
  have hg' : ∀ g' ∈ [g], legalGate g' := by simpa using! hg
  have hmem := (mem_run_iff [g] hg' s.tableau ψ).mpr hψ
  refine ⟨normalized_applyGate (Uword_unitary [g] hg') hn, ?_⟩
  simpa using! hmem

/-- For a consistent tableau and an anticommuting pivot, each Pauli measurement branch has
fair-bit probability and lies in the updated code space. -/
theorem randomStep_born {n m : ℕ} (s : Machine n m) (a : Fin m) (p : PauliElem n)
    (hp : IsHermitianPauli p) (hanti : pauliAnticommutes (s.tableau a).decode p)
    (b : Bool) (rest : List Bool) (ψ : QState (Reg n)) (hn : Normalized ψ)
    (hψ : ψ ∈ codeSpace s.tableau) (ht : ConsistentTableau s.tableau) :
    pauliBranchProjector p b *ᵥ ψ ∈ codeSpace (randomStep s a p b rest).tableau ∧
      ProjectiveBranchMass (pauliBranchProjector p true) b ψ = fairBitLaw.prob b := by
  have hantiOp : ∃ a' : Fin m, op (s.tableau a').decode * op p =
      -(op p * op (s.tableau a').decode) :=
    ⟨a, op_anticommute_of_pauliAnticommutes hanti⟩
  have hmem := mem_codeSpace_measuredTableau s.tableau ht a p hp hanti b ψ hψ
  have hprob := clause3RandomStep_branch_prob s.tableau ψ hψ hn p hp hantiOp
  refine ⟨?_, ?_⟩
  · simpa using! hmem
  · cases b with
    | false => exact hprob.2
    | true => exact hprob.1

/-- For a consistent tableau and an anticommuting pivot, the normalized Pauli branch lies in the
randomly updated tableau code space. -/
theorem randomStep_branchState {n m : ℕ} (s : Machine n m) (a : Fin m) (p : PauliElem n)
    (hp : IsHermitianPauli p) (hanti : pauliAnticommutes (s.tableau a).decode p)
    (b : Bool) (rest : List Bool) (ψ : QState (Reg n)) (hn : Normalized ψ)
    (hψ : ψ ∈ codeSpace s.tableau) (ht : ConsistentTableau s.tableau) :
    Normalized (branchState p b ψ) ∧
      branchState p b ψ ∈ codeSpace (randomStep s a p b rest).tableau := by
  have hb := randomStep_born s a p hp hanti b rest ψ hn hψ ht
  have hpos : 0 < ProjectiveBranchMass (pauliBranchProjector p true) b ψ := by
    rw [hb.2]
    cases b <;> norm_num [fairBitLaw]
  exact ⟨normalized_branchState p b ψ hpos, branchState_mem p b ψ _ hb.1⟩

/-- A signed measured Pauli in the generated stabilizer subgroup fixes every vector in the
tableau code space. -/
theorem op_signedMeasuredPauli_fixes {n m : ℕ} (t : Tableau n m) (p : PauliElem n)
    (b : Bool) (hgen : signedMeasuredPauli p b ∈ generatedSubgroup (tableauGenerators t))
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    op (signedMeasuredPauli p b) *ᵥ ψ = ψ := by
  obtain ⟨mask, hmask, hprod⟩ := hgen
  rw [← hprod]
  exact op_maskProduct_fixes_codeSpace t ψ hψ mask hmask

/-- If the signed measured Pauli belongs to the generated stabilizer subgroup, its selected
branch projector fixes code-space vectors. -/
theorem deterministic_branch {n m : ℕ} (t : Tableau n m) (p : PauliElem n)
    (b : Bool) (hgen : signedMeasuredPauli p b ∈ generatedSubgroup (tableauGenerators t))
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    pauliBranchProjector p b *ᵥ ψ = ψ := by
  have hs := op_signedMeasuredPauli_fixes t p b hgen ψ hψ
  cases b with
  | false =>
      have hs' := hs
      rw [op_signedMeasuredPauli] at hs'
      simp only [Bool.false_eq_true, ↓reduceIte] at hs'
      have hfix : op p *ᵥ ψ = -ψ := by
        calc op p *ᵥ ψ = -((-op p) *ᵥ ψ) := by rw [Matrix.neg_mulVec, neg_neg]
          _ = -ψ := congrArg Neg.neg hs'
      have hstep : pauliBranchProjector p false *ᵥ ψ =
          ((2 : ℂ)⁻¹) • ((1 - op p) *ᵥ ψ) := by
        rw [pauliBranchProjector]
        exact Matrix.smul_mulVec _ _ _
      rw [hstep, Matrix.sub_mulVec, Matrix.one_mulVec, hfix]
      funext x
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply]
      calc ((2 : ℂ)⁻¹) * (ψ x - -ψ x) = ((2 : ℂ)⁻¹) * (2 * ψ x) := by ring
        _ = ((2 : ℂ)⁻¹ * 2) * ψ x := by ring
        _ = ψ x := by rw [half_mul_two]; ring
  | true =>
      have hfix : op p *ᵥ ψ = ψ := by simpa [signedMeasuredPauli] using! hs
      have hstep : pauliBranchProjector p true *ᵥ ψ =
          ((2 : ℂ)⁻¹) • ((1 + op p) *ᵥ ψ) := by
        rw [pauliBranchProjector]
        exact Matrix.smul_mulVec _ _ _
      rw [hstep, Matrix.add_mulVec, Matrix.one_mulVec, hfix]
      funext x
      simp only [Pi.smul_apply, Pi.add_apply]
      calc ((2 : ℂ)⁻¹) * (ψ x + ψ x) = ((2 : ℂ)⁻¹) * (2 * ψ x) := by ring
        _ = ((2 : ℂ)⁻¹ * 2) * ψ x := by ring
        _ = ψ x := by rw [half_mul_two]; ring

/-- For a normalized code-space state, a stabilizer-determined Hermitian Pauli outcome has mass
one and the opposite outcome has mass zero. -/
theorem deterministic_born {n m : ℕ} (t : Tableau n m) (p : PauliElem n)
    (hp : IsHermitianPauli p) (b : Bool)
    (hgen : signedMeasuredPauli p b ∈ generatedSubgroup (tableauGenerators t))
    (ψ : QState (Reg n)) (hn : Normalized ψ) (hψ : ψ ∈ codeSpace t) :
    ProjectiveBranchMass (pauliBranchProjector p true) b ψ = 1 ∧
      ProjectiveBranchMass (pauliBranchProjector p true) (otherOutcome b) ψ = 0 := by
  have hid := deterministic_branch t p b hgen ψ hψ
  have hsel : ProjectiveBranchMass (pauliBranchProjector p true) b ψ = 1 := by
    unfold ProjectiveBranchMass
    rw [projectiveBranch_pauli, hid, measureProb_univ hn]
  have hsum := projectiveBranchMass_add (pauliBranchProjector_isOrthogonalProjector hp true) ψ
  rw [measureProb_univ hn] at hsum
  cases b with
  | false =>
      have hz : ProjectiveBranchMass (pauliBranchProjector p true) true ψ = 0 := by
        linarith
      exact ⟨hsel, by simpa [otherOutcome] using! hz⟩
  | true =>
      have hz : ProjectiveBranchMass (pauliBranchProjector p true) false ψ = 0 := by
        linarith
      exact ⟨hsel, by simpa [otherOutcome] using! hz⟩

/-- A deterministic measurement branch remains in the unchanged tableau code space, with mass
one for the selected outcome and zero for the opposite outcome. -/
theorem deterministicStep_born {n m : ℕ} (s : Machine n m) (p : PauliElem n)
    (hp : IsHermitianPauli p) (b : Bool)
    (hgen : signedMeasuredPauli p b ∈ generatedSubgroup (tableauGenerators s.tableau))
    (ψ : QState (Reg n)) (hn : Normalized ψ) (hψ : ψ ∈ codeSpace s.tableau) :
    pauliBranchProjector p b *ᵥ ψ ∈ codeSpace (deterministicStep s b).tableau ∧
      ProjectiveBranchMass (pauliBranchProjector p true) b ψ = 1 ∧
      ProjectiveBranchMass (pauliBranchProjector p true) (otherOutcome b) ψ = 0 := by
  have hid := deterministic_branch s.tableau p b hgen ψ hψ
  have hprob := deterministic_born s.tableau p hp b hgen ψ hn hψ
  refine ⟨?_, hprob⟩
  rw [deterministicStep_tableau, hid]
  exact hψ

/-- A stabilizer-determined Hermitian Pauli branch is normalized and remains in the code space
after a deterministic step. -/
theorem deterministicStep_branchState {n m : ℕ} (s : Machine n m) (p : PauliElem n)
    (hp : IsHermitianPauli p) (b : Bool)
    (hgen : signedMeasuredPauli p b ∈ generatedSubgroup (tableauGenerators s.tableau))
    (ψ : QState (Reg n)) (hn : Normalized ψ) (hψ : ψ ∈ codeSpace s.tableau) :
    Normalized (branchState p b ψ) ∧
      branchState p b ψ ∈ codeSpace (deterministicStep s b).tableau := by
  have hb := deterministicStep_born s p hp b hgen ψ hn hψ
  have hpos : 0 < ProjectiveBranchMass (pauliBranchProjector p true) b ψ := by
    rw [hb.2.1]
    norm_num
  exact ⟨normalized_branchState p b ψ hpos, branchState_mem p b ψ _ hb.1⟩

namespace Program

/-- Count the random bits consumed along the branch selected by a tape, stopping the count when
the tape is exhausted. -/
def consumedFairBits {n m : ℕ} : Program n m → List Bool → ℕ
  | .halt, _ => 0
  | .gate _ next, tape => consumedFairBits next tape
  | .random _ _ _ _, [] => 0
  | .random _ _ onFalse onTrue, b :: rest =>
      1 + match b with
      | false => consumedFairBits onFalse rest
      | true => consumedFairBits onTrue rest
  | .deterministic _ _ next, tape => consumedFairBits next tape

end Program

/-- Successful execution increases the fair bit counter by exactly `Program.consumedFairBits
program s.tape`. -/
theorem execute_fairBits_eq {n m : ℕ} (program : Program n m) :
    ∀ {s result : Machine n m}, execute program s = some result →
      result.fairBits = s.fairBits + Program.consumedFairBits program s.tape := by
  induction program with
  | halt =>
      intro s result h
      cases h
      rfl
  | gate g next ih =>
      intro s result h
      have h' : execute next (gateStep s g) = some result := by simpa [execute] using! h
      have hrec := ih h'
      simpa [Program.consumedFairBits, gateStep] using! hrec
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s result h
      cases htape : s.tape with
      | nil => simp [execute, htape] at h
      | cons b rest =>
          cases b with
          | false =>
              have h' : execute onFalse (randomStep s a p false rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihFalse h'
              simp only [randomStep_fairBits, randomStep_tape] at hrec
              simp only [Program.consumedFairBits]
              omega
          | true =>
              have h' : execute onTrue (randomStep s a p true rest) = some result := by
                simpa [execute, htape] using! h
              have hrec := ihTrue h'
              simp only [randomStep_fairBits, randomStep_tape] at hrec
              simp only [Program.consumedFairBits]
              omega
  | deterministic p b next ih =>
      intro s result h
      have h' : execute next (deterministicStep s b) = some result := by simpa [execute] using! h
      have hrec := ih h'
      simpa [Program.consumedFairBits, deterministicStep] using! hrec

/-- Successful execution of a valid program preserves consistency of the tableau. -/
theorem execute_consistent {n m : ℕ} (program : Program n m) :
    ∀ {s result : Machine n m}, execute program s = some result →
      Program.Valid s.tableau program → ConsistentTableau s.tableau →
      ConsistentTableau result.tableau := by
  induction program with
  | halt =>
      intro s result h _ ht
      cases h
      exact ht
  | gate g next ih =>
      intro s result h hv ht
      have h' : execute next (gateStep s g) = some result := by simpa [execute] using! h
      have hg : ∀ g' ∈ [g], legalGate g' := by simpa using! hv.1
      have ht' : ConsistentTableau (gateStep s g).tableau := by
        rw [gateStep_tableau]
        exact Qatlib.Concepts.PauliClifford.PauliAlgebra.consistent_run
          [g] hg s.tableau ht
      exact ih h' hv.2 ht'
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s result h hv ht
      rcases hv with ⟨hp, hanti, hvFalse, hvTrue⟩
      cases htape : s.tape with
      | nil => simp [execute, htape] at h
      | cons b rest =>
          cases b with
          | false =>
              have h' : execute onFalse (randomStep s a p false rest) = some result := by
                simpa [execute, htape] using! h
              have ht' : ConsistentTableau (randomStep s a p false rest).tableau := by
                rw [randomStep_tableau]
                exact consistent_measuredTableau s.tableau ht a p hp hanti false
              have hv' : Program.Valid (randomStep s a p false rest).tableau onFalse := by
                rw [randomStep_tableau]
                exact hvFalse
              exact ihFalse h' hv' ht'
          | true =>
              have h' : execute onTrue (randomStep s a p true rest) = some result := by
                simpa [execute, htape] using! h
              have ht' : ConsistentTableau (randomStep s a p true rest).tableau := by
                rw [randomStep_tableau]
                exact consistent_measuredTableau s.tableau ht a p hp hanti true
              have hv' : Program.Valid (randomStep s a p true rest).tableau onTrue := by
                rw [randomStep_tableau]
                exact hvTrue
              exact ihTrue h' hv' ht'
  | deterministic p b next ih =>
      intro s result h hv ht
      have h' : execute next (deterministicStep s b) = some result := by simpa [execute] using! h
      exact ih h' hv.2.2 ht

/-- A simulation result containing the classical machine, a quantum state, and the joint mass of
the selected measurement branch. -/
structure PhysicalResult (n m : ℕ) where
  machine : Machine n m
  state : QState (Reg n)
  jointMass : ℝ

namespace PhysicalResult

/-- Multiply the joint mass of a physical result by a real factor. -/
noncomputable def scale {n m : ℕ} (mass : ℝ) (r : PhysicalResult n m) : PhysicalResult n m where
  machine := r.machine
  state := r.state
  jointMass := mass * r.jointMass

end PhysicalResult

/-- Execute a tableau program together with quantum gate evolution, normalized measurement
branches, and their joint probability mass. -/
noncomputable def physicalExecute {n m : ℕ} :
    Program n m → Machine n m → QState (Reg n) → Option (PhysicalResult n m)
  | .halt, s, ψ => some ⟨s, ψ, 1⟩
  | .gate g next, s, ψ => physicalExecute next (gateStep s g) (Uword [g] *ᵥ ψ)
  | .random a p onFalse onTrue, s, ψ =>
      match s.tape with
      | [] => none
      | b :: rest =>
          match b with
          | false =>
              match physicalExecute onFalse (randomStep s a p false rest) (branchState p false ψ) with
              | none => none
              | some r => some (r.scale (ProjectiveBranchMass (pauliBranchProjector p true) false ψ))
          | true =>
              match physicalExecute onTrue (randomStep s a p true rest) (branchState p true ψ) with
              | none => none
              | some r => some (r.scale (ProjectiveBranchMass (pauliBranchProjector p true) true ψ))
  | .deterministic p b next, s, ψ =>
      match physicalExecute next (deterministicStep s b) (branchState p b ψ) with
      | none => none
      | some r => some (r.scale (ProjectiveBranchMass (pauliBranchProjector p true) b ψ))

/-- Physical execution succeeds when the random tape meets the program's maximum fair bit
requirement. -/
theorem physicalExecute_some {n m : ℕ} (program : Program n m) :
    ∀ (s : Machine n m) (ψ : QState (Reg n)), program.maxFairBits ≤ s.tape.length →
      ∃ result, physicalExecute program s ψ = some result := by
  induction program with
  | halt =>
      intro s ψ _
      exact ⟨⟨s, ψ, 1⟩, rfl⟩
  | gate g next ih =>
      intro s ψ h
      simpa [physicalExecute] using! ih (gateStep s g) (Uword [g] *ᵥ ψ) h
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s ψ h
      cases htape : s.tape with
      | nil => simp [htape, Program.maxFairBits] at h
      | cons b rest =>
          simp only [Program.maxFairBits, htape, List.length_cons] at h
          cases b with
          | false =>
              have hbudget : onFalse.maxFairBits ≤ rest.length := by
                have hmax := Nat.le_max_left onFalse.maxFairBits onTrue.maxFairBits
                omega
              obtain ⟨r, hr⟩ :=
                  ihFalse (randomStep s a p false rest) (branchState p false ψ) hbudget
              exact ⟨r.scale (ProjectiveBranchMass (pauliBranchProjector p true) false ψ),
                by simp [physicalExecute, htape, hr]⟩
          | true =>
              have hbudget : onTrue.maxFairBits ≤ rest.length := by
                have hmax := Nat.le_max_right onFalse.maxFairBits onTrue.maxFairBits
                omega
              obtain ⟨r, hr⟩ := ihTrue (randomStep s a p true rest) (branchState p true ψ) hbudget
              exact ⟨r.scale (ProjectiveBranchMass (pauliBranchProjector p true) true ψ),
                by simp [physicalExecute, htape, hr]⟩
  | deterministic p b next ih =>
      intro s ψ h
      obtain ⟨r, hr⟩ := ih (deterministicStep s b) (branchState p b ψ) h
      exact ⟨r.scale (ProjectiveBranchMass (pauliBranchProjector p true) b ψ),
        by simp [physicalExecute, hr]⟩

/-- The machine component of a successful physical execution agrees with ordinary tableau
execution. -/
theorem physicalExecute_machine {n m : ℕ} (program : Program n m) :
    ∀ {s : Machine n m} {ψ : QState (Reg n)} {result : PhysicalResult n m},
      physicalExecute program s ψ = some result → execute program s = some result.machine := by
  induction program with
  | halt =>
      intro s ψ result h
      cases h
      rfl
  | gate g next ih =>
      intro s ψ result h
      simpa [execute] using! ih h
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s ψ result h
      cases htape : s.tape with
      | nil => simp [physicalExecute, htape] at h
      | cons b rest =>
          cases b with
          | false =>
              cases hr : physicalExecute onFalse (randomStep s a p false rest)
                (branchState p false ψ) with
              | none => simp [physicalExecute, htape, hr] at h
              | some r0 =>
                  have hrec := ihFalse hr
                  simp [physicalExecute, htape, hr] at h
                  cases h
                  simpa [execute, htape, PhysicalResult.scale] using! hrec
          | true =>
              cases hr : physicalExecute onTrue (randomStep s a p true rest)
                (branchState p true ψ) with
              | none => simp [physicalExecute, htape, hr] at h
              | some r0 =>
                  have hrec := ihTrue hr
                  simp [physicalExecute, htape, hr] at h
                  cases h
                  simpa [execute, htape, PhysicalResult.scale] using! hrec
  | deterministic p b next ih =>
      intro s ψ result h
      cases hr : physicalExecute next (deterministicStep s b) (branchState p b ψ) with
      | none => simp [physicalExecute, hr] at h
      | some r0 =>
          have hrec := ih hr
          simp [physicalExecute, hr] at h
          cases h
          simpa [execute, PhysicalResult.scale] using! hrec

/-- Valid physical execution from a normalized state in a consistent tableau code space
preserves normalization and code-space membership. Its joint mass is one half raised to the
number of consumed fair bits. -/
theorem physicalExecute_correct {n m : ℕ} (program : Program n m) :
    ∀ {s : Machine n m} {ψ : QState (Reg n)} {result : PhysicalResult n m},
      physicalExecute program s ψ = some result →
      Program.Valid s.tableau program → ConsistentTableau s.tableau →
      Normalized ψ → ψ ∈ codeSpace s.tableau →
      (Normalized result.state ∧ result.state ∈ codeSpace result.machine.tableau) ∧
      result.jointMass = (1 / 2 : ℝ) ^ Program.consumedFairBits program s.tape := by
  induction program with
  | halt =>
      intro s ψ result h _ _ hn hψ
      cases h
      exact ⟨⟨hn, hψ⟩, by simp [Program.consumedFairBits]⟩
  | gate g next ih =>
      intro s ψ result h hv ht hn hψ
      have hstate := gateStep_state s g hv.1 ψ hn hψ
      have hg : ∀ g' ∈ [g], legalGate g' := by simpa using! hv.1
      have ht' : ConsistentTableau (gateStep s g).tableau := by
        rw [gateStep_tableau]
        exact Qatlib.Concepts.PauliClifford.PauliAlgebra.consistent_run
          [g] hg s.tableau ht
      have hrec := ih h hv.2 ht' hstate.1 hstate.2
      simpa [Program.consumedFairBits, gateStep] using! hrec
  | random a p onFalse onTrue ihFalse ihTrue =>
      intro s ψ result h hv ht hn hψ
      rcases hv with ⟨hp, hanti, hvFalse, hvTrue⟩
      cases htape : s.tape with
      | nil => simp [physicalExecute, htape] at h
      | cons b rest =>
          cases b with
          | false =>
              cases hr : physicalExecute onFalse (randomStep s a p false rest)
                (branchState p false ψ) with
              | none => simp [physicalExecute, htape, hr] at h
              | some r0 =>
                  have hb := randomStep_branchState s a p hp hanti false rest ψ hn hψ ht
                  have ht' : ConsistentTableau (randomStep s a p false rest).tableau := by
                    rw [randomStep_tableau]
                    exact consistent_measuredTableau s.tableau ht a p hp hanti false
                  have hv' : Program.Valid (randomStep s a p false rest).tableau onFalse := by
                    rw [randomStep_tableau]
                    exact hvFalse
                  have hrec := ihFalse hr hv' ht' hb.1 hb.2
                  have hprob := (randomStep_born s a p hp hanti false rest ψ hn hψ ht).2
                  simp [physicalExecute, htape, hr] at h
                  cases h
                  refine ⟨?_, ?_⟩
                  · simpa [PhysicalResult.scale] using! hrec.1
                  · change ProjectiveBranchMass (pauliBranchProjector p true) false ψ *
                      r0.jointMass = _
                    rw [hrec.2, hprob]
                    simp [Program.consumedFairBits, fairBitLaw, pow_add]
          | true =>
              cases hr : physicalExecute onTrue (randomStep s a p true rest)
                (branchState p true ψ) with
              | none => simp [physicalExecute, htape, hr] at h
              | some r0 =>
                  have hb := randomStep_branchState s a p hp hanti true rest ψ hn hψ ht
                  have ht' : ConsistentTableau (randomStep s a p true rest).tableau := by
                    rw [randomStep_tableau]
                    exact consistent_measuredTableau s.tableau ht a p hp hanti true
                  have hv' : Program.Valid (randomStep s a p true rest).tableau onTrue := by
                    rw [randomStep_tableau]
                    exact hvTrue
                  have hrec := ihTrue hr hv' ht' hb.1 hb.2
                  have hprob := (randomStep_born s a p hp hanti true rest ψ hn hψ ht).2
                  simp [physicalExecute, htape, hr] at h
                  cases h
                  refine ⟨?_, ?_⟩
                  · simpa [PhysicalResult.scale] using! hrec.1
                  · change ProjectiveBranchMass (pauliBranchProjector p true) true ψ *
                      r0.jointMass = _
                    rw [hrec.2, hprob]
                    simp [Program.consumedFairBits, fairBitLaw, pow_add]
  | deterministic p b next ih =>
      intro s ψ result h hv ht hn hψ
      have hb := deterministicStep_branchState s p hv.1 b hv.2.1 ψ hn hψ
      cases hr : physicalExecute next (deterministicStep s b) (branchState p b ψ) with
      | none => simp [physicalExecute, hr] at h
      | some r0 =>
          have hrec := ih hr hv.2.2 ht hb.1 hb.2
          have hprob := deterministicStep_born s p hv.1 b hv.2.1 ψ hn hψ
          simp [physicalExecute, hr] at h
          cases h
          refine ⟨?_, ?_⟩
          · simpa [PhysicalResult.scale] using! hrec.1
          · change ProjectiveBranchMass (pauliBranchProjector p true) b ψ * r0.jointMass = _
            rw [hrec.2, hprob.2.1]
            simp [Program.consumedFairBits]

/-- A valid program with a sufficient tape and `m ≤ n` has a physical execution preserving
normalization, code-space membership, and tableau consistency. The result has the stated
exact branch mass and fair bit count, with quadratic abstract time and space bounds. -/
theorem frontier1 {n m : ℕ} (program : Program n m) (t : Tableau n m) (tape : List Bool)
    (ψ : QState (Reg n)) (hm : m ≤ n) (hv : Program.Valid t program)
    (ht : ConsistentTableau t) (hn : Normalized ψ) (hψ : ψ ∈ codeSpace t)
    (hbudget : program.maxFairBits ≤ tape.length) :
    ∃ result, physicalExecute program (initial t tape) ψ = some result ∧
      (Normalized result.state ∧ result.state ∈ codeSpace result.machine.tableau) ∧
      ConsistentTableau result.machine.tableau ∧
      result.jointMass = (1 / 2 : ℝ) ^ Program.consumedFairBits program tape ∧
      result.machine.fairBits = Program.consumedFairBits program tape ∧
      result.machine.elapsed ≤ program.maxSteps * stepPolynomial n ∧
      result.machine.peakSpace ≤ spacePolynomial n + program.maxMeasurements := by
  obtain ⟨result, hr⟩ := physicalExecute_some program (initial t tape) ψ hbudget
  have hmch := physicalExecute_machine program hr
  have hc := physicalExecute_correct program hr hv ht hn hψ
  have hcons := execute_consistent program hmch hv ht
  have hfair := execute_fairBits_eq program hmch
  have htime := execute_elapsed_le program hm hmch
  have hspace := execute_peakSpace_le program hm hmch (initial_peakSpace_le t tape hm)
  refine ⟨result, hr, hc.1, hcons, hc.2, ?_, ?_, ?_⟩
  · simpa [initial] using! hfair
  · simpa [initial] using! htime
  · simpa [initial] using! hspace

/-- The bit encoding of a row has length `rowWidth n`. -/
theorem rowWidth_eq_bits_length {n : ℕ} (r : Row n) : rowWidth n = r.bits.length := by
  rw [row_bits_length]
  rfl

/-- The bit encoding of an `m`-row machine tableau has length `m * rowWidth n`. -/
theorem machine_tableauBits_length {n m : ℕ} (s : Machine n m) :
    (tableauBits s.tableau).length = m * rowWidth n := by
  rw [tableau_bits_length]
  rfl

end Qatlib.Concepts.CliffordTheory.TableauSim

namespace Qatlib.Concepts.CliffordTheory.TableauSim.BitExecution

/-- An array of Boolean registers with exactly `R` entries. -/
abbrev BitBank (R : ℕ) := { a : Array Bool // a.size = R }

/-- Read a Boolean register at a bounded index. -/
def bankRead {R : ℕ} (a : BitBank R) (i : Fin R) : Bool :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

/-- Write a Boolean register at a bounded index. -/
def bankWrite {R : ℕ} (a : BitBank R) (i : Fin R) (b : Bool) : BitBank R :=
  ⟨a.val.setIfInBounds i.val b, Array.size_setIfInBounds.trans a.property⟩

/-- Reading after a register write returns the new bit at the written index and the original bit
elsewhere. -/
@[simp] theorem bankRead_write {R : ℕ} (a : BitBank R) (i k : Fin R) (b : Bool) :
    bankRead (bankWrite a i b) k = if k = i then b else bankRead a k := by
  have hk : k.val < a.val.size := by rw [a.property]; exact k.isLt
  have h := Array.getElem_setIfInBounds (xs := a.val) (i := i.val) (a := b) hk
  simpa only [bankRead, bankWrite, Fin.ext_iff, eq_comm] using! h

/-- Elementary bit-machine events for input scanning, Boolean evaluation, register access, and
output writing. -/
inductive BitAction (R : ℕ) where
  | right | left | readInput (b : Bool) | literal (b : Bool)
  | readRegister (i : Fin R) (b : Bool)
  | bnot (b : Bool) | band (a b : Bool) | bxor (a b : Bool)
  | writeRegister (i : Fin R) (b : Bool) | outputLeft | writeOutput (b : Bool)
  deriving DecidableEq, Repr

/-- Read a bit by recursively scanning from the head of a list, using `false` beyond its end. -/
def scanBit (bits : List Bool) : ℕ → Bool
  | 0 => bits.headD false
  | k + 1 => scanBit bits.tail k

/-- The input-scan trace that moves to an address, reads its bit, and returns to the starting
position. -/
def scanTrace {R : ℕ} (bits : List Bool) : ℕ → List (BitAction R)
  | 0 => [.readInput (bits.headD false)]
  | k + 1 => .right :: scanTrace bits.tail k ++ [.left]

/-- The execution relation for a bit scan, recording its input list, address, trace, and
returned bit. -/
inductive ScanExec (R : ℕ) : List Bool → ℕ → List (BitAction R) → Bool → Prop where
  | here (bits) : ScanExec R bits 0 [.readInput (bits.headD false)] (bits.headD false)
  | next (bits k trace b) : ScanExec R bits.tail k trace b →
      ScanExec R bits (k + 1) (.right :: trace ++ [.left]) b

/-- The trace produced by `scanTrace` executes a scan returning `scanBit bits k`. -/
theorem scanTrace_exec {R : ℕ} (bits : List Bool) (k : ℕ) :
    ScanExec R bits k (scanTrace bits k) (scanBit bits k) := by
  induction k generalizing bits with
  | zero => exact .here bits
  | succ k ih => exact .next bits k _ _ (ih bits.tail)

/-- Recursive bit scanning agrees with list lookup using `false` as the default. -/
theorem scanBit_getD (bits : List Bool) (k : ℕ) : scanBit bits k = bits.getD k false := by
  induction k generalizing bits with
  | zero => cases bits <;> rfl
  | succ k ih => cases bits <;> simp [scanBit, List.getD, ih]

/-- Scanning address `k` and returning to the origin takes exactly `2 * k + 1` events. -/
theorem scanTrace_length {R : ℕ} (bits : List Bool) (k : ℕ) :
    (scanTrace (R := R) bits k).length = 2 * k + 1 := by
  induction k generalizing bits with
  | zero => rfl
  | succ k ih => simp [scanTrace, ih]; omega

/-- Boolean expressions built from literals, input addresses, registers, negation, conjunction,
and exclusive disjunction. -/
inductive BitExpr (R : ℕ) where
  | literal (b : Bool) | input (address : ℕ) | reg (i : Fin R)
  | bnot (a : BitExpr R) | band (a b : BitExpr R) | bxor (a b : BitExpr R)
  deriving DecidableEq, Repr

namespace BitExpr

/-- Evaluate a Boolean expression against an input bit list and a register bank. -/
def eval {R : ℕ} (bits : List Bool) (regs : BitBank R) : BitExpr R → Bool
  | .literal b => b
  | .input k => scanBit bits k
  | .reg i => bankRead regs i
  | .bnot a => !(eval bits regs a)
  | .band a b => eval bits regs a && eval bits regs b
  | .bxor a b => xor (eval bits regs a) (eval bits regs b)

/-- Count the syntax-tree nodes of a Boolean expression. -/
def nodes {R : ℕ} : BitExpr R → ℕ
  | .literal _ | .input _ | .reg _ => 1
  | .bnot a => a.nodes + 1
  | .band a b | .bxor a b => a.nodes + b.nodes + 1

/-- The largest input address read by an expression, with value zero for literals and register
reads. -/
def maxRead {R : ℕ} : BitExpr R → ℕ
  | .literal _ | .reg _ => 0
  | .input k => k
  | .bnot a => a.maxRead
  | .band a b | .bxor a b => max a.maxRead b.maxRead

/-- Generate the elementary event trace for evaluating a Boolean expression. -/
def eventTrace {R : ℕ} (bits : List Bool) (regs : BitBank R) : BitExpr R → List (BitAction R)
  | .literal b => [.literal b]
  | .input k => scanTrace bits k
  | .reg i => [.readRegister i (bankRead regs i)]
  | .bnot a => eventTrace bits regs a ++ [.bnot (eval bits regs a)]
  | .band a b => eventTrace bits regs a ++ eventTrace bits regs b ++
      [.band (eval bits regs a) (eval bits regs b)]
  | .bxor a b => eventTrace bits regs a ++ eventTrace bits regs b ++
      [.bxor (eval bits regs a) (eval bits regs b)]

end BitExpr

/-- The execution relation connecting a Boolean expression, its elementary event trace, and its
value. -/
inductive ExprExec {R : ℕ} (bits : List Bool) (regs : BitBank R) :
    BitExpr R → List (BitAction R) → Bool → Prop where
  | literal (b) : ExprExec bits regs (.literal b) [.literal b] b
  | input {k trace b} : ScanExec R bits k trace b → ExprExec bits regs (.input k) trace b
  | reg (i) : ExprExec bits regs (.reg i) [.readRegister i (bankRead regs i)] (bankRead regs i)
  | bnot {a ta va} : ExprExec bits regs a ta va →
      ExprExec bits regs (.bnot a) (ta ++ [.bnot va]) (!va)
  | band {a b ta tb va vb} : ExprExec bits regs a ta va → ExprExec bits regs b tb vb →
      ExprExec bits regs (.band a b) (ta ++ tb ++ [.band va vb]) (va && vb)
  | bxor {a b ta tb va vb} : ExprExec bits regs a ta va → ExprExec bits regs b tb vb →
      ExprExec bits regs (.bxor a b) (ta ++ tb ++ [.bxor va vb]) (xor va vb)

/-- The generated expression trace executes with the value returned by `BitExpr.eval`. -/
theorem exprTrace_exec {R : ℕ} (bits : List Bool) (regs : BitBank R) (e : BitExpr R) :
    ExprExec bits regs e (e.eventTrace bits regs) (e.eval bits regs) := by
  induction e with
  | literal b => exact .literal b
  | input k => exact .input (scanTrace_exec bits k)
  | reg i => exact .reg i
  | bnot a ih => exact .bnot ih
  | band a b ha hb => exact .band ha hb
  | bxor a b ha hb => exact .bxor ha hb

/-- An expression trace has length at most `(2 * e.maxRead + 3) * e.nodes`. -/
theorem exprTrace_bound {R : ℕ} (bits : List Bool) (regs : BitBank R) (e : BitExpr R) :
    (e.eventTrace bits regs).length ≤ (2 * e.maxRead + 3) * e.nodes := by
  induction e with
  | literal b => simp [BitExpr.eventTrace, BitExpr.nodes, BitExpr.maxRead]
  | input k => simp [BitExpr.eventTrace, BitExpr.nodes, BitExpr.maxRead, scanTrace_length]
  | reg i => simp [BitExpr.eventTrace, BitExpr.nodes, BitExpr.maxRead]
  | bnot a ih =>
    simp only [BitExpr.eventTrace, BitExpr.nodes, BitExpr.maxRead, List.length_append,
      List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one]
    omega
  | band a b ha hb | bxor a b ha hb =>
    have hma := le_max_left a.maxRead b.maxRead
    have hmb := le_max_right a.maxRead b.maxRead
    have hca := ha.trans (Nat.mul_le_mul_right a.nodes
      (show 2 * a.maxRead + 3 ≤ 2 * max a.maxRead b.maxRead + 3 by omega))
    have hcb := hb.trans (Nat.mul_le_mul_right b.nodes
      (show 2 * b.maxRead + 3 ≤ 2 * max a.maxRead b.maxRead + 3 by omega))
    simp only [BitExpr.eventTrace, BitExpr.nodes, BitExpr.maxRead, List.length_append,
      List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one]
    omega

/-- An instruction frame consisting of input bits, a fixed-size register bank, and an output bit
list. -/
structure BitFrame (R : ℕ) where
  input : List Bool
  regs : BitBank R
  output : List Bool

/-- Bit instructions that either assign an expression to a register or emit its value. -/
inductive BitInstr (R : ℕ) where
  | assign (i : Fin R) (e : BitExpr R)
  | emit (e : BitExpr R)
  deriving DecidableEq, Repr

/-- The Boolean expression evaluated by an assignment or emission instruction. -/
def BitInstr.expr {R : ℕ} : BitInstr R → BitExpr R
  | .assign _ e | .emit e => e

/-- Execute one instruction by updating a register or prepending an evaluated bit to the output. -/
def bitStep {R : ℕ} (i : BitInstr R) (f : BitFrame R) : BitFrame R :=
  match i with
  | .assign k e => { f with regs := bankWrite f.regs k (e.eval f.input f.regs) }
  | .emit e => { f with output := e.eval f.input f.regs :: f.output }

/-- Generate the expression-evaluation and write events for a single bit instruction. -/
def bitStepTrace {R : ℕ} (i : BitInstr R) (f : BitFrame R) : List (BitAction R) :=
  match i with
  | .assign k e => e.eventTrace f.input f.regs ++ [.writeRegister k (e.eval f.input f.regs)]
  | .emit e => e.eventTrace f.input f.regs ++ [.outputLeft, .writeOutput (e.eval f.input f.regs)]

/-- The execution relation for a bit instruction, including expression evaluation and its
register or output update. -/
inductive StepExec {R : ℕ} : BitInstr R → BitFrame R → List (BitAction R) → BitFrame R → Prop where
  | assign {f k e trace b} : ExprExec f.input f.regs e trace b →
      StepExec (.assign k e) f (trace ++ [.writeRegister k b])
        { f with regs := bankWrite f.regs k b }
  | emit {f e trace b} : ExprExec f.input f.regs e trace b →
      StepExec (.emit e) f (trace ++ [.outputLeft, .writeOutput b]) { f with output := b :: f.output }

/-- The generated instruction trace executes to the frame computed by `bitStep`. -/
theorem bitStep_exec {R : ℕ} (i : BitInstr R) (f : BitFrame R) :
    StepExec i f (bitStepTrace i f) (bitStep i f) := by
  cases i with
  | assign k e => exact .assign (exprTrace_exec f.input f.regs e)
  | emit e => exact .emit (exprTrace_exec f.input f.regs e)

/-- Execute a list of bit instructions from left to right. -/
def bitRun {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) : BitFrame R :=
  code.foldl (fun f i => bitStep i f) f

/-- Generate the concatenated event trace for executing a block of bit instructions. -/
def bitRunTrace {R : ℕ} : List (BitInstr R) → BitFrame R → List (BitAction R)
  | [], _ => []
  | i :: code, f => bitStepTrace i f ++ bitRunTrace code (bitStep i f)

/-- The execution relation for a block of bit instructions and its concatenated event trace. -/
inductive BlockExec {R : ℕ} : List (BitInstr R) → BitFrame R → List (BitAction R) → BitFrame R → Prop where
  | nil (f) : BlockExec [] f [] f
  | cons {i code f g h t u} : StepExec i f t g → BlockExec code g u h →
      BlockExec (i :: code) f (t ++ u) h

/-- The generated block trace executes to the frame computed by `bitRun`. -/
theorem bitRun_exec {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) :
    BlockExec code f (bitRunTrace code f) (bitRun code f) := by
  induction code generalizing f with
  | nil => exact .nil f
  | cons i code ih => exact .cons (bitStep_exec i f) (ih _)

/-- An instruction trace is bounded by its expression evaluation bound plus two write events. -/
theorem bitStep_bound {R : ℕ} (i : BitInstr R) (f : BitFrame R) :
    (bitStepTrace i f).length ≤ (2 * i.expr.maxRead + 3) * i.expr.nodes + 2 := by
  have he := exprTrace_bound f.input f.regs i.expr
  cases i <;> simp only [bitStepTrace, BitInstr.expr, List.length_append, List.length_cons,
    List.length_nil] at * <;> omega

/-- A block with expression size at most `S` and read addresses at most `A` has trace length at
most `code.length * ((2 * A + 3) * S + 2)`. -/
theorem bitRun_bound {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) (S A : ℕ)
    (hn : ∀ i ∈ code, i.expr.nodes ≤ S) (ha : ∀ i ∈ code, i.expr.maxRead ≤ A) :
    (bitRunTrace code f).length ≤ code.length * ((2 * A + 3) * S + 2) := by
  induction code generalizing f with
  | nil => simp [bitRunTrace]
  | cons i code ih =>
    have hn0 := hn i (by simp)
    have ha0 := ha i (by simp)
    have hi := bitStep_bound i f
    have hh1 := Nat.mul_le_mul_right i.expr.nodes
      (show 2 * i.expr.maxRead + 3 ≤ 2 * A + 3 by omega)
    have hh2 := Nat.mul_le_mul_left (2 * A + 3) hn0
    have hstep : (bitStepTrace i f).length ≤ (2 * A + 3) * S + 2 := by omega
    have htail := ih (bitStep i f) (fun j hj => hn j (by simp [hj]))
      (fun j hj => ha j (by simp [hj]))
    simp only [bitRunTrace, List.length_append, List.length_cons]
    rw [Nat.succ_mul code.length ((2 * A + 3) * S + 2)]
    omega

/-- Test whether a bit instruction emits an output bit. -/
def BitInstr.isEmit {R : ℕ} : BitInstr R → Bool
  | .emit _ => true
  | .assign _ _ => false

/-- Executing a block of bit instructions preserves its input list. -/
theorem bitRun_input {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) :
    (bitRun code f).input = f.input := by
  induction code generalizing f with
  | nil => rfl
  | cons i code ih =>
    change (bitRun code (bitStep i f)).input = _
    rw [ih]
    cases i <;> rfl

/-- A block increases output length by exactly its number of emission instructions. -/
theorem bitRun_output_length {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) :
    (bitRun code f).output.length = f.output.length + (code.filter BitInstr.isEmit).length := by
  induction code generalizing f with
  | nil => simp [bitRun]
  | cons i code ih =>
    change (bitRun code (bitStep i f)).output.length = _
    rw [ih]
    cases i <;> simp [bitStep, BitInstr.isEmit, Nat.add_assoc, Nat.add_comm]

/-- Code for adding two two-bit phases modulo four, placing the result in registers zero and
one. -/
def phaseAddCode : List (BitInstr 8) :=
  [.assign 4 (.bxor (.reg 0) (.reg 2)),
    .assign 5 (.bxor (.bxor (.reg 1) (.reg 3)) (.band (.reg 0) (.reg 2))),
    .assign 0 (.reg 4), .assign 1 (.reg 5)]

set_option maxHeartbeats 2000000 in

/-- Given the two-bit encodings of phases in registers zero through three, `phaseAddCode` stores
the bits of their sum in registers zero and one. -/
theorem phaseAdd_correct (f : BitFrame 8) (p q : ZMod 4)
    (h0 : bankRead f.regs 0 = p.val.testBit 0) (h1 : bankRead f.regs 1 = p.val.testBit 1)
    (h2 : bankRead f.regs 2 = q.val.testBit 0) (h3 : bankRead f.regs 3 = q.val.testBit 1) :
    bankRead (bitRun phaseAddCode f).regs 0 = (p + q).val.testBit 0 ∧
      bankRead (bitRun phaseAddCode f).regs 1 = (p + q).val.testBit 1 := by
  fin_cases p <;> fin_cases q <;>
    simp only [phaseAddCode, bitRun, List.foldl_cons, List.foldl_nil, bitStep,
      BitExpr.eval, bankRead_write, Fin.reduceEq, if_true, if_false, h0, h1, h2, h3] <;> decide

/-- The phase addition code generates exactly sixteen elementary events. -/
theorem phaseAdd_trace_length (f : BitFrame 8) :
    (bitRunTrace phaseAddCode f).length = 16 := by
  simp [phaseAddCode, bitRunTrace, bitStepTrace, BitExpr.eventTrace]

/-- Input addresses for the X bits, Z bits, and two phase bits of a tableau row. -/
structure RowLayout (n : ℕ) where
  x : Fin n → ℕ
  z : Fin n → ℕ
  low : ℕ
  high : ℕ

/-- The standard contiguous row layout starting at a specified bit offset. -/
def rowLayout (n offset : ℕ) : RowLayout n where
  x i := offset + i.val
  z i := offset + n + i.val
  low := offset + 2 * n
  high := offset + 2 * n + 1

/-- The input bits at a row layout agree with the row's X coordinates, Z coordinates, and two
phase bits. -/
def RepresentsRow {n : ℕ} (bits : List Bool) (a : RowLayout n) (r : Row n) : Prop :=
  (∀ i, scanBit bits (a.x i) = r.x i) ∧
  (∀ i, scanBit bits (a.z i) = r.z i) ∧
  scanBit bits a.low = r.phase.val.testBit 0 ∧
  scanBit bits a.high = r.phase.val.testBit 1

/-- Adding two conditionally to a phase preserves its low bit and toggles its high bit by the
condition. -/
theorem phase_toggle_bits (p : ZMod 4) (b : Bool) :
    (p + if b then 2 else 0).val.testBit 0 = p.val.testBit 0 ∧
    (p + if b then 2 else 0).val.testBit 1 = xor (p.val.testBit 1) b := by
  fin_cases p <;> cases b <;> decide

/-- The expression computing an updated X coordinate under a Clifford gate. -/
def gateXExpr {n : ℕ} (a : RowLayout n) : CliffordGate n → Fin n → BitExpr 8
  | .H i, k => if k = i then .input (a.z i) else .input (a.x k)
  | .S _, k => .input (a.x k)
  | .CNOT i j, k => if k = j then .bxor (.input (a.x j)) (.input (a.x i))
      else .input (a.x k)

/-- The expression computing an updated Z coordinate under a Clifford gate. -/
def gateZExpr {n : ℕ} (a : RowLayout n) : CliffordGate n → Fin n → BitExpr 8
  | .H i, k => if k = i then .input (a.x i) else .input (a.z k)
  | .S i, k => if k = i then .bxor (.input (a.z i)) (.input (a.x i))
      else .input (a.z k)
  | .CNOT i j, k => if k = i then .bxor (.input (a.z i)) (.input (a.z j))
      else .input (a.z k)

/-- The expression computing the phase-toggle condition for a Clifford row update. -/
def gateFlipExpr {n : ℕ} (a : RowLayout n) : CliffordGate n → BitExpr 8
  | .H i | .S i => .band (.input (a.x i)) (.input (a.z i))
  | .CNOT i j => .band (.band (.input (a.x i)) (.input (a.z j)))
      (.bnot (.bxor (.input (a.x j)) (.input (a.z i))))

/-- The expressions for all encoded bits of a row after a Clifford gate update. -/
def gateRowExprs {n : ℕ} (a : RowLayout n) (g : CliffordGate n) : List (BitExpr 8) :=
  List.ofFn (gateXExpr a g) ++ List.ofFn (gateZExpr a g) ++
    [.input a.low, .bxor (.input a.high) (gateFlipExpr a g)]

/-- Compile a list of expressions into emissions in reverse order so that their values appear in
the original order in the output. -/
def emitCode {R : ℕ} (es : List (BitExpr R)) : List (BitInstr R) :=
  es.reverse.map .emit

/-- Executing concatenated instruction blocks agrees with executing the first block and then the
second. -/
theorem bitRun_append {R : ℕ} (xs ys : List (BitInstr R)) (f : BitFrame R) :
    bitRun (xs ++ ys) f = bitRun ys (bitRun xs f) := by
  simp [bitRun, List.foldl_append]

/-- Emission code prepends the expression values in their original order and preserves the input
and registers. -/
theorem emitCode_correct {R : ℕ} (es : List (BitExpr R)) (f : BitFrame R) :
    (bitRun (emitCode es) f).input = f.input ∧
    (bitRun (emitCode es) f).regs = f.regs ∧
    (bitRun (emitCode es) f).output = es.map (BitExpr.eval f.input f.regs) ++ f.output := by
  induction es generalizing f with
  | nil => simp [emitCode, bitRun]
  | cons e es ih =>
    have h := ih f
    have hcode : emitCode (e :: es) = emitCode es ++ [.emit e] := by simp [emitCode]
    rw [hcode, bitRun_append]
    change (bitRun (emitCode es) f).input = f.input ∧
      (bitRun (emitCode es) f).regs = f.regs ∧
      e.eval (bitRun (emitCode es) f).input (bitRun (emitCode es) f).regs ::
        (bitRun (emitCode es) f).output = _
    exact ⟨h.1, h.2.1, by rw [h.1, h.2.1, h.2.2]; rfl⟩

/-- The Boolean condition determining whether a Clifford gate adds two to a row phase. -/
def gateControl {n : ℕ} (r : Row n) : CliffordGate n → Bool
  | .H i | .S i => r.x i && r.z i
  | .CNOT i j => r.x i && r.z j && !(xor (r.x j) (r.z i))

/-- On a represented row, `gateXExpr` evaluates to the updated X coordinate. -/
theorem gateXExpr_correct {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (f : BitFrame 8) (r : Row n) (hr : RepresentsRow f.input a r) (k : Fin n) :
    (gateXExpr a g k).eval f.input f.regs = (r.update g).x k := by
  cases g with
  | H i => by_cases h : k = i <;> simp [gateXExpr, BitExpr.eval, Row.update, h, hr.1, hr.2.1]
  | S i => exact hr.1 k
  | CNOT i j => by_cases h : k = j <;> simp [gateXExpr, BitExpr.eval, Row.update, h, hr.1]

/-- On a represented row, `gateZExpr` evaluates to the updated Z coordinate. -/
theorem gateZExpr_correct {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (f : BitFrame 8) (r : Row n) (hr : RepresentsRow f.input a r) (k : Fin n) :
    (gateZExpr a g k).eval f.input f.regs = (r.update g).z k := by
  cases g with
  | H i => by_cases h : k = i <;> simp [gateZExpr, BitExpr.eval, Row.update, h, hr.1, hr.2.1]
  | S i => by_cases h : k = i <;> simp [gateZExpr, BitExpr.eval, Row.update, h, hr.1, hr.2.1]
  | CNOT i j => by_cases h : k = i <;> simp [gateZExpr, BitExpr.eval, Row.update, h, hr.2.1]

/-- On a represented row, the phase-toggle expression evaluates to `gateControl`. -/
theorem gateFlipExpr_correct {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (f : BitFrame 8) (r : Row n) (hr : RepresentsRow f.input a r) :
    (gateFlipExpr a g).eval f.input f.regs = gateControl r g := by
  cases g <;> simp only [gateFlipExpr, BitExpr.eval, hr.1, hr.2.1, gateControl]

/-- A Clifford row update adds two to the phase exactly when `gateControl` is true. -/
theorem gate_phase_eq {n : ℕ} (r : Row n) (g : CliffordGate n) :
    (r.update g).phase = r.phase + if gateControl r g then 2 else 0 := by
  cases g <;> rfl

/-- Evaluating the gate row expressions yields the bit encoding of the updated row. -/
theorem gateRowExprs_correct {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (f : BitFrame 8) (r : Row n) (hr : RepresentsRow f.input a r) :
    (gateRowExprs a g).map (BitExpr.eval f.input f.regs) = (r.update g).bits := by
  have hp := phase_toggle_bits r.phase (gateControl r g)
  simp only [gateRowExprs, List.map_append, List.map_ofFn, Function.comp_def,
    gateXExpr_correct a g f r hr, gateZExpr_correct a g f r hr, List.map_cons, List.map_nil,
    BitExpr.eval, hr.2.2.1, hr.2.2.2, gateFlipExpr_correct a g f r hr,
    Row.bits, gate_phase_eq, hp.1, hp.2]

/-- The compiled gate row emissions prepend the updated row encoding to the output. -/
theorem gateRowCode_correct {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (f : BitFrame 8) (r : Row n) (hr : RepresentsRow f.input a r) :
    (bitRun (emitCode (gateRowExprs a g)) f).output = (r.update g).bits ++ f.output := by
  rw [(emitCode_correct _ _).2.2, gateRowExprs_correct a g f r hr]

/-- Every address in a row layout is at most the specified bound. -/
def RowLayout.Bounded {n : ℕ} (a : RowLayout n) (A : ℕ) : Prop :=
  (∀ i, a.x i ≤ A) ∧ (∀ i, a.z i ≤ A) ∧ a.low ≤ A ∧ a.high ≤ A

/-- An updated X expression has at most three nodes and respects the layout's address bound. -/
theorem gateXExpr_bounds {n : ℕ} (a : RowLayout n) (g : CliffordGate n) (k : Fin n)
    (A : ℕ) (ha : a.Bounded A) :
    (gateXExpr a g k).nodes ≤ 3 ∧ (gateXExpr a g k).maxRead ≤ A := by
  cases g with
  | H i => by_cases h : k = i <;> simp [gateXExpr, h, BitExpr.nodes, BitExpr.maxRead, ha.1, ha.2.1]
  | S i => exact ⟨by simp [gateXExpr, BitExpr.nodes], ha.1 k⟩
  | CNOT i j => by_cases h : k = j <;>
      simp [gateXExpr, h, BitExpr.nodes, BitExpr.maxRead, ha.1]

/-- An updated Z expression has at most three nodes and respects the layout's address bound. -/
theorem gateZExpr_bounds {n : ℕ} (a : RowLayout n) (g : CliffordGate n) (k : Fin n)
    (A : ℕ) (ha : a.Bounded A) :
    (gateZExpr a g k).nodes ≤ 3 ∧ (gateZExpr a g k).maxRead ≤ A := by
  cases g with
  | H i => by_cases h : k = i <;> simp [gateZExpr, h, BitExpr.nodes, BitExpr.maxRead, ha.1, ha.2.1]
  | S i => by_cases h : k = i <;>
      simp [gateZExpr, h, BitExpr.nodes, BitExpr.maxRead, ha.1, ha.2.1]
  | CNOT i j => by_cases h : k = i <;>
      simp [gateZExpr, h, BitExpr.nodes, BitExpr.maxRead, ha.2.1]

/-- The phase-toggle expression has at most eight nodes and respects the layout's address bound. -/
theorem gateFlipExpr_bounds {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (A : ℕ) (ha : a.Bounded A) :
    (gateFlipExpr a g).nodes ≤ 8 ∧ (gateFlipExpr a g).maxRead ≤ A := by
  cases g <;> simp [gateFlipExpr, BitExpr.nodes, BitExpr.maxRead, ha.1, ha.2.1]

/-- The list of gate row expressions has length `rowWidth n`. -/
theorem gateRowExprs_length {n : ℕ} (a : RowLayout n) (g : CliffordGate n) :
    (gateRowExprs a g).length = rowWidth n := by simp [gateRowExprs, rowWidth]; omega

/-- Every gate row expression has at most ten nodes and respects the layout's address bound. -/
theorem gateRowExprs_bounds {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (A : ℕ) (ha : a.Bounded A) :
    ∀ e ∈ gateRowExprs a g, e.nodes ≤ 10 ∧ e.maxRead ≤ A := by
  intro e he
  simp only [gateRowExprs, List.mem_append, List.mem_ofFn, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with h | h
  · rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h := gateXExpr_bounds a g k A ha
      exact ⟨by omega, h.2⟩
    · have h := gateZExpr_bounds a g k A ha
      exact ⟨by omega, h.2⟩
  · rcases h with rfl | rfl
    · exact ⟨by simp [BitExpr.nodes], ha.2.2.1⟩
    · have h := gateFlipExpr_bounds a g A ha
      simp only [BitExpr.nodes, BitExpr.maxRead]
      exact ⟨by omega, max_le ha.2.2.2 h.2⟩

/-- Gate row emission has trace length at most `rowWidth n * ((2 * A + 3) * 10 + 2)` for a
layout bounded by `A`. -/
theorem gateRowCode_time {n : ℕ} (a : RowLayout n) (g : CliffordGate n)
    (f : BitFrame 8) (A : ℕ) (ha : a.Bounded A) :
    (bitRunTrace (emitCode (gateRowExprs a g)) f).length ≤
      rowWidth n * ((2 * A + 3) * 10 + 2) := by
  have he := gateRowExprs_bounds a g A ha
  have hmem : ∀ i ∈ emitCode (gateRowExprs a g), i.expr.nodes ≤ 10 ∧ i.expr.maxRead ≤ A := by
    intro i hi
    simp only [emitCode, List.mem_map, List.mem_reverse] at hi
    obtain ⟨e, he', rfl⟩ := hi
    exact he e he'
  have h := bitRun_bound (emitCode (gateRowExprs a g)) f 10 A
    (fun i hi => (hmem i hi).1) (fun i hi => (hmem i hi).2)
  simpa only [emitCode, List.length_map, List.length_reverse, gateRowExprs_length] using! h

/-- Scanning an address within the left list of a concatenation gives the same bit as scanning
that list alone. -/
theorem scanBit_append_left (xs ys : List Bool) (k : ℕ) (hk : k < xs.length) :
    scanBit (xs ++ ys) k = scanBit xs k := by
  simp only [scanBit_getD]
  exact List.getD_append xs ys false k hk

/-- Scanning beyond the left list by an offset agrees with scanning the right list at that
offset. -/
theorem scanBit_append_right (xs ys : List Bool) (k : ℕ) :
    scanBit (xs ++ ys) (xs.length + k) = scanBit ys k := by
  simp only [scanBit_getD]
  rw [List.getD_append_right xs ys false (xs.length + k) (by omega), Nat.add_sub_cancel_left]

/-- Scanning the list generated by a finite Boolean function returns the function's value. -/
theorem scanBit_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    scanBit (List.ofFn f) i.val = f i := by
  rw [scanBit_getD, List.getD_eq_getElem _ _ (by simp)]
  simp

/-- A row's own encoding represents it at offset zero. -/
theorem representsRow_self {n : ℕ} (r : Row n) : RepresentsRow r.bits (rowLayout n 0) r := by
  unfold RepresentsRow rowLayout
  dsimp
  simp only [Nat.zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [Row.bits, List.append_assoc, scanBit_append_left _ _ _ (by simp)]
    exact scanBit_ofFn r.x i
  · intro i
    rw [Row.bits, List.append_assoc]
    rw [show n + i.val = (List.ofFn r.x).length + i.val by simp]
    rw [scanBit_append_right, scanBit_append_left _ _ _ (by simp)]
    exact scanBit_ofFn r.z i
  · rw [Row.bits, List.append_assoc]
    have h : 2 * n = (List.ofFn r.x).length + (List.ofFn r.z).length := by simp; omega
    rw [h, scanBit_append_right]
    simpa using!
        scanBit_append_right (List.ofFn r.z) [r.phase.val.testBit 0, r.phase.val.testBit 1] 0
  · rw [Row.bits, List.append_assoc]
    have h : 2 * n + 1 = (List.ofFn r.x).length + ((List.ofFn r.z).length + 1) := by simp; omega
    rw [h, scanBit_append_right, scanBit_append_right]
    rfl

/-- A Boolean expression for the low bit of the single-site Pauli multiplication phase. -/
def cocycleLow {R : ℕ} (x z y w : BitExpr R) : BitExpr R :=
  .bxor (.band x w) (.band z y)

/-- A Boolean expression for the high bit of the single-site Pauli multiplication phase. -/
def cocycleHigh {R : ℕ} (x z y w : BitExpr R) : BitExpr R :=
  .bxor (.bxor
    (.band (.band x (.bnot z)) (.band (.bnot y) w))
    (.band (.band x z) (.band y (.bnot w))))
    (.band (.band (.bnot x) z) (.band y w))

/-- The two bits of a single-site Pauli multiplication phase are given by the stated Boolean
formulas. -/
theorem cocycle_bits (x z y w : Bool) :
    (pauliMulPhase (letter x z) (letter y w)).val.testBit 0 = xor (x && w) (z && y) ∧
    (pauliMulPhase (letter x z) (letter y w)).val.testBit 1 =
      xor (xor ((x && !z) && (!y && w)) ((x && z) && (y && !w))) ((!x && z) && (y && w)) := by
  cases x <;> cases z <;> cases y <;> cases w <;> decide

/-- The low-bit Pauli cocycle expression at a site of two represented rows. -/
def cocycleLowExpr {n : ℕ} (a c : RowLayout n) (k : Fin n) : BitExpr 8 :=
  cocycleLow (.input (a.x k)) (.input (a.z k)) (.input (c.x k)) (.input (c.z k))

/-- The high-bit Pauli cocycle expression at a site of two represented rows. -/
def cocycleHighExpr {n : ℕ} (a c : RowLayout n) (k : Fin n) : BitExpr 8 :=
  cocycleHigh (.input (a.x k)) (.input (a.z k)) (.input (c.x k)) (.input (c.z k))

/-- The phase modulo four contributed by multiplying the two single-site Pauli letters. -/
def rowCocycle {n : ℕ} (r s : Row n) (k : Fin n) : ZMod 4 :=
  pauliMulPhase (letter (r.x k) (r.z k)) (letter (s.x k) (s.z k))

/-- For represented rows, the cocycle expressions evaluate to the two bits of `rowCocycle`. -/
theorem cocycleExpr_correct {n : ℕ} (a c : RowLayout n) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s) (k : Fin n) :
    (cocycleLowExpr a c k).eval f.input f.regs = (rowCocycle r s k).val.testBit 0 ∧
    (cocycleHighExpr a c k).eval f.input f.regs = (rowCocycle r s k).val.testBit 1 := by
  simp only [cocycleLowExpr, cocycleHighExpr, cocycleLow, cocycleHigh, BitExpr.eval,
    hr.1, hr.2.1, hs.1, hs.2.1, rowCocycle]
  exact ⟨(cocycle_bits _ _ _ _).1.symm, (cocycle_bits _ _ _ _).2.symm⟩

/-- Load and add the two input row phases into accumulator registers zero and one. -/
def phaseInitCode {n : ℕ} (a c : RowLayout n) : List (BitInstr 8) :=
  [.assign 0 (.input a.low), .assign 1 (.input a.high),
    .assign 2 (.input c.low), .assign 3 (.input c.high)] ++ phaseAddCode

/-- Add one site's Pauli multiplication phase to the two-bit phase accumulator. -/
def phaseSiteCode {n : ℕ} (a c : RowLayout n) (k : Fin n) : List (BitInstr 8) :=
  [.assign 2 (cocycleLowExpr a c k), .assign 3 (cocycleHighExpr a c k)] ++ phaseAddCode

/-- Concatenate the phase-accumulation code for a list of sites. -/
def phaseSitesCode {n : ℕ} (a c : RowLayout n) (ks : List (Fin n)) : List (BitInstr 8) :=
  ks.flatMap (phaseSiteCode a c)

/-- Executing code with no emission instructions preserves the output list. -/
theorem bitRun_noEmit_output {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R)
    (h : ∀ i ∈ code, i.isEmit = false) : (bitRun code f).output = f.output := by
  induction code generalizing f with
  | nil => rfl
  | cons i code ih =>
    have h0 := h i (by simp)
    have htail := ih (bitStep i f) (fun j hj => h j (by simp [hj]))
    change (bitRun code (bitStep i f)).output = _
    rw [htail]
    cases i with
    | assign k e => rfl
    | emit e => simp [BitInstr.isEmit] at h0

/-- Phase initialization preserves both the input and output lists. -/
theorem phaseInit_input_output {n : ℕ} (a c : RowLayout n) (f : BitFrame 8) :
    (bitRun (phaseInitCode a c) f).input = f.input ∧
    (bitRun (phaseInitCode a c) f).output = f.output := by
  refine ⟨bitRun_input _ _, bitRun_noEmit_output _ _ ?_⟩
  intro i hi
  simp only [phaseInitCode, phaseAddCode, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rfl

/-- Accumulating a single site's phase preserves the input and output lists. -/
theorem phaseSite_input_output {n : ℕ} (a c : RowLayout n) (k : Fin n) (f : BitFrame 8) :
    (bitRun (phaseSiteCode a c k) f).input = f.input ∧
    (bitRun (phaseSiteCode a c k) f).output = f.output := by
  refine ⟨bitRun_input _ _, bitRun_noEmit_output _ _ ?_⟩
  intro i hi
  simp only [phaseSiteCode, phaseAddCode, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rfl

/-- Accumulating phases over a list of sites preserves the input and output lists. -/
theorem phaseSites_input_output {n : ℕ} (a c : RowLayout n) (ks : List (Fin n)) (f : BitFrame 8) :
    (bitRun (phaseSitesCode a c ks) f).input = f.input ∧
    (bitRun (phaseSitesCode a c ks) f).output = f.output := by
  induction ks generalizing f with
  | nil => exact ⟨rfl, rfl⟩
  | cons k ks ih =>
    simp only [phaseSitesCode, List.flatMap_cons, bitRun_append] at *
    have h := ih (bitRun (phaseSiteCode a c k) f)
    exact ⟨h.1.trans (phaseSite_input_output a c k f).1,
      h.2.trans (phaseSite_input_output a c k f).2⟩

set_option maxHeartbeats 2000000 in

/-- For represented rows, phase initialization stores the bits of the sum of their phases. -/
theorem phaseInit_correct {n : ℕ} (a c : RowLayout n) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s) :
    bankRead (bitRun (phaseInitCode a c) f).regs 0 = (r.phase + s.phase).val.testBit 0 ∧
    bankRead (bitRun (phaseInitCode a c) f).regs 1 = (r.phase + s.phase).val.testBit 1 := by
  rw [phaseInitCode, bitRun_append]
  apply phaseAdd_correct _ r.phase s.phase
  all_goals simp [bitRun, bitStep, BitExpr.eval, hr.2.2.1, hr.2.2.2, hs.2.2.1, hs.2.2.2]

set_option maxHeartbeats 2000000 in

/-- For represented rows and an accumulator encoding `p`, one phase site step stores the bits of
`p + rowCocycle r s k`. -/
theorem phaseSite_correct {n : ℕ} (a c : RowLayout n) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s)
    (p : ZMod 4) (h0 : bankRead f.regs 0 = p.val.testBit 0)
    (h1 : bankRead f.regs 1 = p.val.testBit 1) (k : Fin n) :
    bankRead (bitRun (phaseSiteCode a c k) f).regs 0 = (p + rowCocycle r s k).val.testBit 0 ∧
    bankRead (bitRun (phaseSiteCode a c k) f).regs 1 = (p + rowCocycle r s k).val.testBit 1 := by
  rw [phaseSiteCode, bitRun_append]
  apply phaseAdd_correct _ p (rowCocycle r s k)
  · simpa [bitRun, bitStep] using! h0
  · simpa [bitRun, bitStep] using! h1
  · simp only [bitRun, List.foldl_cons, List.foldl_nil, bitStep, bankRead_write,
      Fin.reduceEq, if_true, if_false]
    exact (cocycleExpr_correct a c f r s hr hs k).1
  · simp only [bitRun, List.foldl_cons, List.foldl_nil, bitStep, bankRead_write,
      Fin.reduceEq, if_true, if_false]
    exact (cocycleExpr_correct a c _ r s hr hs k).2

/-- Phase accumulation over `ks` adds the sum of their cocycle contributions to the encoded
accumulator phase. -/
theorem phaseSites_correct {n : ℕ} (a c : RowLayout n) (ks : List (Fin n)) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s)
    (p : ZMod 4) (h0 : bankRead f.regs 0 = p.val.testBit 0)
    (h1 : bankRead f.regs 1 = p.val.testBit 1) :
    bankRead (bitRun (phaseSitesCode a c ks) f).regs 0 =
      (p + (ks.map (rowCocycle r s)).sum).val.testBit 0 ∧
    bankRead (bitRun (phaseSitesCode a c ks) f).regs 1 =
      (p + (ks.map (rowCocycle r s)).sum).val.testBit 1 := by
  induction ks generalizing f p with
  | nil => simpa [phaseSitesCode, bitRun] using! And.intro h0 h1
  | cons k ks ih =>
    have hh := phaseSite_correct a c f r s hr hs p h0 h1 k
    have hr' : RepresentsRow (bitRun (phaseSiteCode a c k) f).input a r := by
      rw [bitRun_input]; exact hr
    have hs' : RepresentsRow (bitRun (phaseSiteCode a c k) f).input c s := by
      rw [bitRun_input]; exact hs
    have ht := ih (bitRun (phaseSiteCode a c k) f) hr' hs' (p + rowCocycle r s k) hh.1 hh.2
    simpa only [phaseSitesCode, List.flatMap_cons, bitRun_append, List.map_cons,
      List.sum_cons, add_assoc] using! ht

/-- Code for computing the product-row phase from the two row phases and all single-site
cocycles. -/
def mulPhaseCode {n : ℕ} (a c : RowLayout n) : List (BitInstr 8) :=
  phaseInitCode a c ++ phaseSitesCode a c (List.ofFn id)

/-- For represented rows, `mulPhaseCode` stores the two bits of the product row's phase. -/
theorem mulPhaseCode_correct {n : ℕ} (a c : RowLayout n) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s) :
    bankRead (bitRun (mulPhaseCode a c) f).regs 0 = (r.mul s).phase.val.testBit 0 ∧
    bankRead (bitRun (mulPhaseCode a c) f).regs 1 = (r.mul s).phase.val.testBit 1 := by
  have hi := phaseInit_correct a c f r s hr hs
  have hr' : RepresentsRow (bitRun (phaseInitCode a c) f).input a r := by
    rw [bitRun_input]; exact hr
  have hs' : RepresentsRow (bitRun (phaseInitCode a c) f).input c s := by
    rw [bitRun_input]; exact hs
  have h := phaseSites_correct a c (List.ofFn id) (bitRun (phaseInitCode a c) f)
    r s hr' hs' (r.phase + s.phase) hi.1 hi.2
  simpa only [mulPhaseCode, bitRun_append, List.map_ofFn, Function.comp_id,
    List.sum_ofFn, Row.mul, rowCocycle] using! h

/-- Expressions for the X and Z coordinates of a product row, followed by the accumulated phase
bits. -/
def mulRowExprs {n : ℕ} (a c : RowLayout n) : List (BitExpr 8) :=
  List.ofFn (fun k => .bxor (.input (a.x k)) (.input (c.x k))) ++
  List.ofFn (fun k => .bxor (.input (a.z k)) (.input (c.z k))) ++ [.reg 0, .reg 1]

/-- Compute a product row's phase and emit its full bit encoding. -/
def mulRowCode {n : ℕ} (a c : RowLayout n) : List (BitInstr 8) :=
  mulPhaseCode a c ++ emitCode (mulRowExprs a c)

/-- Product-phase computation preserves the input and output lists. -/
theorem mulPhase_input_output {n : ℕ} (a c : RowLayout n) (f : BitFrame 8) :
    (bitRun (mulPhaseCode a c) f).input = f.input ∧
    (bitRun (mulPhaseCode a c) f).output = f.output := by
  rw [mulPhaseCode, bitRun_append]
  have h := phaseSites_input_output a c (List.ofFn id) (bitRun (phaseInitCode a c) f)
  exact ⟨h.1.trans (phaseInit_input_output a c f).1,
    h.2.trans (phaseInit_input_output a c f).2⟩

/-- For represented rows, row multiplication code prepends the bit encoding of their product to
the output. -/
theorem mulRowCode_correct {n : ℕ} (a c : RowLayout n) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s) :
    (bitRun (mulRowCode a c) f).output = (r.mul s).bits ++ f.output := by
  have hp := mulPhaseCode_correct a c f r s hr hs
  have hio := mulPhase_input_output a c f
  rw [mulRowCode, bitRun_append, (emitCode_correct _ _).2.2, hio.2]
  congr 1
  simp only [mulRowExprs, List.map_append, List.map_ofFn, Function.comp_def, List.map_cons,
    List.map_nil, BitExpr.eval, hio.1, hr.1, hr.2.1, hs.1, hs.2.1, hp.1, hp.2, Row.bits, Row.mul]

/-- Scanning a valid address in flattened row encodings returns the corresponding bit of the
selected row. -/
theorem scanBit_flatRows {n : ℕ} (rs : List (Row n)) (suffix : List Bool)
    (j k : ℕ) (hj : j < rs.length) (hk : k < rowWidth n) :
    scanBit (rs.flatMap Row.bits ++ suffix) (j * rowWidth n + k) = scanBit rs[j].bits k := by
  induction rs generalizing j with
  | nil => simp at hj
  | cons r rs ih =>
    cases j with
    | zero =>
      simp only [List.flatMap_cons, List.append_assoc, Nat.zero_mul, Nat.zero_add,
        List.getElem_cons_zero]
      exact scanBit_append_left _ _ _ (by simpa only [row_bits_length, rowWidth] using! hk)
    | succ j =>
      have hj' : j < rs.length := by simpa using! hj
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_succ]
      rw [show (j + 1) * rowWidth n + k = r.bits.length + (j * rowWidth n + k) by
        rw [← rowWidth_eq_bits_length r, Nat.add_mul, Nat.one_mul]; omega, scanBit_append_right]
      exact ih j hj'

/-- Each row of a tableau is represented at its standard offset in the tableau encoding, even
with an appended suffix. -/
theorem representsRow_tableau {n m : ℕ} (t : Tableau n m) (suffix : List Bool) (j : Fin m) :
    RepresentsRow (tableauBits t ++ suffix) (rowLayout n (j.val * rowWidth n)) (t j) := by
  have hscan (k : ℕ) (hk : k < rowWidth n) :
      scanBit (tableauBits t ++ suffix) (j.val * rowWidth n + k) = scanBit (t j).bits k := by
    have h := scanBit_flatRows (List.ofFn t) suffix j.val k (by simp) hk
    simpa only [tableauBits, List.getElem_ofFn] using! h
  have hself := representsRow_self (t j)
  simp only [RepresentsRow, rowLayout, Nat.zero_add] at hself ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hscan i.val (by unfold rowWidth; omega)]
    exact hself.1 i
  · intro i
    rw [Nat.add_assoc, hscan (n + i.val) (by unfold rowWidth; omega)]
    exact hself.2.1 i
  · rw [hscan (2 * n) (by unfold rowWidth; omega)]
    exact hself.2.2.1
  · rw [Nat.add_assoc, hscan (2 * n + 1) (by unfold rowWidth; omega)]
    exact hself.2.2.2

/-- The concatenated expressions for a Clifford gate update of every tableau row. -/
def gateTableauExprs {n m : ℕ} (g : CliffordGate n) : List (BitExpr 8) :=
  (List.ofFn (fun j : Fin m => gateRowExprs (rowLayout n (j.val * rowWidth n)) g)).flatten

/-- Code emitting the tableau bits after a Clifford gate update. -/
def gateTableauCode {n m : ℕ} (g : CliffordGate n) : List (BitInstr 8) :=
  emitCode (gateTableauExprs (m := m) g)

/-- Given a tableau encoding as input, gate tableau code prepends the encoding of the updated
tableau to the output. -/
theorem gateTableauCode_correct {n m : ℕ} (g : CliffordGate n) (t : Tableau n m)
    (f : BitFrame 8) (hf : f.input = tableauBits t) :
    (bitRun (gateTableauCode (m := m) g) f).output = tableauBits (update g t) ++ f.output := by
  rw [gateTableauCode, (emitCode_correct _ _).2.2]
  congr 1
  simp only [gateTableauExprs, List.map_flatten, List.map_ofFn,
    Function.comp_def, tableauBits, List.flatMap_def]
  congr 1
  congr 1
  funext j
  apply gateRowExprs_correct _ g f (t j)
  rw [hf]
  simpa only [List.append_nil] using! representsRow_tableau t [] j

/-- The Boolean symplectic pairing contribution of two rows at one qubit. -/
def rowParityAt {n : ℕ} (r s : Row n) (k : Fin n) : Bool :=
  xor (r.x k && s.z k) (r.z k && s.x k)

/-- The exclusive-disjunction sum of the single-site symplectic pairing contributions. -/
def rowParity {n : ℕ} (r s : Row n) : Bool :=
  (List.ofFn (rowParityAt r s)).foldl xor false

/-- The Boolean-to-`ZMod 2` equivalence maps exclusive disjunction to addition. -/
theorem boolZMod_xor (x y : Bool) :
    boolZModEquiv (xor x y) = boolZModEquiv x + boolZModEquiv y := by
  cases x <;> cases y <;> decide

/-- Mapping an exclusive-disjunction fold to `ZMod 2` gives the initial value plus the sum of
the mapped bits. -/
theorem xorFold_sum (bs : List Bool) (b : Bool) :
    boolZModEquiv (bs.foldl xor b) = boolZModEquiv b + (bs.map boolZModEquiv).sum := by
  induction bs generalizing b with
  | nil => simp
  | cons c bs ih => simp only [List.foldl_cons, ih, boolZMod_xor, List.map_cons,
      List.sum_cons, add_assoc]

/-- The Boolean row parity represents the symplectic pairing of the decoded Pauli words. -/
theorem rowParity_symplectic {n : ℕ} (r s : Row n) :
    boolZModEquiv (rowParity r s) =
      symplecticForm (symplecticVec r.decode.word) (symplecticVec s.decode.word) := by
  have hsite (k : Fin n) : boolZModEquiv (rowParityAt r s k) =
      siteForm (r.decode.word k) (s.decode.word k) := by
    cases hx : r.x k <;> cases hz : r.z k <;> cases hy : s.x k <;> cases hw : s.z k <;>
      simp only [rowParityAt, Row.decode, hx, hz, hy, hw] <;> decide
  rw [rowParity, xorFold_sum]
  change (0 : ZMod 2) + _ = _
  rw [zero_add, List.map_ofFn, List.sum_ofFn]
  rw [show symplecticVec r.decode.word = (symplecticX r.decode.word, symplecticZ r.decode.word) from rfl,
    show symplecticVec s.decode.word = (symplecticX s.decode.word,
        symplecticZ s.decode.word) from rfl,
    symplecticForm_eq_sum_site]
  exact Finset.sum_congr rfl (fun k _ => hsite k)

/-- Row parity is false exactly when the decoded Pauli words have zero symplectic pairing. -/
theorem rowParity_false_iff {n : ℕ} (r s : Row n) :
    rowParity r s = false ↔
      symplecticForm (symplecticVec r.decode.word) (symplecticVec s.decode.word) = 0 := by
  rw [← rowParity_symplectic]
  change rowParity r s = false ↔ boolZModEquiv (rowParity r s) = boolZModEquiv false
  exact boolZModEquiv.injective.eq_iff.symm

/-- Code accumulating the symplectic parity contributions of selected sites in register six. -/
def paritySitesCode {n : ℕ} (a c : RowLayout n) (ks : List (Fin n)) : List (BitInstr 8) :=
  ks.map (fun k => .assign 6 (.bxor (.reg 6) (cocycleLowExpr a c k)))

/-- Initialize register six to false and accumulate the full row symplectic parity. -/
def parityCode {n : ℕ} (a c : RowLayout n) : List (BitInstr 8) :=
  [.assign 6 (.literal false)] ++ paritySitesCode a c (List.ofFn id)

/-- For represented rows, parity site code folds the selected single-site parities into the
initial value of register six. -/
theorem paritySites_correct {n : ℕ} (a c : RowLayout n) (ks : List (Fin n)) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s) :
    bankRead (bitRun (paritySitesCode a c ks) f).regs 6 =
      (ks.map (rowParityAt r s)).foldl xor (bankRead f.regs 6) := by
  induction ks generalizing f with
  | nil => rfl
  | cons k ks ih =>
    let step := BitInstr.assign 6 (.bxor (.reg 6) (cocycleLowExpr a c k))
    have hr' : RepresentsRow (bitStep step f).input a r := hr
    have hs' : RepresentsRow (bitStep step f).input c s := hs
    have h := ih (bitStep step f) hr' hs'
    change bankRead (bitRun (paritySitesCode a c ks) (bitStep step f)).regs 6 = _
    rw [h]
    simp only [List.map_cons, List.foldl_cons]
    congr 1
    simp only [step, bitStep, bankRead_write, if_true, BitExpr.eval, cocycleLowExpr,
      cocycleLow, hr.1, hr.2.1, hs.1, hs.2.1, rowParityAt]

/-- For represented rows, parity code stores their row parity in register six. -/
theorem parityCode_correct {n : ℕ} (a c : RowLayout n) (f : BitFrame 8)
    (r s : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s) :
    bankRead (bitRun (parityCode a c) f).regs 6 = rowParity r s := by
  rw [parityCode, bitRun_append]
  have hr' : RepresentsRow (bitRun [.assign 6 (.literal false)] f).input a r := by
    rw [bitRun_input]; exact hr
  have hs' : RepresentsRow (bitRun [.assign 6 (.literal false)] f).input c s := by
    rw [bitRun_input]; exact hs
  rw [paritySites_correct a c _ _ r s hr' hs']
  simp only [bitRun, List.foldl_cons, List.foldl_nil, bitStep, BitExpr.eval,
    bankRead_write, if_true, List.map_ofFn, Function.comp_id, rowParity]

/-- Executing code that never assigns a particular register preserves that register. -/
theorem bitRun_register {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) (k : Fin R)
    (h : ∀ i ∈ code, match i with | .assign j _ => j ≠ k | .emit _ => True) :
    bankRead (bitRun code f).regs k = bankRead f.regs k := by
  induction code generalizing f with
  | nil => rfl
  | cons i code ih =>
    have h0 := h i (by simp)
    have ht := ih (bitStep i f) (fun j hj => h j (by simp [hj]))
    change bankRead (bitRun code (bitStep i f)).regs k = _
    rw [ht]
    cases i with
    | assign j e =>
      change j ≠ k at h0
      simp only [bitStep, bankRead_write, if_neg (Ne.symm h0)]
    | emit e => rfl

/-- Product-phase code preserves every register other than zero through five. -/
theorem mulPhase_register {n : ℕ} (a c : RowLayout n) (f : BitFrame 8) (k : Fin 8)
    (h0 : (0 : Fin 8) ≠ k) (h1 : (1 : Fin 8) ≠ k) (h2 : (2 : Fin 8) ≠ k)
    (h3 : (3 : Fin 8) ≠ k) (h4 : (4 : Fin 8) ≠ k) (h5 : (5 : Fin 8) ≠ k) :
    bankRead (bitRun (mulPhaseCode a c) f).regs k = bankRead f.regs k := by
  apply bitRun_register
  intro i hi
  simp only [mulPhaseCode, phaseSitesCode, List.mem_append, List.mem_flatMap] at hi
  rcases hi with hi | ⟨j, _, hi⟩
  · simp only [phaseInitCode, phaseAddCode, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5
  · simp only [phaseSiteCode, phaseAddCode, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl) | (rfl | rfl | rfl | rfl)
    all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5

/-- A Boolean multiplexer expression selecting `yes` or `no` according to the condition
expression. -/
def muxExpr {R : ℕ} (c yes no : BitExpr R) : BitExpr R :=
  .bxor (.band c yes) (.band (.bnot c) no)

/-- The multiplexer expression evaluates to the selected branch value. -/
theorem muxExpr_eval {R : ℕ} (c yes no : BitExpr R) (f : BitFrame R) :
    (muxExpr c yes no).eval f.input f.regs =
      if c.eval f.input f.regs then yes.eval f.input f.regs else no.eval f.input f.regs := by
  simp only [muxExpr, BitExpr.eval]
  cases c.eval f.input f.regs <;> simp

/-- Expressions selecting the original row or its product with another row according to parity
register six. -/
def nonpivotExprs {n : ℕ} (a c : RowLayout n) : List (BitExpr 8) :=
  List.ofFn (fun k => muxExpr (.reg 6) (.bxor (.input (a.x k)) (.input (c.x k))) (.input (a.x k))) ++
  List.ofFn (fun k => muxExpr (.reg 6) (.bxor (.input (a.z k)) (.input (c.z k))) (.input (a.z k))) ++
    [muxExpr (.reg 6) (.reg 0) (.input a.low), muxExpr (.reg 6) (.reg 1) (.input a.high)]

/-- Code for a nonpivot measurement row, computing its measurement parity and conditionally
multiplying by the pivot. -/
def nonpivotRowCode {n : ℕ} (a pivot measured : RowLayout n) : List (BitInstr 8) :=
  parityCode a measured ++ mulPhaseCode a pivot ++ emitCode (nonpivotExprs a pivot)

/-- With the product phase and measurement parity in the designated registers, nonpivot
expressions encode the unchanged row for zero symplectic pairing and the product row
otherwise. -/
theorem nonpivotExprs_correct {n : ℕ} (a c : RowLayout n) (f : BitFrame 8)
    (r s p : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input c s)
    (h0 : bankRead f.regs 0 = (r.mul s).phase.val.testBit 0)
    (h1 : bankRead f.regs 1 = (r.mul s).phase.val.testBit 1)
    (h6 : bankRead f.regs 6 = rowParity r p) :
    (nonpivotExprs a c).map (BitExpr.eval f.input f.regs) =
      (if symplecticForm (symplecticVec r.decode.word) (symplecticVec p.decode.word) = 0
        then r else r.mul s).bits := by
  by_cases hc : symplecticForm (symplecticVec r.decode.word) (symplecticVec p.decode.word) = 0
  · have hb : bankRead f.regs 6 = false := h6.trans ((rowParity_false_iff r p).mpr hc)
    simp only [nonpivotExprs, List.map_append, List.map_ofFn, Function.comp_def,
      List.map_cons, List.map_nil, muxExpr_eval, BitExpr.eval, hb, Bool.false_eq_true,
      if_false, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, if_pos hc, Row.bits]
  · have hb : bankRead f.regs 6 = true := by
      rw [h6]
      cases hp : rowParity r p
      · exact False.elim (hc ((rowParity_false_iff r p).mp hp))
      · rfl
    simp only [nonpivotExprs, List.map_append, List.map_ofFn, Function.comp_def,
      List.map_cons, List.map_nil, muxExpr_eval, BitExpr.eval, hb, if_true,
      hr.1, hr.2.1, hs.1, hs.2.1, h0, h1, if_neg hc, Row.bits, Row.mul]

/-- For represented row, pivot, and observable inputs, nonpivot code emits the original row if
it commutes with the observable and its product with the pivot otherwise. -/
theorem nonpivotRowCode_correct {n : ℕ} (a pivot measured : RowLayout n) (f : BitFrame 8)
    (r s p : Row n) (hr : RepresentsRow f.input a r) (hs : RepresentsRow f.input pivot s)
    (hp : RepresentsRow f.input measured p) :
    (bitRun (nonpivotRowCode a pivot measured) f).output =
      (if symplecticForm (symplecticVec r.decode.word) (symplecticVec p.decode.word) = 0
        then r else r.mul s).bits ++ f.output := by
  let f' := bitRun (parityCode a measured) f
  have hr' : RepresentsRow f'.input a r := by dsimp [f']; rw [bitRun_input]; exact hr
  have hs' : RepresentsRow f'.input pivot s := by dsimp [f']; rw [bitRun_input]; exact hs
  have hphase := mulPhaseCode_correct a pivot f' r s hr' hs'
  have h6 := mulPhase_register a pivot f' 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hpar := parityCode_correct a measured f r p hr hp
  have hio := mulPhase_input_output a pivot f'
  have hro : RepresentsRow (bitRun (mulPhaseCode a pivot) f').input a r := by
    rw [bitRun_input]; exact hr'
  have hso : RepresentsRow (bitRun (mulPhaseCode a pivot) f').input pivot s := by
    rw [bitRun_input]; exact hs'
  have hexpr := nonpivotExprs_correct a pivot (bitRun (mulPhaseCode a pivot) f')
    r s p hro hso hphase.1 hphase.2 (h6.trans hpar)
  have hout : f'.output = f.output := by
    apply bitRun_noEmit_output
    intro i hi
    simp only [parityCode, paritySitesCode, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map] at hi
    rcases hi with rfl | ⟨k, _, rfl⟩ <;> rfl
  rw [nonpivotRowCode, bitRun_append, bitRun_append, (emitCode_correct _ _).2.2]
  rw [hexpr, hio.2, hout]

/-- Expressions for the signed measured Pauli row, using register seven as the measurement
outcome. -/
def pivotRowExprs {n : ℕ} (p : RowLayout n) : List (BitExpr 8) :=
  List.ofFn (fun k => .input (p.x k)) ++ List.ofFn (fun k => .input (p.z k)) ++
    [.input p.low, .bxor (.input p.high) (.bnot (.reg 7))]

/-- The signed measured Pauli has the original phase plus two when the Boolean outcome is false. -/
theorem signedMeasured_phase {n : ℕ} (p : PauliElem n) (b : Bool) :
    (signedMeasuredPauli p b).phase = p.phase + if !b then 2 else 0 := by
  cases b with
  | true => simp [signedMeasuredPauli]
  | false =>
    have hzero : ∀ k : Fin n, pauliMulPhase (p.word k) .I = 0 := by
      intro k; cases p.word k <;> rfl
    simp [signedMeasuredPauli, PauliElem.mul, hzero]

/-- Given a represented Pauli and its outcome in register seven, pivot expressions evaluate to
the encoding of the signed measured Pauli. -/
theorem pivotRowExprs_correct {n : ℕ} (a : RowLayout n) (f : BitFrame 8)
    (p : PauliElem n) (b : Bool) (hp : RepresentsRow f.input a (encode p))
    (hb : bankRead f.regs 7 = b) :
    (pivotRowExprs a).map (BitExpr.eval f.input f.regs) = (encode (signedMeasuredPauli p b)).bits := by
  have ht := phase_toggle_bits p.phase (!b)
  simp only [pivotRowExprs, List.map_append, List.map_ofFn, Function.comp_def, List.map_cons,
    List.map_nil, BitExpr.eval, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hb, Row.bits, encode,
    word_signedMeasuredPauli, signedMeasured_phase, ht.1, ht.2]

/-- Parity code preserves every register except register six. -/
theorem parityCode_register {n : ℕ} (a c : RowLayout n) (f : BitFrame 8) (k : Fin 8)
    (hk : (6 : Fin 8) ≠ k) :
    bankRead (bitRun (parityCode a c) f).regs k = bankRead f.regs k := by
  apply bitRun_register
  intro i hi
  simp only [parityCode, paritySitesCode, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hi
  rcases hi with rfl | ⟨j, _, rfl⟩ <;> exact hk

/-- Nonpivot row code preserves the measurement outcome in register seven. -/
theorem nonpivotRowCode_register7 {n : ℕ} (a pivot measured : RowLayout n) (f : BitFrame 8) :
    bankRead (bitRun (nonpivotRowCode a pivot measured) f).regs 7 = bankRead f.regs 7 := by
  rw [nonpivotRowCode, bitRun_append, bitRun_append, (emitCode_correct _ _).2.1]
  rw [mulPhase_register _ _ _ 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    parityCode_register _ _ _ 7 (by decide)]

/-- A row encoding appended to arbitrary front bits represents the row at the offset given by
the front length. -/
theorem representsRow_prefixed {n : ℕ} (frontBits : List Bool) (r : Row n) :
    RepresentsRow (frontBits ++ r.bits) (rowLayout n frontBits.length) r := by
  have h := representsRow_self r
  simp only [RepresentsRow, rowLayout, Nat.zero_add] at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; rw [scanBit_append_right]; exact h.1 i
  · intro i; rw [Nat.add_assoc, scanBit_append_right]; exact h.2.1 i
  · rw [scanBit_append_right]; exact h.2.2.1
  · rw [Nat.add_assoc, scanBit_append_right]; exact h.2.2.2

/-- Compile the update of a selected tableau row, using signed observable emission for the pivot
and conditional multiplication otherwise. -/
def measuredRowCode {n m : ℕ} (a i : Fin m) : List (BitInstr 8) :=
  if i = a then emitCode (pivotRowExprs (rowLayout n (m * rowWidth n)))
  else nonpivotRowCode (rowLayout n (i.val * rowWidth n)) (rowLayout n (a.val * rowWidth n))
    (rowLayout n (m * rowWidth n))

/-- With the encoded tableau and observable as input and the outcome in register seven, measured
row code emits the bit encoding of `measureRow`. -/
theorem measuredRowCode_correct {n m : ℕ} (a i : Fin m) (t : Tableau n m)
    (p : PauliElem n) (b : Bool) (f : BitFrame 8)
    (hf : f.input = tableauBits t ++ (encode p).bits) (hb : bankRead f.regs 7 = b) :
    (bitRun (measuredRowCode (n := n) a i) f).output = (measureRow t a p b i).bits ++ f.output := by
  have hr : RepresentsRow f.input (rowLayout n (i.val * rowWidth n)) (t i) := by
    rw [hf]; exact representsRow_tableau _ _ _
  have hs : RepresentsRow f.input (rowLayout n (a.val * rowWidth n)) (t a) := by
    rw [hf]; exact representsRow_tableau _ _ _
  have hp : RepresentsRow f.input (rowLayout n (m * rowWidth n)) (encode p) := by
    rw [hf]
    simpa only [tableau_bits_length, rowWidth] using!
        representsRow_prefixed (tableauBits t) (encode p)
  by_cases hi : i = a
  · rw [measuredRowCode, if_pos hi, (emitCode_correct _ _).2.2,
      pivotRowExprs_correct _ f p b hp hb, measureRow, if_pos hi]
  · rw [measuredRowCode, if_neg hi, nonpivotRowCode_correct _ _ _ f (t i) (t a) (encode p) hr hs hp]
    simp only [measureRow, if_neg hi, decode_encode]

/-- Measured row code preserves register seven. -/
theorem measuredRowCode_register7 {n m : ℕ} (a i : Fin m) (f : BitFrame 8) :
    bankRead (bitRun (measuredRowCode (n := n) a i) f).regs 7 = bankRead f.regs 7 := by
  by_cases hi : i = a
  · rw [measuredRowCode, if_pos hi, (emitCode_correct _ _).2.1]
  · rw [measuredRowCode, if_neg hi, nonpivotRowCode_register7]

/-- Concatenate indexed row blocks in reverse index-list order to support output prepending. -/
def rowBlocksCode {α : Type} (ks : List α) (code : α → List (BitInstr 8)) : List (BitInstr 8) :=
  ks.reverse.flatMap code

/-- Row block concatenation preserves register seven when every constituent block preserves it. -/
theorem rowBlocks_register7 {α : Type} (ks : List α) (code : α → List (BitInstr 8))
    (hreg : ∀ k ∈ ks, ∀ f, bankRead (bitRun (code k) f).regs 7 = bankRead f.regs 7)
    (f : BitFrame 8) :
    bankRead (bitRun (rowBlocksCode ks code) f).regs 7 = bankRead f.regs 7 := by
  induction ks generalizing f with
  | nil => rfl
  | cons k ks ih =>
    have hcode : rowBlocksCode (k :: ks) code = rowBlocksCode ks code ++ code k := by
      simp [rowBlocksCode]
    rw [hcode, bitRun_append, hreg k (by simp)]
    exact ih (fun j hj => hreg j (by simp [hj])) f

/-- If each row block emits its specified bits and preserves register seven, the combined code
prepends the concatenated row encodings in index-list order. -/
theorem rowBlocks_output {α : Type} (ks : List α) (code : α → List (BitInstr 8))
    (bytes : α → List Bool) (input : List Bool) (b : Bool)
    (hreg : ∀ k ∈ ks, ∀ f, bankRead (bitRun (code k) f).regs 7 = bankRead f.regs 7)
    (hrow : ∀ k ∈ ks, ∀ f, f.input = input → bankRead f.regs 7 = b →
      (bitRun (code k) f).output = bytes k ++ f.output)
    (f : BitFrame 8) (hf : f.input = input) (hb : bankRead f.regs 7 = b) :
    (bitRun (rowBlocksCode ks code) f).output = ks.flatMap bytes ++ f.output := by
  induction ks generalizing f with
  | nil => rfl
  | cons k ks ih =>
    have hcode : rowBlocksCode (k :: ks) code = rowBlocksCode ks code ++ code k := by
      simp [rowBlocksCode]
    have hr := rowBlocks_register7 ks code (fun j hj => hreg j (by simp [hj])) f
    have ht := ih (fun j hj => hreg j (by simp [hj])) (fun j hj => hrow j (by simp [hj])) f hf hb
    rw [hcode, bitRun_append, hrow k (by simp) _ ((bitRun_input _ _).trans hf) (hr.trans hb), ht]
    simp only [List.flatMap_cons, List.append_assoc]

/-- Compile the measurement update of every tableau row for a specified pivot. -/
def measuredTableauCode {n m : ℕ} (a : Fin m) : List (BitInstr 8) :=
  rowBlocksCode (List.ofFn id) (measuredRowCode (n := n) a)

/-- With the tableau and observable encodings as input and the outcome in register seven,
measured tableau code emits the encoding of the measured tableau. -/
theorem measuredTableauCode_correct {n m : ℕ} (a : Fin m) (t : Tableau n m)
    (p : PauliElem n) (b : Bool) (f : BitFrame 8)
    (hf : f.input = tableauBits t ++ (encode p).bits) (hb : bankRead f.regs 7 = b) :
    (bitRun (measuredTableauCode (n := n) a) f).output = tableauBits (measureTableau t a p b) ++ f.output := by
  have h := rowBlocks_output (List.ofFn id) (measuredRowCode (n := n) a)
    (fun i => (measureRow t a p b i).bits) (tableauBits t ++ (encode p).bits) b
    (fun i _ g => measuredRowCode_register7 a i g)
    (fun i _ g hg hgb => measuredRowCode_correct a i t p b g hg hgb) f hf hb
  simpa only [measuredTableauCode, tableauBits, List.flatMap_def, List.map_ofFn,
    Function.comp_def, measureTableau] using! h

/-- Every instruction expression in a code block has at most forty nodes and reads input
addresses at most `A`. -/
def CodeBound (code : List (BitInstr 8)) (A : ℕ) : Prop :=
  ∀ i ∈ code, i.expr.nodes ≤ 40 ∧ i.expr.maxRead ≤ A

/-- Concatenating two blocks satisfying `CodeBound` preserves the common bound. -/
theorem codeBound_append (xs ys : List (BitInstr 8)) (A : ℕ)
    (hx : CodeBound xs A) (hy : CodeBound ys A) : CodeBound (xs ++ ys) A := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hx i hi
  · exact hy i hi

/-- Emission code satisfies `CodeBound` when each source expression has at most forty nodes and
respects the address bound. -/
theorem emitCode_bound (es : List (BitExpr 8)) (A : ℕ)
    (he : ∀ e ∈ es, e.nodes ≤ 40 ∧ e.maxRead ≤ A) : CodeBound (emitCode es) A := by
  intro i hi
  simp only [emitCode, List.mem_map, List.mem_reverse] at hi
  obtain ⟨e, he', rfl⟩ := hi
  exact he e he'

/-- Phase addition code satisfies `CodeBound` for every input address bound. -/
theorem phaseAddCode_bound (A : ℕ) : CodeBound phaseAddCode A := by
  intro i hi
  simp only [phaseAddCode, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [BitInstr.expr, BitExpr.nodes, BitExpr.maxRead]

/-- Phase initialization code satisfies `CodeBound` when both row layouts respect the address
bound. -/
theorem phaseInitCode_bound {n : ℕ} (a c : RowLayout n) (A : ℕ)
    (ha : a.Bounded A) (hc : c.Bounded A) : CodeBound (phaseInitCode a c) A := by
  apply codeBound_append _ _ A ?_ (phaseAddCode_bound A)
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨by simp [BitInstr.expr, BitExpr.nodes], ha.2.2.1⟩
  · exact ⟨by simp [BitInstr.expr, BitExpr.nodes], ha.2.2.2⟩
  · exact ⟨by simp [BitInstr.expr, BitExpr.nodes], hc.2.2.1⟩
  · exact ⟨by simp [BitInstr.expr, BitExpr.nodes], hc.2.2.2⟩

/-- The low and high cocycle expressions each have at most forty nodes and respect the common
row-layout address bound. -/
theorem cocycleExpr_bounds {n : ℕ} (a c : RowLayout n) (A : ℕ)
    (ha : a.Bounded A) (hc : c.Bounded A) (k : Fin n) :
    ((cocycleLowExpr a c k).nodes ≤ 40 ∧ (cocycleLowExpr a c k).maxRead ≤ A) ∧
    ((cocycleHighExpr a c k).nodes ≤ 40 ∧ (cocycleHighExpr a c k).maxRead ≤ A) := by
  simp [cocycleLowExpr, cocycleHighExpr, cocycleLow, cocycleHigh, BitExpr.nodes,
    BitExpr.maxRead, ha.1, ha.2.1, hc.1, hc.2.1]

/-- A phase site block satisfies `CodeBound` when both row layouts respect the address bound. -/
theorem phaseSiteCode_bound {n : ℕ} (a c : RowLayout n) (A : ℕ)
    (ha : a.Bounded A) (hc : c.Bounded A) (k : Fin n) : CodeBound (phaseSiteCode a c k) A := by
  apply codeBound_append _ _ A ?_ (phaseAddCode_bound A)
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact (cocycleExpr_bounds a c A ha hc k).1
  · exact (cocycleExpr_bounds a c A ha hc k).2

/-- Product-phase code satisfies `CodeBound` when both row layouts respect the address bound. -/
theorem mulPhaseCode_bound {n : ℕ} (a c : RowLayout n) (A : ℕ)
    (ha : a.Bounded A) (hc : c.Bounded A) : CodeBound (mulPhaseCode a c) A := by
  apply codeBound_append _ _ A (phaseInitCode_bound a c A ha hc)
  intro i hi
  simp only [phaseSitesCode, List.mem_flatMap] at hi
  obtain ⟨k, _, hi⟩ := hi
  exact phaseSiteCode_bound a c A ha hc k i hi

/-- Parity code satisfies `CodeBound` when both row layouts respect the address bound. -/
theorem parityCode_bound {n : ℕ} (a c : RowLayout n) (A : ℕ)
    (ha : a.Bounded A) (hc : c.Bounded A) : CodeBound (parityCode a c) A := by
  intro i hi
  simp only [parityCode, paritySitesCode, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hi
  rcases hi with rfl | ⟨k, _, rfl⟩
  · simp [BitInstr.expr, BitExpr.nodes, BitExpr.maxRead]
  · simp [BitInstr.expr, cocycleLowExpr, cocycleLow, BitExpr.nodes, BitExpr.maxRead,
      ha.1, ha.2.1, hc.1, hc.2.1]

/-- Each nonpivot expression has at most forty nodes and respects the common row-layout address
bound. -/
theorem nonpivotExprs_bounds {n : ℕ} (a c : RowLayout n) (A : ℕ)
    (ha : a.Bounded A) (hc : c.Bounded A) :
    ∀ e ∈ nonpivotExprs a c, e.nodes ≤ 40 ∧ e.maxRead ≤ A := by
  intro e he
  simp only [nonpivotExprs, List.mem_append, List.mem_ofFn, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with h | h
  · rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp [muxExpr, BitExpr.nodes, BitExpr.maxRead, ha.1, hc.1]
    · simp [muxExpr, BitExpr.nodes, BitExpr.maxRead, ha.2.1, hc.2.1]
  · rcases h with rfl | rfl
    · simp [muxExpr, BitExpr.nodes, BitExpr.maxRead, ha.2.2.1]
    · simp [muxExpr, BitExpr.nodes, BitExpr.maxRead, ha.2.2.2]

/-- Nonpivot row code satisfies `CodeBound` when the row, pivot, and measured layouts respect
the address bound. -/
theorem nonpivotRowCode_bound {n : ℕ} (a pivot measured : RowLayout n) (A : ℕ)
    (ha : a.Bounded A) (hp : pivot.Bounded A) (hm : measured.Bounded A) :
    CodeBound (nonpivotRowCode a pivot measured) A := by
  rw [nonpivotRowCode, List.append_assoc]
  apply codeBound_append _ _ A (parityCode_bound a measured A ha hm)
  exact codeBound_append _ _ A (mulPhaseCode_bound a pivot A ha hp)
    (emitCode_bound _ A (nonpivotExprs_bounds a pivot A ha hp))

/-- Each pivot row expression has at most forty nodes and respects the row-layout address bound. -/
theorem pivotRowExprs_bounds {n : ℕ} (a : RowLayout n) (A : ℕ) (ha : a.Bounded A) :
    ∀ e ∈ pivotRowExprs a, e.nodes ≤ 40 ∧ e.maxRead ≤ A := by
  intro e he
  simp only [pivotRowExprs, List.mem_append, List.mem_ofFn, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with h | h
  · rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨by simp [BitExpr.nodes], ha.1 k⟩
    · exact ⟨by simp [BitExpr.nodes], ha.2.1 k⟩
  · rcases h with rfl | rfl
    · exact ⟨by simp [BitExpr.nodes], ha.2.2.1⟩
    · simp [BitExpr.nodes, BitExpr.maxRead, ha.2.2.2]

/-- A standard row layout at offset `j * rowWidth n`, with `j ≤ m`, is bounded by `(m + 1) *
rowWidth n`. -/
theorem rowLayout_bound {n m j : ℕ} (hj : j ≤ m) :
    (rowLayout n (j * rowWidth n)).Bounded ((m + 1) * rowWidth n) := by
  have hm := Nat.mul_le_mul_right (rowWidth n) hj
  dsimp only [RowLayout.Bounded, rowLayout]
  simp only [Nat.succ_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; have hi := i.isLt; unfold rowWidth at *; omega
  · intro i; have hi := i.isLt; unfold rowWidth at *; omega
  · unfold rowWidth at *; omega
  · unfold rowWidth at *; omega

/-- Measured row code satisfies `CodeBound` with address bound `(m + 1) * rowWidth n`. -/
theorem measuredRowCode_bound {n m : ℕ} (a i : Fin m) :
    CodeBound (measuredRowCode (n := n) a i) ((m + 1) * rowWidth n) := by
  by_cases hi : i = a
  · rw [measuredRowCode, if_pos hi]
    exact emitCode_bound _ _ (pivotRowExprs_bounds _ _ (rowLayout_bound (Nat.le_refl m)))
  · rw [measuredRowCode, if_neg hi]
    exact nonpivotRowCode_bound _ _ _ _ (rowLayout_bound (Nat.le_of_lt i.isLt))
      (rowLayout_bound (Nat.le_of_lt a.isLt)) (rowLayout_bound (Nat.le_refl m))

/-- Measured tableau code satisfies `CodeBound` with address bound `(m + 1) * rowWidth n`. -/
theorem measuredTableauCode_bound {n m : ℕ} (a : Fin m) :
    CodeBound (measuredTableauCode (n := n) a) ((m + 1) * rowWidth n) := by
  intro i hi
  simp only [measuredTableauCode, rowBlocksCode, List.mem_flatMap, List.mem_reverse] at hi
  obtain ⟨j, _, hi⟩ := hi
  exact measuredRowCode_bound a j i hi

/-- Product-phase code has exactly `8 + 6 * n` instructions. -/
theorem mulPhaseCode_length {n : ℕ} (a c : RowLayout n) :
    (mulPhaseCode a c).length = 8 + 6 * n := by
  simp [mulPhaseCode, phaseInitCode, phaseSitesCode, phaseSiteCode, phaseAddCode,
    List.length_flatMap, List.map_ofFn]
  omega

/-- Nonpivot row code has exactly `9 * n + 11` instructions. -/
theorem nonpivotRowCode_length {n : ℕ} (a pivot measured : RowLayout n) :
    (nonpivotRowCode a pivot measured).length = 9 * n + 11 := by
  simp only [nonpivotRowCode, List.length_append, mulPhaseCode_length, parityCode,
    paritySitesCode, List.length_map, List.length_ofFn, emitCode, List.length_reverse,
    nonpivotExprs, List.length_cons, List.length_nil]
  omega

/-- Measured row code has at most `9 * n + 11` instructions. -/
theorem measuredRowCode_length {n m : ℕ} (a i : Fin m) :
    (measuredRowCode (n := n) a i).length ≤ 9 * n + 11 := by
  by_cases hi : i = a
  · rw [measuredRowCode, if_pos hi]
    simp [emitCode, pivotRowExprs]
    omega
  · rw [measuredRowCode, if_neg hi, nonpivotRowCode_length]

/-- If every indexed row block has at most `B` instructions, their concatenation has at most
`ks.length * B` instructions. -/
theorem rowBlocksCode_length {α : Type} (ks : List α) (code : α → List (BitInstr 8)) (B : ℕ)
    (hc : ∀ k ∈ ks, (code k).length ≤ B) :
    (rowBlocksCode ks code).length ≤ ks.length * B := by
  induction ks with
  | nil => simp [rowBlocksCode]
  | cons k ks ih =>
    have hcode : rowBlocksCode (k :: ks) code = rowBlocksCode ks code ++ code k := by
      simp [rowBlocksCode]
    have ht := ih (fun j hj => hc j (by simp [hj]))
    have hh := hc k (by simp)
    rw [hcode, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Measured tableau code has at most `m * (9 * n + 11)` instructions. -/
theorem measuredTableauCode_length {n m : ℕ} (a : Fin m) :
    (measuredTableauCode (n := n) a).length ≤ m * (9 * n + 11) := by
  have h := rowBlocksCode_length (List.ofFn id) (measuredRowCode (n := n) a) (9 * n + 11)
    (fun i _ => measuredRowCode_length a i)
  simpa only [measuredTableauCode, List.length_ofFn] using! h

/-- The trace length of measured tableau code is bounded by its instruction count bound times
the uniform expression-evaluation bound. -/
theorem measuredTableauCode_time {n m : ℕ} (a : Fin m) (f : BitFrame 8) :
    (bitRunTrace (measuredTableauCode (n := n) a) f).length ≤
      m * (9 * n + 11) * ((2 * ((m + 1) * rowWidth n) + 3) * 40 + 2) := by
  have hb := measuredTableauCode_bound (n := n) a
  have ht := bitRun_bound (measuredTableauCode (n := n) a) f 40 ((m + 1) * rowWidth n)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
  exact ht.trans (Nat.mul_le_mul_right _ (measuredTableauCode_length a))

/-- Code copying the first `size` input bits to the front of the output. -/
def copyCode (size : ℕ) : List (BitInstr 8) :=
  emitCode (List.ofFn (fun i : Fin size => .input i.val))

/-- Copying the full input prepends it to the original output list. -/
theorem copyCode_correct (f : BitFrame 8) :
    (bitRun (copyCode f.input.length) f).output = f.input ++ f.output := by
  rw [copyCode, (emitCode_correct _ _).2.2]
  congr 1
  simp only [List.map_ofFn, Function.comp_def, BitExpr.eval]
  have h : (fun i : Fin f.input.length => scanBit f.input i.val) = fun i => f.input[i.val] := by
    funext i
    rw [scanBit_getD, List.getD_eq_getElem _ _ i.isLt]
  rw [h, List.ofFn_getElem]

/-- Copying the full input has trace length at most `f.input.length * (2 * f.input.length + 5)`. -/
theorem copyCode_time (f : BitFrame 8) :
    (bitRunTrace (copyCode f.input.length) f).length ≤ f.input.length * (2 * f.input.length + 5) := by
  have hb : ∀ i ∈ copyCode f.input.length,
      i.expr.nodes ≤ 1 ∧ i.expr.maxRead ≤ f.input.length := by
    intro i hi
    simp only [copyCode, emitCode, List.mem_map, List.mem_reverse, List.mem_ofFn] at hi
    obtain ⟨e, ⟨k, rfl⟩, rfl⟩ := hi
    exact ⟨by simp [BitInstr.expr, BitExpr.nodes], Nat.le_of_lt k.isLt⟩
  have h := bitRun_bound (copyCode f.input.length) f 1 f.input.length
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
  simpa only [copyCode, emitCode, List.length_map, List.length_reverse, List.length_ofFn,
    Nat.mul_one, Nat.add_assoc] using! h

/-- Preparation events selecting the operand or tableau input, together with elementary
bit-machine events. -/
inductive PrepareAction where
  | selectOperand | selectTableau | bit (event : BitAction 8)
  deriving DecidableEq, Repr

/-- A frame for copying an operand with the given registers and an empty output. -/
def operandCopyFrame (operand : List Bool) (regs : BitBank 8) : BitFrame 8 :=
  ⟨operand, regs, []⟩

/-- A frame for copying the tableau with the copied operand already present in the output. -/
def tableauCopyFrame (table operand : List Bool) (regs : BitBank 8) : BitFrame 8 :=
  ⟨table, regs, (bitRun (copyCode operand.length) (operandCopyFrame operand regs)).output⟩

/-- Prepare the measurement input by copying the operand and then prepending the tableau. -/
def prepareInput (table operand : List Bool) (regs : BitBank 8) : List Bool :=
  (bitRun (copyCode table.length) (tableauCopyFrame table operand regs)).output

/-- Generate the input-selection and bit-copy trace for preparing a measurement input. -/
def prepareTrace (table operand : List Bool) (regs : BitBank 8) : List PrepareAction :=
  .selectOperand :: ((bitRunTrace (copyCode operand.length) (operandCopyFrame operand regs)).map .bit ++
    .selectTableau :: (bitRunTrace (copyCode table.length) (tableauCopyFrame table operand regs)).map .bit)

/-- Input preparation produces the tableau bits followed by the operand bits. -/
theorem prepareInput_correct (table operand : List Bool) (regs : BitBank 8) :
    prepareInput table operand regs = table ++ operand := by
  have htable := copyCode_correct (tableauCopyFrame table operand regs)
  change (bitRun (copyCode table.length) (tableauCopyFrame table operand regs)).output =
    table ++ (bitRun (copyCode operand.length) (operandCopyFrame operand regs)).output at htable
  have hop := copyCode_correct (operandCopyFrame operand regs)
  change (bitRun (copyCode operand.length) (operandCopyFrame operand regs)).output = operand ++
      [] at hop
  exact htable.trans (by rw [hop, List.append_nil])

/-- The preparation trace is bounded by the sum of the two full-input copy bounds plus two
input-selection events. -/
theorem prepareTrace_time (table operand : List Bool) (regs : BitBank 8) :
    (prepareTrace table operand regs).length ≤
      operand.length * (2 * operand.length + 5) + table.length * (2 * table.length + 5) + 2 := by
  have hop := copyCode_time (operandCopyFrame operand regs)
  change (bitRunTrace (copyCode operand.length) (operandCopyFrame operand regs)).length ≤
    operand.length * (2 * operand.length + 5) at hop
  have htable := copyCode_time (tableauCopyFrame table operand regs)
  change (bitRunTrace (copyCode table.length) (tableauCopyFrame table operand regs)).length ≤
    table.length * (2 * table.length + 5) at htable
  simp only [prepareTrace, List.length_cons, List.length_append, List.length_map]
  omega

/-- Finite simulator programs whose random measurement operands are raw bit lists and whose
deterministic steps retain only the outcome. -/
inductive RawProgram (n m : ℕ) where
  | halt
  | gate (g : CliffordGate n) (next : RawProgram n m)
  | random (a : Fin m) (operand : List Bool) (onFalse onTrue : RawProgram n m)
  | deterministic (b : Bool) (next : RawProgram n m)

/-- Encode a tableau program as a raw program by replacing Pauli measurement operands with their
row bit encodings. -/
def encodeProgram {n m : ℕ} : Program n m → RawProgram n m
  | .halt => .halt
  | .gate g next => .gate g (encodeProgram next)
  | .random a p onFalse onTrue =>
      .random a (encode p).bits (encodeProgram onFalse) (encodeProgram onTrue)
  | .deterministic _ b next => .deterministic b (encodeProgram next)

/-- A raw simulator state containing encoded tableau bits, the remaining random tape, stored
outcomes, and eight Boolean registers. -/
structure RawState where
  bits : List Bool
  tape : List Bool
  outcomes : List Bool
  regs : BitBank 8

/-- Events of the raw simulator, covering bit execution, input preparation, control flow, random
reads, and outcome recording. -/
inductive RunAction where
  | bit (event : BitAction 8)
  | prepare (event : PrepareAction)
  | enterGate | enterRandom | enterDeterministic
  | selectTableau | selectWork | swapOutput
  | readFair (b : Bool) | storeOutcome (b : Bool) | literalOutcome (b : Bool)
  | recordLeft | recordWrite (b : Bool) | branch (b : Bool) | halt
  deriving DecidableEq, Repr

/-- The final raw simulator state paired with its event trace. -/
structure RawResult where
  state : RawState
  trace : List RunAction

/-- Prepend events to a raw result's trace. -/
def RawResult.prepend (events : List RunAction) (r : RawResult) : RawResult :=
  ⟨r.state, events ++ r.trace⟩

/-- The bit-instruction frame for applying a gate to a raw state's tableau encoding. -/
def rawGateFrame (s : RawState) : BitFrame 8 := ⟨s.bits, s.regs, []⟩

/-- Execute compiled gate tableau code and replace the raw tableau bits and registers by its
results. -/
def rawGateStep {n m : ℕ} (s : RawState) (g : CliffordGate n) : RawState :=
  let f := bitRun (gateTableauCode (m := m) g) (rawGateFrame s)
  { s with bits := f.output, regs := f.regs }

/-- The raw event trace for entering a gate, selecting the tableau, executing its bit code, and
installing the output. -/
def rawGateTrace {n m : ℕ} (s : RawState) (g : CliffordGate n) : List RunAction :=
  [.enterGate, .selectTableau] ++
    (bitRunTrace (gateTableauCode (m := m) g) (rawGateFrame s)).map .bit ++ [.swapOutput]

/-- Prepare a measurement frame by storing the outcome in register seven and concatenating the
tableau and operand encodings. -/
def rawMeasureFrame (s : RawState) (operand : List Bool) (b : Bool) : BitFrame 8 :=
  let regs := bankWrite s.regs 7 b
  ⟨prepareInput s.bits operand regs, regs, []⟩

/-- Execute compiled measured tableau code, replace the random tape, and prepend the outcome to
the stored record. -/
def rawRandomStep {n m : ℕ} (s : RawState) (a : Fin m) (operand : List Bool)
    (b : Bool) (rest : List Bool) : RawState :=
  let f := bitRun (measuredTableauCode (n := n) a) (rawMeasureFrame s operand b)
  ⟨f.output, rest, b :: s.outcomes, f.regs⟩

/-- The raw event trace for a random measurement, including one fair read, operand preparation,
tableau update, outcome recording, and branch selection. -/
def rawRandomTrace {n m : ℕ} (s : RawState) (a : Fin m) (operand : List Bool)
    (b : Bool) : List RunAction :=
  [.enterRandom, .readFair b, .storeOutcome b] ++
    (prepareTrace s.bits operand (bankWrite s.regs 7 b)).map .prepare ++
    [.selectWork] ++
    (bitRunTrace (measuredTableauCode (n := n) a) (rawMeasureFrame s operand b)).map .bit ++
    [.recordLeft, .recordWrite b, .branch b, .swapOutput]

/-- Prepend a deterministic outcome to the raw state's stored record. -/
def rawDeterministicStep (s : RawState) (b : Bool) : RawState :=
  { s with outcomes := b :: s.outcomes }

/-- The four-event trace for entering a deterministic step and recording its fixed outcome. -/
def rawDeterministicTrace (b : Bool) : List RunAction :=
  [.enterDeterministic, .literalOutcome b, .recordLeft, .recordWrite b]

/-- Execute a finite raw program and accumulate its event trace, returning `none` if a random
step encounters an empty tape. -/
def rawRun {n m : ℕ} : RawProgram n m → RawState → Option RawResult
  | .halt, s => some ⟨s, [.halt]⟩
  | .gate g next, s =>
      (rawRun next (rawGateStep (m := m) s g)).map (RawResult.prepend (rawGateTrace (m := m) s g))
  | .random a operand onFalse onTrue, s =>
      match s.tape with
      | [] => none
      | false :: rest =>
          (rawRun onFalse (rawRandomStep (n := n) s a operand false rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) s a operand false))
      | true :: rest =>
          (rawRun onTrue (rawRandomStep (n := n) s a operand true rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) s a operand true))
  | .deterministic b next, s =>
      (rawRun next (rawDeterministicStep s b)).map (RawResult.prepend (rawDeterministicTrace b))

/-- Initialize a raw state with specified tableau bits and random tape, empty outcomes, and
eight false registers. -/
def rawInitial (bits tape : List Bool) : RawState :=
  ⟨bits, tape, [], ⟨Array.replicate 8 false, by simp⟩⟩

/-- A raw state represents a tableau machine when its tableau encoding, random tape, and stored
outcomes agree. -/
def RepresentsMachine {n m : ℕ} (r : RawState) (s : Machine n m) : Prop :=
  r.bits = tableauBits s.tableau ∧ r.tape = s.tape ∧ r.outcomes = s.outcomes

/-- The initial raw state represents the initial tableau machine. -/
theorem rawInitial_represents {n m : ℕ} (t : Tableau n m) (tape : List Bool) :
    RepresentsMachine (rawInitial (tableauBits t) tape) (initial t tape) := ⟨rfl, rfl, rfl⟩

/-- A compiled raw gate step preserves representation of the corresponding tableau gate step. -/
theorem rawGateStep_represents {n m : ℕ} (r : RawState) (s : Machine n m)
    (h : RepresentsMachine r s) (g : CliffordGate n) :
    RepresentsMachine (rawGateStep (m := m) r g) (gateStep s g) := by
  refine ⟨?_, h.2.1, h.2.2⟩
  have hg := gateTableauCode_correct g s.tableau (rawGateFrame r) h.1
  simpa only [rawGateStep, rawGateFrame, gateStep, List.append_nil] using! hg

/-- A compiled raw random step with an encoded Pauli operand represents the corresponding
tableau random step. -/
theorem rawRandomStep_represents {n m : ℕ} (r : RawState) (s : Machine n m)
    (h : RepresentsMachine r s) (a : Fin m) (p : PauliElem n) (b : Bool) (rest : List Bool) :
    RepresentsMachine (rawRandomStep (n := n) r a (encode p).bits b rest) (randomStep s a p b rest) := by
  have hf : (rawMeasureFrame r (encode p).bits b).input =
      tableauBits s.tableau ++ (encode p).bits := by
    change prepareInput r.bits (encode p).bits (bankWrite r.regs 7 b) = _
    rw [prepareInput_correct, h.1]
  have hb : bankRead (rawMeasureFrame r (encode p).bits b).regs 7 = b := by
    simp [rawMeasureFrame]
  have hm := measuredTableauCode_correct a s.tableau p b (rawMeasureFrame r (encode p).bits b) hf hb
  refine ⟨?_, rfl, ?_⟩
  · simpa only [rawRandomStep, rawMeasureFrame, List.append_nil, randomStep,
      measureTableau_eq] using! hm
  · change b :: r.outcomes = b :: s.outcomes
    rw [h.2.2]

/-- A raw deterministic step preserves representation of the corresponding tableau deterministic
step. -/
theorem rawDeterministicStep_represents {n m : ℕ} (r : RawState) (s : Machine n m)
    (h : RepresentsMachine r s) (b : Bool) :
    RepresentsMachine (rawDeterministicStep r b) (deterministicStep s b) := by
  exact ⟨h.1, h.2.1, congrArg (List.cons b) h.2.2⟩

/-- Test whether a raw event reads a fair random bit. -/
def RunAction.isFairRead : RunAction → Bool
  | .readFair _ => true
  | _ => false

/-- Count the fair random bit read events in a raw trace. -/
def fairReads (events : List RunAction) : ℕ := events.countP RunAction.isFairRead

/-- The number of fair reads is additive under trace concatenation. -/
theorem fairReads_append (xs ys : List RunAction) : fairReads (xs ++ ys) = fairReads xs + fairReads ys := by
  simp [fairReads]

/-- A raw gate trace contains no fair reads. -/
theorem fairReads_gate {n m : ℕ} (s : RawState) (g : CliffordGate n) :
    fairReads (rawGateTrace (m := m) s g) = 0 := by
  simp [fairReads, rawGateTrace, RunAction.isFairRead, List.countP_map]

/-- A raw random measurement trace contains exactly one fair read. -/
theorem fairReads_random {n m : ℕ} (s : RawState) (a : Fin m) (operand : List Bool) (b : Bool) :
    fairReads (rawRandomTrace (n := n) s a operand b) = 1 := by
  simp [fairReads, rawRandomTrace, RunAction.isFairRead, List.countP_map]

/-- A raw deterministic measurement trace contains no fair reads. -/
theorem fairReads_deterministic (b : Bool) : fairReads (rawDeterministicTrace b) = 0 := by
  rfl

/-- A successful tableau execution has a corresponding encoded raw execution whose final state
represents the result and whose fair reads equal the consumed fair bits. -/
theorem rawRun_simulates {n m : ℕ} (program : Program n m) :
    ∀ (r : RawState) (s result : Machine n m), RepresentsMachine r s →
      execute program s = some result →
      ∃ rr, rawRun (encodeProgram program) r = some rr ∧ RepresentsMachine rr.state result ∧
        fairReads rr.trace = Program.consumedFairBits program s.tape := by
  induction program with
  | halt =>
    intro r s result hs he
    cases he
    exact ⟨⟨r, [.halt]⟩, rfl, hs, rfl⟩
  | gate g next ih =>
    intro r s result hs he
    have he' : execute next (gateStep s g) = some result := he
    obtain ⟨rr, hr, hrep, hfair⟩ := ih (rawGateStep (m := m) r g) (gateStep s g) result
      (rawGateStep_represents r s hs g) he'
    refine ⟨rr.prepend (rawGateTrace (m := m) r g), ?_, hrep, ?_⟩
    · simp only [encodeProgram, rawRun, hr, Option.map_some]
    · simpa only [RawResult.prepend, fairReads_append, fairReads_gate, Nat.zero_add,
        Program.consumedFairBits, gateStep] using! hfair
  | random a p onFalse onTrue ihFalse ihTrue =>
    intro r s result hs he
    cases ht : s.tape with
    | nil => simp [execute, ht] at he
    | cons b rest =>
      have hrt : r.tape = b :: rest := hs.2.1.trans ht
      cases b with
      | false =>
        have he' : execute onFalse (randomStep s a p false rest) = some result := by
          simpa only [execute, ht] using! he
        obtain ⟨rr, hr, hrep, hfair⟩ := ihFalse _ _ result
          (rawRandomStep_represents r s hs a p false rest) he'
        refine ⟨rr.prepend (rawRandomTrace (n := n) r a (encode p).bits false), ?_, hrep, ?_⟩
        · simp only [encodeProgram, rawRun, hrt, hr, Option.map_some]
        · simpa only [RawResult.prepend, fairReads_append, fairReads_random,
            Program.consumedFairBits, ht, randomStep] using! congrArg (1 + ·) hfair
      | true =>
        have he' : execute onTrue (randomStep s a p true rest) = some result := by
          simpa only [execute, ht] using! he
        obtain ⟨rr, hr, hrep, hfair⟩ := ihTrue _ _ result
          (rawRandomStep_represents r s hs a p true rest) he'
        refine ⟨rr.prepend (rawRandomTrace (n := n) r a (encode p).bits true), ?_, hrep, ?_⟩
        · simp only [encodeProgram, rawRun, hrt, hr, Option.map_some]
        · simpa only [RawResult.prepend, fairReads_append, fairReads_random,
            Program.consumedFairBits, ht, randomStep] using! congrArg (1 + ·) hfair
  | deterministic p b next ih =>
    intro r s result hs he
    have he' : execute next (deterministicStep s b) = some result := he
    obtain ⟨rr, hr, hrep, hfair⟩ := ih _ _ result (rawDeterministicStep_represents r s hs b) he'
    refine ⟨rr.prepend (rawDeterministicTrace b), ?_, hrep, ?_⟩
    · simp only [encodeProgram, rawRun, hr, Option.map_some]
    · simpa only [RawResult.prepend, fairReads_append, fairReads_deterministic, Nat.zero_add,
        Program.consumedFairBits, deterministicStep] using! hfair

/-- A valid program with sufficient random tape has matching raw and physical executions from a
normalized code-space state. The physical result remains normalized in the represented code
space and has joint mass one half raised to the raw fair-read count. -/
theorem raw_physical {n m : ℕ} (program : Program n m) (t : Tableau n m) (tape : List Bool)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n))
    (hv : Program.Valid t program) (ht : Qatlib.Concepts.PauliClifford.PauliAlgebra.ConsistentTableau t)
    (hn : Qatlib.Foundations.PureStateMath.Normalized ψ) (hψ : ψ ∈ codeSpace t)
    (hbudget : program.maxFairBits ≤ tape.length) :
    ∃ rr pr, rawRun (encodeProgram program) (rawInitial (tableauBits t) tape) = some rr ∧
      physicalExecute program (initial t tape) ψ = some pr ∧ RepresentsMachine rr.state pr.machine ∧
      Qatlib.Foundations.PureStateMath.Normalized pr.state ∧ pr.state ∈ codeSpace pr.machine.tableau ∧
      pr.jointMass = (1 / 2 : ℝ) ^ fairReads rr.trace := by
  obtain ⟨pr, hp⟩ := physicalExecute_some program (initial t tape) ψ hbudget
  have he := physicalExecute_machine program hp
  obtain ⟨rr, hr, hrep, hfair⟩ := rawRun_simulates program _ _ _ (rawInitial_represents t tape) he
  have hc := physicalExecute_correct program hp hv ht hn hψ
  refine ⟨rr, pr, hr, hp, hrep, hc.1.1, hc.1.2, ?_⟩
  rw [hfair]
  exact hc.2

/-- Gate tableau code satisfies `CodeBound` with address bound `(m + 1) * rowWidth n`. -/
theorem gateTableauCode_bound {n m : ℕ} (g : CliffordGate n) :
    CodeBound (gateTableauCode (m := m) g) ((m + 1) * rowWidth n) := by
  apply emitCode_bound
  intro e he
  simp only [gateTableauExprs, List.mem_flatten, List.mem_ofFn] at he
  obtain ⟨es, ⟨j, rfl⟩, he⟩ := he
  have h := gateRowExprs_bounds (rowLayout n (j.val * rowWidth n)) g _
    (rowLayout_bound (Nat.le_of_lt j.isLt)) e he
  exact ⟨by omega, h.2⟩

/-- Gate tableau code has exactly `m * rowWidth n` instructions. -/
theorem gateTableauCode_length {n m : ℕ} (g : CliffordGate n) :
    (gateTableauCode (m := m) g).length = m * rowWidth n := by
  simp [gateTableauCode, emitCode, gateTableauExprs, List.length_flatten, List.map_ofFn,
    Function.comp_def, gateRowExprs_length]

/-- The uniform per-instruction event bound for expressions with at most forty nodes and input
addresses at most `(m + 1) * rowWidth n`. -/
def instructionFactor (n m : ℕ) : ℕ := (2 * ((m + 1) * rowWidth n) + 3) * 40 + 2

/-- The gate tableau trace budget obtained from its instruction count and `instructionFactor`. -/
def gateBudget (n m : ℕ) : ℕ := m * rowWidth n * instructionFactor n m

/-- The measured tableau trace budget obtained from its instruction count bound and
`instructionFactor`. -/
def measureBudget (n m : ℕ) : ℕ := m * (9 * n + 11) * instructionFactor n m

/-- The input-preparation budget for copying an encoded Pauli operand and an encoded tableau. -/
def prepareBudget (n m : ℕ) : ℕ := rowWidth n * (2 * rowWidth n + 5) +
  (m * rowWidth n) * (2 * (m * rowWidth n) + 5) + 2

/-- A common raw step budget combining gate, measurement, preparation, and fixed control-event
allowances. -/
def rawStepBound (n m : ℕ) : ℕ := gateBudget n m + measureBudget n m + prepareBudget n m + 16

/-- The compiled gate tableau trace has length at most `gateBudget n m`. -/
theorem gateTableauCode_time {n m : ℕ} (g : CliffordGate n) (f : BitFrame 8) :
    (bitRunTrace (gateTableauCode (m := m) g) f).length ≤ gateBudget n m := by
  have hb := gateTableauCode_bound (m := m) g
  have ht := bitRun_bound (gateTableauCode (m := m) g) f 40 ((m + 1) * rowWidth n)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
  simpa only [gateTableauCode_length, gateBudget, instructionFactor] using! ht

/-- The raw gate trace has length at most `rawStepBound n m`. -/
theorem rawGateTrace_time {n m : ℕ} (r : RawState) (g : CliffordGate n) :
    (rawGateTrace (m := m) r g).length ≤ rawStepBound n m := by
  have h := gateTableauCode_time (m := m) g (rawGateFrame r)
  simp only [rawGateTrace, List.length_append, List.length_map, List.length_cons, List.length_nil]
  unfold rawStepBound
  omega

/-- For a raw tableau encoding of the expected length and an encoded Pauli operand, the random
step trace has length at most `rawStepBound n m`. -/
theorem rawRandomTrace_time {n m : ℕ} (r : RawState) (a : Fin m) (p : PauliElem n) (b : Bool)
    (hlen : r.bits.length = m * rowWidth n) :
    (rawRandomTrace (n := n) r a (encode p).bits b).length ≤ rawStepBound n m := by
  have hprep := prepareTrace_time r.bits (encode p).bits (bankWrite r.regs 7 b)
  have hrow : (encode p).bits.length = rowWidth n := (rowWidth_eq_bits_length _).symm
  rw [hlen, hrow] at hprep
  have hbit := measuredTableauCode_time (n := n) a (rawMeasureFrame r (encode p).bits b)
  change _ ≤ measureBudget n m at hbit
  change _ ≤ prepareBudget n m at hprep
  simp only [rawRandomTrace, List.length_append, List.length_map, List.length_cons, List.length_nil]
  unfold rawStepBound
  omega

/-- A deterministic step trace has length at most `rawStepBound n m`. -/
theorem rawDeterministicTrace_time (n m : ℕ) (b : Bool) :
    (rawDeterministicTrace b).length ≤ rawStepBound n m := by
  simp only [rawDeterministicTrace, List.length_cons, List.length_nil]
  unfold rawStepBound
  omega

/-- If `m ≤ n`, the raw step budget for `m` rows is at most the budget for `n` rows. -/
theorem rawStepBound_mono {n m : ℕ} (hm : m ≤ n) : rawStepBound n m ≤ rawStepBound n n := by
  unfold rawStepBound gateBudget measureBudget prepareBudget instructionFactor
  gcongr

/-- Matching successful raw and tableau executions have raw trace length at most `1 +
program.maxSteps * rawStepBound n m`. -/
theorem rawRun_time {n m : ℕ} (program : Program n m) :
    ∀ (r : RawState) (s result : Machine n m) (rr : RawResult), RepresentsMachine r s →
      execute program s = some result → rawRun (encodeProgram program) r = some rr →
      rr.trace.length ≤ 1 + program.maxSteps * rawStepBound n m := by
  induction program with
  | halt =>
    intro r s result rr _ _ hr
    cases hr
    simp [Program.maxSteps]
  | gate g next ih =>
    intro r s result rr hs he hr
    have he' : execute next (gateStep s g) = some result := he
    have hr' : (rawRun (encodeProgram next) (rawGateStep (m := m) r g)).map
        (RawResult.prepend (rawGateTrace (m := m) r g)) = some rr := hr
    obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
    subst rr
    have ht := ih _ _ result rr' (rawGateStep_represents r s hs g) he' hn
    have hg := rawGateTrace_time (m := m) r g
    simp only [RawResult.prepend, List.length_append, Program.maxSteps, Nat.add_mul, Nat.one_mul]
    omega
  | random a p onFalse onTrue ihFalse ihTrue =>
    intro r s result rr hs he hr
    have hlen : r.bits.length = m * rowWidth n := by rw [hs.1, tableau_bits_length]; rfl
    cases ht : s.tape with
    | nil => simp [execute, ht] at he
    | cons b rest =>
      have hrt : r.tape = b :: rest := hs.2.1.trans ht
      cases b with
      | false =>
        have he' : execute onFalse (randomStep s a p false rest) = some result := by
          simpa only [execute, ht] using! he
        have hr' : (rawRun (encodeProgram onFalse) (rawRandomStep (n := n) r a (encode p).bits false rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) r a (encode p).bits false)) = some rr := by
          simpa only [encodeProgram, rawRun, hrt] using! hr
        obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
        subst rr
        have hrec := ihFalse _ _ result rr' (rawRandomStep_represents r s hs a p false rest) he' hn
        have hstep := rawRandomTrace_time r a p false hlen
        have hmax := Nat.mul_le_mul_right (rawStepBound n m)
          (Nat.le_max_left onFalse.maxSteps onTrue.maxSteps)
        simp only [RawResult.prepend, List.length_append, Program.maxSteps, Nat.add_mul,
            Nat.one_mul]
        omega
      | true =>
        have he' : execute onTrue (randomStep s a p true rest) = some result := by
          simpa only [execute, ht] using! he
        have hr' : (rawRun (encodeProgram onTrue) (rawRandomStep (n := n) r a (encode p).bits true rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) r a (encode p).bits true)) = some rr := by
          simpa only [encodeProgram, rawRun, hrt] using! hr
        obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
        subst rr
        have hrec := ihTrue _ _ result rr' (rawRandomStep_represents r s hs a p true rest) he' hn
        have hstep := rawRandomTrace_time r a p true hlen
        have hmax := Nat.mul_le_mul_right (rawStepBound n m)
          (Nat.le_max_right onFalse.maxSteps onTrue.maxSteps)
        simp only [RawResult.prepend, List.length_append, Program.maxSteps, Nat.add_mul,
            Nat.one_mul]
        omega
  | deterministic p b next ih =>
    intro r s result rr hs he hr
    have he' : execute next (deterministicStep s b) = some result := he
    have hr' : (rawRun (encodeProgram next) (rawDeterministicStep r b)).map
        (RawResult.prepend (rawDeterministicTrace b)) = some rr := hr
    obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
    subst rr
    have hrec := ih _ _ result rr' (rawDeterministicStep_represents r s hs b) he' hn
    have hstep := rawDeterministicTrace_time n m b
    simp only [RawResult.prepend, List.length_append, Program.maxSteps, Nat.add_mul, Nat.one_mul]
    omega

/-- In a successful raw execution, the number of fair reads plus the remaining tape length
equals the initial tape length. -/
theorem rawRun_tape_conservation {n m : ℕ} (program : RawProgram n m) :
    ∀ (s : RawState) (rr : RawResult), rawRun program s = some rr →
      fairReads rr.trace + rr.state.tape.length = s.tape.length := by
  induction program with
  | halt =>
    intro s rr hr
    cases hr
    simp [fairReads, RunAction.isFairRead]
  | gate g next ih =>
    intro s rr hr
    have hr' : (rawRun next (rawGateStep (m := m) s g)).map
        (RawResult.prepend (rawGateTrace (m := m) s g)) = some rr := hr
    obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
    subst rr
    have hrec := ih _ rr' hn
    simpa only [RawResult.prepend, fairReads_append, fairReads_gate, Nat.zero_add,
        rawGateStep] using! hrec
  | random a operand onFalse onTrue ihFalse ihTrue =>
    intro s rr hr
    cases ht : s.tape with
    | nil => simp [rawRun, ht] at hr
    | cons b rest =>
      cases b with
      | false =>
        have hr' : (rawRun onFalse (rawRandomStep (n := n) s a operand false rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) s a operand false)) = some rr := by
          simpa only [rawRun, ht] using! hr
        obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
        subst rr
        have hrec := ihFalse _ rr' hn
        change fairReads rr'.trace + rr'.state.tape.length = rest.length at hrec
        simp only [RawResult.prepend, fairReads_append, fairReads_random, List.length_cons]
        omega
      | true =>
        have hr' : (rawRun onTrue (rawRandomStep (n := n) s a operand true rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) s a operand true)) = some rr := by
          simpa only [rawRun, ht] using! hr
        obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
        subst rr
        have hrec := ihTrue _ rr' hn
        change fairReads rr'.trace + rr'.state.tape.length = rest.length at hrec
        simp only [RawResult.prepend, fairReads_append, fairReads_random, List.length_cons]
        omega
  | deterministic b next ih =>
    intro s rr hr
    have hr' : (rawRun next (rawDeterministicStep s b)).map
        (RawResult.prepend (rawDeterministicTrace b)) = some rr := hr
    obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
    subst rr
    have hrec := ih _ rr' hn
    simpa only [RawResult.prepend, fairReads_append, fairReads_deterministic,
      Nat.zero_add, rawDeterministicStep] using! hrec

/-- For a valid program with sufficient tape and `m ≤ n`, matching raw and physical executions
preserve the state conditions and have the stated branch mass, tape conservation, and trace
length bound. -/
theorem rawPhysicalTime {n m : ℕ} (program : Program n m) (t : Tableau n m) (tape : List Bool)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) (hm : m ≤ n)
    (hv : Program.Valid t program) (ht : Qatlib.Concepts.PauliClifford.PauliAlgebra.ConsistentTableau t)
    (hn : Qatlib.Foundations.PureStateMath.Normalized ψ) (hψ : ψ ∈ codeSpace t)
    (hbudget : program.maxFairBits ≤ tape.length) :
    ∃ rr pr, rawRun (encodeProgram program) (rawInitial (tableauBits t) tape) = some rr ∧
      physicalExecute program (initial t tape) ψ = some pr ∧ RepresentsMachine rr.state pr.machine ∧
      Qatlib.Foundations.PureStateMath.Normalized pr.state ∧ pr.state ∈ codeSpace pr.machine.tableau ∧
      pr.jointMass = (1 / 2 : ℝ) ^ fairReads rr.trace ∧
      fairReads rr.trace + rr.state.tape.length = tape.length ∧
      rr.trace.length ≤ 1 + program.maxSteps * rawStepBound n n := by
  obtain ⟨rr, pr, hr, hp, hrep, hnorm, hcode, hmass⟩ :=
      raw_physical program t tape ψ hv ht hn hψ hbudget
  have htime := rawRun_time program _ _ _ rr (rawInitial_represents t tape)
    (physicalExecute_machine program hp) hr
  have hmono := Nat.mul_le_mul_left program.maxSteps (rawStepBound_mono hm)
  exact ⟨rr, pr, hr, hp, hrep, hnorm, hcode, hmass,
    rawRun_tape_conservation _ _ _ hr, htime.trans (by omega)⟩

/-- A cell-machine configuration with input, registers, output, an input head position, and an
evaluation stack. -/
structure CellConfig (R : ℕ) where
  input : List Bool
  regs : BitBank R
  output : List Bool
  head : ℕ
  stack : List Bool

/-- The single-event cell-machine transition relation for head motion, Boolean stack operations,
register access, and output writing. -/
inductive CellStep {R : ℕ} : CellConfig R → BitAction R → CellConfig R → Prop where
  | right (f : CellConfig R) : CellStep f .right { f with head := f.head + 1 }
  | left (f : CellConfig R) : CellStep f .left { f with head := f.head - 1 }
  | read (f : CellConfig R) : CellStep f (.readInput (f.input.getD f.head false))
      { f with stack := f.input.getD f.head false :: f.stack }
  | literal (f : CellConfig R) (b : Bool) : CellStep f (.literal b) { f with stack := b :: f.stack }
  | reg (f : CellConfig R) (i : Fin R) : CellStep f (.readRegister i (bankRead f.regs i))
      { f with stack := bankRead f.regs i :: f.stack }
  | bnot (f : CellConfig R) (b : Bool) (bs : List Bool) : CellStep { f with stack := b :: bs } (.bnot b) { f with stack := (!b) :: bs }
  | band (f : CellConfig R) (a b : Bool) (bs : List Bool) : CellStep { f with stack := b :: a :: bs } (.band a b)
      { f with stack := (a && b) :: bs }
  | bxor (f : CellConfig R) (a b : Bool) (bs : List Bool) : CellStep { f with stack := b :: a :: bs } (.bxor a b)
      { f with stack := xor a b :: bs }
  | store (f : CellConfig R) (i : Fin R) (b : Bool) (bs : List Bool) : CellStep { f with stack := b :: bs } (.writeRegister i b)
      { f with stack := bs, regs := bankWrite f.regs i b }
  | outputLeft (f : CellConfig R) : CellStep f .outputLeft { f with output := false :: f.output }
  | outputWrite (f : CellConfig R) (b old : Bool) (bs out : List Bool) :
      CellStep { f with stack := b :: bs, output := old :: out } (.writeOutput b)
        { f with stack := bs, output := b :: out }

/-- The finite-trace execution relation generated by cell-machine steps. -/
inductive CellExec {R : ℕ} : CellConfig R → List (BitAction R) → CellConfig R → Prop where
  | nil (f) : CellExec f [] f
  | cons {f g h e es} : CellStep f e g → CellExec g es h → CellExec f (e :: es) h

/-- A cell-machine step gives an execution of its singleton event trace. -/
theorem CellExec.single {R : ℕ} {f g : CellConfig R} {e : BitAction R} (h : CellStep f e g) :
    CellExec f [e] g := .cons h (.nil _)

/-- Cell-machine executions compose by concatenating their traces. -/
theorem CellExec.trans {R : ℕ} {f g h : CellConfig R} {xs ys : List (BitAction R)}
    (hx : CellExec f xs g) (hy : CellExec g ys h) : CellExec f (xs ++ ys) h := by
  induction hx with
  | nil => exact hy
  | cons he _ ih => exact .cons he (ih hy)

/-- The cell-space measure counting registers, output bits, stack bits, and the input head
position. -/
def cellSpace {R : ℕ} (f : CellConfig R) : ℕ := R + f.output.length + f.stack.length + f.head

/-- One cell-machine event increases `cellSpace` by at most one. -/
theorem cellStep_space {R : ℕ} {f g : CellConfig R} {e : BitAction R} (h : CellStep f e g) :
    cellSpace g ≤ cellSpace f + 1 := by
  cases h <;> simp only [cellSpace, List.length_cons] <;> omega

/-- A cell-machine execution increases `cellSpace` by at most its trace length. -/
theorem cellExec_space {R : ℕ} {f g : CellConfig R} {es : List (BitAction R)} (h : CellExec f es g) :
    cellSpace g ≤ cellSpace f + es.length := by
  induction h with
  | nil => simp
  | @cons f g h e es hs _ ih =>
    have hh := cellStep_space hs
    simp only [List.length_cons]
    omega

/-- The cell space reached after any executable trace prefix is bounded by the initial space
plus the full trace length. -/
theorem cellExec_prefix_space {R : ℕ} (f : CellConfig R) (es : List (BitAction R))
    (prefixEvents suffixEvents : List (BitAction R)) (htrace : es = prefixEvents ++ suffixEvents)
    (g : CellConfig R) (hg : CellExec f prefixEvents g) :
    cellSpace g ≤ cellSpace f + es.length := by
  have h := cellExec_space hg
  have hlen : prefixEvents.length ≤ es.length := by rw [htrace, List.length_append]; omega
  omega

/-- The default head of a dropped list equals lookup at the drop offset with the same default. -/
theorem headD_drop_getD (bits : List Bool) (c : ℕ) :
    (bits.drop c).headD false = bits.getD c false := by
  induction c generalizing bits with
  | zero => cases bits <;> rfl
  | succ c _ => cases bits <;> simp [List.drop, List.getD]

/-- A scan trace starting at head position `c` returns to `c` and pushes the bit at offset `k`
of the remaining input onto the stack. -/
theorem scanTrace_cellExec {R : ℕ} (f : CellConfig R) (k c : ℕ) :
    CellExec { f with head := c } (scanTrace (R := R) (f.input.drop c) k)
      { f with head := c, stack := scanBit (f.input.drop c) k :: f.stack } := by
  induction k generalizing c with
  | zero =>
    simp only [scanTrace, scanBit, headD_drop_getD]
    exact CellExec.single (.read _)
  | succ k ih =>
    have hmid := ih (c + 1)
    have hstart : CellStep { f with head := c } .right { f with head := c + 1 } := .right _
    have hend : CellStep
        { f with head := c + 1, stack := scanBit (f.input.drop (c + 1)) k :: f.stack } .left
        { f with head := c, stack := scanBit (f.input.drop (c + 1)) k :: f.stack } := by
      simpa only [Nat.add_sub_cancel_right] using! CellStep.left
        { f with head := c + 1, stack := scanBit (f.input.drop (c + 1)) k :: f.stack }
    have hall := CellExec.trans (CellExec.cons hstart hmid) (CellExec.single hend)
    simpa only [scanTrace, scanBit, List.tail_drop, List.cons_append] using! hall

/-- An expression trace starting at head position zero returns there and pushes the evaluated
Boolean value onto the stack. -/
theorem exprTrace_cellExec {R : ℕ} (e : BitExpr R) (f : CellConfig R) :
    CellExec { f with head := 0 } (e.eventTrace f.input f.regs)
      { f with head := 0, stack := e.eval f.input f.regs :: f.stack } := by
  induction e generalizing f with
  | literal b => exact CellExec.single (.literal _ b)
  | reg i => exact CellExec.single (.reg _ i)
  | input k =>
    simpa only [List.drop_zero, BitExpr.eventTrace, BitExpr.eval] using! scanTrace_cellExec f k 0
  | bnot a ih =>
    have ha := ih f
    have hop : CellStep { f with head := 0, stack := a.eval f.input f.regs :: f.stack }
        (.bnot (a.eval f.input f.regs))
        { f with head := 0, stack := (!(a.eval f.input f.regs)) :: f.stack } :=
      .bnot { f with head := 0 } _ _
    exact ha.trans (CellExec.single hop)
  | band a b iha ihb =>
    have ha := iha f
    have hb := ihb { f with stack := a.eval f.input f.regs :: f.stack }
    have hop : CellStep
        { f with head := 0, stack := b.eval f.input f.regs :: a.eval f.input f.regs :: f.stack }
        (.band (a.eval f.input f.regs) (b.eval f.input f.regs))
        { f with head := 0, stack := (a.eval f.input f.regs && b.eval f.input f.regs) :: f.stack } :=
      .band { f with head := 0 } _ _ _
    simpa only [BitExpr.eventTrace, BitExpr.eval, List.append_assoc] using!
      ha.trans (hb.trans (CellExec.single hop))
  | bxor a b iha ihb =>
    have ha := iha f
    have hb := ihb { f with stack := a.eval f.input f.regs :: f.stack }
    have hop : CellStep
        { f with head := 0, stack := b.eval f.input f.regs :: a.eval f.input f.regs :: f.stack }
        (.bxor (a.eval f.input f.regs) (b.eval f.input f.regs))
        { f with head := 0, stack := xor (a.eval f.input f.regs) (b.eval f.input f.regs) :: f.stack } :=
      .bxor { f with head := 0 } _ _ _
    simpa only [BitExpr.eventTrace, BitExpr.eval, List.append_assoc] using!
      ha.trans (hb.trans (CellExec.single hop))

/-- Embed a bit-instruction frame into a cell configuration with head position zero and a
specified evaluation stack. -/
def cellOfFrame {R : ℕ} (f : BitFrame R) (stack : List Bool) : CellConfig R :=
  ⟨f.input, f.regs, f.output, 0, stack⟩

/-- The trace of one bit instruction executes between its embedded initial and final frames
while preserving the supplied stack. -/
theorem bitStepTrace_cellExec {R : ℕ} (i : BitInstr R) (f : BitFrame R) (stack : List Bool) :
    CellExec (cellOfFrame f stack) (bitStepTrace i f) (cellOfFrame (bitStep i f) stack) := by
  cases i with
  | assign k e =>
    have he := exprTrace_cellExec e (cellOfFrame f stack)
    have hs :=
        CellExec.single (CellStep.store (cellOfFrame f stack) k (e.eval f.input f.regs) stack)
    exact he.trans hs
  | emit e =>
    have he := exprTrace_cellExec e (cellOfFrame f stack)
    have hs : CellExec
        { cellOfFrame f stack with stack := e.eval f.input f.regs :: stack }
        [.outputLeft, .writeOutput (e.eval f.input f.regs)]
        { cellOfFrame f stack with output := e.eval f.input f.regs :: f.output } :=
      .cons (.outputLeft _) (CellExec.single (.outputWrite (cellOfFrame f stack)
        (e.eval f.input f.regs) false stack f.output))
    exact he.trans hs

/-- The trace of a bit code block executes between its embedded initial and final frames while
preserving the supplied stack. -/
theorem bitRunTrace_cellExec {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) (stack : List Bool) :
    CellExec (cellOfFrame f stack) (bitRunTrace code f) (cellOfFrame (bitRun code f) stack) := by
  induction code generalizing f with
  | nil => exact .nil _
  | cons i code ih =>
    change CellExec _ (bitStepTrace i f ++ bitRunTrace code (bitStep i f))
      (cellOfFrame (bitRun code (bitStep i f)) stack)
    exact (bitStepTrace_cellExec i f stack).trans (ih (bitStep i f))

/-- Every executable prefix of a bit block trace has cell space bounded by the register count,
initial output and stack lengths, and the full trace length. -/
theorem bitRun_all_prefix_space {R : ℕ} (code : List (BitInstr R)) (f : BitFrame R) (stack : List Bool)
    (prefixEvents suffixEvents : List (BitAction R))
    (htrace : bitRunTrace code f = prefixEvents ++ suffixEvents) (g : CellConfig R)
    (hg : CellExec (cellOfFrame f stack) prefixEvents g) :
    cellSpace g ≤ R + f.output.length + stack.length + (bitRunTrace code f).length := by
  have h := cellExec_prefix_space (cellOfFrame f stack) (bitRunTrace code f)
    prefixEvents suffixEvents htrace g hg
  simpa only [cellSpace, cellOfFrame, Nat.add_zero] using! h

/-- Every executable prefix of measured tableau code has cell space bounded by eight registers,
the initial output and stack lengths, and `measureBudget n m`. -/
theorem measuredTableauCode_prefix_space {n m : ℕ} (a : Fin m) (f : BitFrame 8) (stack : List Bool)
    (prefixEvents suffixEvents : List (BitAction 8))
    (htrace : bitRunTrace (measuredTableauCode (n := n) a) f = prefixEvents ++ suffixEvents)
    (g : CellConfig 8) (hg : CellExec (cellOfFrame f stack) prefixEvents g) :
    cellSpace g ≤ 8 + f.output.length + stack.length + measureBudget n m := by
  have hp := bitRun_all_prefix_space (measuredTableauCode (n := n) a) f stack _ _ htrace g hg
  have ht := measuredTableauCode_time (n := n) a f
  change _ ≤ measureBudget n m at ht
  omega

/-- The selectable input sources of the live simulator: tableau, operand, and work bits. -/
inductive InputPort where
  | table | operand | work

/-- A live simulator configuration with program control, pending branches, input buffers, random
tape, outcome record, and cell-machine state. -/
structure LiveConfig (n m : ℕ) where
  control : RawProgram n m
  branches : Option (RawProgram n m × RawProgram n m)
  operand : List Bool
  table : List Bool
  work : List Bool
  output : List Bool
  tape : List Bool
  outcomes : List Bool
  regs : BitBank 8
  head : ℕ
  stack : List Bool
  port : InputPort

/-- Select the live input bit list according to the configuration's active input port. -/
def liveInput {n m : ℕ} (f : LiveConfig n m) : List Bool :=
  match f.port with
  | .table => f.table
  | .operand => f.operand
  | .work => f.work

/-- Extract the cell-machine configuration from the selected live input and mutable cell state. -/
def liveCell {n m : ℕ} (f : LiveConfig n m) : CellConfig 8 :=
  ⟨liveInput f, f.regs, f.output, f.head, f.stack⟩

/-- Restore registers, output, head position, and stack from a cell configuration into a live
configuration. -/
def liveRestore {n m : ℕ} (f : LiveConfig n m) (c : CellConfig 8) : LiveConfig n m :=
  { f with regs := c.regs, output := c.output, head := c.head, stack := c.stack }

/-- Embed a raw state into a live configuration with specified program and operand, empty work
buffers, and the tableau input selected. -/
def liveOfRaw {n m : ℕ} (program : RawProgram n m) (s : RawState) (operand : List Bool) : LiveConfig n m :=
  ⟨program, none, operand, s.bits, [], [], s.tape, s.outcomes, s.regs, 0, [], .table⟩

/-- The single-event live simulator transition relation implementing raw control events and
embedded cell-machine steps. -/
inductive LiveStep {n m : ℕ} : LiveConfig n m → RunAction → LiveConfig n m → Prop where
  | bit (f : LiveConfig n m) (c e) : CellStep (liveCell f) e c →
      LiveStep f (.bit e) (liveRestore f c)
  | prepareBit (f : LiveConfig n m) (c e) : CellStep (liveCell f) e c →
      LiveStep f (.prepare (.bit e)) (liveRestore f c)
  | enterGate (f : LiveConfig n m) (g next) :
      LiveStep { f with control := .gate g next } .enterGate { f with control := next }
  | enterRandom (f : LiveConfig n m) (a operand onFalse onTrue) :
      LiveStep { f with control := .random a operand onFalse onTrue } .enterRandom
        { f with control := .halt, branches := some (onFalse,onTrue), operand := operand }
  | enterDeterministic (f : LiveConfig n m) (b next) :
      LiveStep { f with control := .deterministic b next } .enterDeterministic
        { f with control := .deterministic b next }
  | selectTableau (f : LiveConfig n m) : LiveStep f .selectTableau
      { f with port := .table, work := [], output := [], head := 0 }
  | selectOperand (f : LiveConfig n m) : LiveStep f (.prepare .selectOperand)
      { f with port := .operand, work := [], output := [], head := 0 }
  | prepareTableau (f : LiveConfig n m) : LiveStep f (.prepare .selectTableau)
      { f with port := .table, head := 0 }
  | selectWork (f : LiveConfig n m) : LiveStep f .selectWork
      { f with port := .work, work := f.output, output := [], head := 0 }
  | swapOutput (f : LiveConfig n m) : LiveStep f .swapOutput
      { f with table := f.output, work := [], output := [], head := 0, port := .table }
  | readFair (f : LiveConfig n m) (b rest) :
      LiveStep { f with tape := b :: rest } (.readFair b)
        { f with tape := rest, stack := b :: f.stack }
  | storeOutcome (f : LiveConfig n m) (b bs) :
      LiveStep { f with stack := b :: bs } (.storeOutcome b)
        { f with stack := b :: bs, regs := bankWrite f.regs 7 b }
  | literalOutcome (f : LiveConfig n m) (b next) :
      LiveStep { f with control := .deterministic b next } (.literalOutcome b)
        { f with control := next, stack := b :: f.stack }
  | recordLeft (f : LiveConfig n m) : LiveStep f .recordLeft
      { f with outcomes := false :: f.outcomes }
  | recordWrite (f : LiveConfig n m) (b old bs out) :
      LiveStep { f with stack := b :: bs, outcomes := old :: out } (.recordWrite b)
        { f with stack := bs, outcomes := b :: out }
  | branch (f : LiveConfig n m) (b onFalse onTrue) : bankRead f.regs 7 = b →
      LiveStep { f with branches := some (onFalse,onTrue) } (.branch b)
        { f with control := if b then onTrue else onFalse, branches := none }
  | halt (f : LiveConfig n m) : LiveStep { f with control := .halt } .halt { f with control := .halt }

/-- The finite-trace execution relation generated by live simulator steps. -/
inductive LiveExec {n m : ℕ} : LiveConfig n m → List RunAction → LiveConfig n m → Prop where
  | nil (f) : LiveExec f [] f
  | cons {f g h e es} : LiveStep f e g → LiveExec g es h → LiveExec f (e :: es) h

/-- A live simulator step gives an execution of its singleton event trace. -/
theorem LiveExec.single {n m : ℕ} {f g : LiveConfig n m} {e : RunAction} (h : LiveStep f e g) :
    LiveExec f [e] g := .cons h (.nil _)

/-- Live simulator executions compose by concatenating their traces. -/
theorem LiveExec.trans {n m : ℕ} {f g h : LiveConfig n m} {xs ys : List RunAction}
    (hx : LiveExec f xs g) (hy : LiveExec g ys h) : LiveExec f (xs ++ ys) h := by
  induction hx with
  | nil => exact hy
  | cons he _ ih => exact .cons he (ih hy)

/-- The live bit-space measure summing tableau, work, and outcome lengths with the embedded
cell-space measure. -/
def liveBitSpace {n m : ℕ} (f : LiveConfig n m) : ℕ :=
  f.table.length + f.work.length + f.outcomes.length + cellSpace (liveCell f)

/-- One live simulator event increases `liveBitSpace` by at most one. -/
theorem liveStep_space {n m : ℕ} {f g : LiveConfig n m} {e : RunAction} (h : LiveStep f e g) :
    liveBitSpace g ≤ liveBitSpace f + 1 := by
  cases h with
  | bit f c e hh | prepareBit f c e hh =>
    have hc := cellStep_space hh
    change f.table.length + f.work.length + f.outcomes.length + cellSpace c ≤
      f.table.length + f.work.length + f.outcomes.length + cellSpace (liveCell f) + 1
    omega
  | _ => simp only [liveBitSpace, liveCell, cellSpace, List.length_cons, List.length_nil]; omega

/-- A live simulator execution increases `liveBitSpace` by at most its trace length. -/
theorem liveExec_space {n m : ℕ} {f g : LiveConfig n m} {es : List RunAction} (h : LiveExec f es g) :
    liveBitSpace g ≤ liveBitSpace f + es.length := by
  induction h with
  | nil => simp
  | @cons f g h e es hs _ ih =>
    have hh := liveStep_space hs
    simp only [List.length_cons]
    omega

/-- The live bit space reached after any executable trace prefix is bounded by the initial space
plus the full trace length. -/
theorem liveExec_prefix_space {n m : ℕ} (f : LiveConfig n m) (es pre suf : List RunAction)
    (htrace : es = pre ++ suf) (g : LiveConfig n m) (hg : LiveExec f pre g) :
    liveBitSpace g ≤ liveBitSpace f + es.length := by
  have h := liveExec_space hg
  have hlen : pre.length ≤ es.length := by rw [htrace, List.length_append]; omega
  omega

/-- A cell-machine step preserves its input list. -/
theorem cellStep_input {R : ℕ} {f g : CellConfig R} {e : BitAction R} (h : CellStep f e g) :
    g.input = f.input := by cases h <;> rfl

/-- Restoring the cell configuration extracted from a live configuration leaves it unchanged. -/
theorem liveRestore_cell {n m : ℕ} (f : LiveConfig n m) : liveRestore f (liveCell f) = f := by
  cases f
  rfl

/-- Extracting a restored cell configuration recovers it when its input agrees with the selected
live input. -/
theorem liveCell_restore {n m : ℕ} (f : LiveConfig n m) (c : CellConfig 8)
    (hi : c.input = liveInput f) : liveCell (liveRestore f c) = c := by
  cases c with
  | mk input regs output head stack =>
    change input = liveInput f at hi
    change CellConfig.mk
        (liveInput f) regs output head stack = CellConfig.mk input regs output head stack
    rw [hi]

/-- Successive cell restorations retain only the mutable cell state from the final restoration. -/
theorem liveRestore_twice {n m : ℕ} (f : LiveConfig n m) (c d : CellConfig 8) :
    liveRestore (liveRestore f c) d = liveRestore f d := rfl

/-- A wrapper that lifts individual cell steps also lifts an entire cell execution to a live
execution of the mapped trace. -/
theorem liveLift {n m : ℕ} (wrap : BitAction 8 → RunAction)
    (hw : ∀ (f : LiveConfig n m) (c : CellConfig 8) (e : BitAction 8),
      CellStep (liveCell f) e c → LiveStep f (wrap e) (liveRestore f c))
    {c d : CellConfig 8} {es : List (BitAction 8)} (h : CellExec c es d) :
    ∀ f : LiveConfig n m, liveCell f = c → LiveExec f (es.map wrap) (liveRestore f d) := by
  induction h with
  | nil c =>
    intro f hf
    rw [← hf, liveRestore_cell]
    exact .nil _
  | @cons c g d e es hs _ ih =>
    intro f hf
    have hs' : CellStep (liveCell f) e g := by rw [hf]; exact hs
    have hi : g.input = liveInput f := cellStep_input hs'
    have htail := ih (liveRestore f g) (liveCell_restore f g hi)
    simpa only [List.map_cons, liveRestore_twice] using! LiveExec.cons (hw f g e hs') htail

/-- Under a compatible event wrapper, a bit block trace lifts to a live execution that restores
the computed frame and preserves the supplied stack. -/
theorem liveBlock {n m : ℕ} (wrap : BitAction 8 → RunAction)
    (hw : ∀ (f : LiveConfig n m) (c : CellConfig 8) (e : BitAction 8),
      CellStep (liveCell f) e c → LiveStep f (wrap e) (liveRestore f c))
    (f : LiveConfig n m) (code : List (BitInstr 8)) (frame : BitFrame 8) (stack : List Bool)
    (hf : liveCell f = cellOfFrame frame stack) :
    LiveExec f ((bitRunTrace code frame).map wrap) (liveRestore f (cellOfFrame (bitRun code frame) stack)) :=
  liveLift wrap hw (bitRunTrace_cellExec code frame stack) f hf

/-- A raw gate trace executes in the live simulator from the gate control state to the embedded
raw gate result. -/
theorem rawGateTrace_liveExec {n m : ℕ} (r : RawState) (g : CliffordGate n)
    (next : RawProgram n m) (operand : List Bool) :
    LiveExec (liveOfRaw (.gate g next) r operand) (rawGateTrace (m := m) r g)
      (liveOfRaw next (rawGateStep (m := m) r g) operand) := by
  let f := liveOfRaw next r operand
  have h1 : LiveStep (liveOfRaw (.gate g next) r operand) .enterGate f := .enterGate f g next
  have h2 := LiveStep.selectTableau f
  let f2 := { f with port := InputPort.table, work := [], output := [], head := 0 }
  have hv : liveCell f2 = cellOfFrame (rawGateFrame r) [] := rfl
  have hb := liveBlock RunAction.bit (fun f c e h => LiveStep.bit f c e h)
    f2 (gateTableauCode (m := m) g) (rawGateFrame r) [] hv
  have hend := LiveExec.single (LiveStep.swapOutput (liveRestore f2
    (cellOfFrame (bitRun (gateTableauCode (m := m) g) (rawGateFrame r)) [])))
  have hprefix : LiveExec (liveOfRaw (.gate g next) r operand) [.enterGate, .selectTableau] f2 :=
    .cons h1 (.cons h2 (.nil _))
  simpa only [rawGateTrace, List.append_assoc] using! hprefix.trans (hb.trans hend)

/-- A raw deterministic trace executes in the live simulator, recording its outcome and
advancing to the continuation. -/
theorem rawDeterministicTrace_liveExec {n m : ℕ} (r : RawState) (b : Bool)
    (next : RawProgram n m) (operand : List Bool) :
    LiveExec (liveOfRaw (.deterministic b next) r operand) (rawDeterministicTrace b)
      (liveOfRaw next (rawDeterministicStep r b) operand) := by
  let f := liveOfRaw next r operand
  exact .cons (.enterDeterministic f b next) (.cons (.literalOutcome f b next)
    (.cons (.recordLeft { f with stack := [b] })
      (.cons (.recordWrite f b false [] r.outcomes) (.nil _))))

/-- Input-copying code preserves the register bank. -/
theorem copyCode_regs (size : ℕ) (f : BitFrame 8) : (bitRun (copyCode size) f).regs = f.regs :=
  (emitCode_correct _ _).2.1

/-- Measured tableau code preserves the outcome register seven. -/
theorem measuredTableauCode_register7 {n m : ℕ} (a : Fin m) (f : BitFrame 8) :
    bankRead (bitRun (measuredTableauCode (n := n) a) f).regs 7 = bankRead f.regs 7 :=
  rowBlocks_register7 (List.ofFn id) (measuredRowCode (n := n) a)
    (fun i _ g => measuredRowCode_register7 a i g) f

/-- With the specified fair bit at the head of the tape, a raw random trace executes in the live
simulator and advances to the corresponding branch with the updated raw state. -/
theorem rawRandomTrace_liveExec {n m : ℕ} (r : RawState) (a : Fin m) (operand : List Bool)
    (b : Bool) (rest : List Bool) (hrt : r.tape = b :: rest)
    (onFalse onTrue : RawProgram n m) (oldOperand : List Bool) :
    LiveExec (liveOfRaw (.random a operand onFalse onTrue) r oldOperand)
      (rawRandomTrace (n := n) r a operand b)
      (liveOfRaw (if b then onTrue else onFalse) (rawRandomStep (n := n) r a operand b rest) operand) := by
  let f :=
      { liveOfRaw (RawProgram.halt : RawProgram n m) r operand with branches := some (onFalse,onTrue) }
  let fr := { f with tape := rest }
  let regs := bankWrite r.regs 7 b
  let f3 := { fr with stack := [b], regs := regs }
  have h1 : LiveStep (liveOfRaw (.random a operand onFalse onTrue) r oldOperand) .enterRandom f :=
    .enterRandom (liveOfRaw .halt r oldOperand) a operand onFalse onTrue
  have h2 : LiveStep f (.readFair b) { fr with stack := [b] } := by
    simpa only [f, fr, liveOfRaw, hrt] using! LiveStep.readFair f b rest
  have h3 : LiveStep { fr with stack := [b] } (.storeOutcome b) f3 :=
    .storeOutcome fr b []
  have hp : LiveExec (liveOfRaw (.random a operand onFalse onTrue) r oldOperand)
      [.enterRandom,.readFair b,.storeOutcome b] f3 := .cons h1 (.cons h2 (.cons h3 (.nil _)))
  let f4 := { f3 with port := InputPort.operand, work := [], output := [], head := 0 }
  let opFrame := operandCopyFrame operand regs
  have hv4 : liveCell f4 = cellOfFrame opFrame [b] := rfl
  have hop := liveBlock (fun e => RunAction.prepare (.bit e))
    (fun f c e h => LiveStep.prepareBit f c e h) f4 (copyCode operand.length) opFrame [b] hv4
  let f5 := liveRestore f4 (cellOfFrame (bitRun (copyCode operand.length) opFrame) [b])
  let f6 := { f5 with port := InputPort.table, head := 0 }
  let tableFrame := tableauCopyFrame r.bits operand regs
  have hv6 : liveCell f6 = cellOfFrame tableFrame [b] := by
    change CellConfig.mk r.bits (bitRun (copyCode operand.length) opFrame).regs
      (bitRun (copyCode operand.length) opFrame).output 0 [b] =
      CellConfig.mk r.bits regs (bitRun (copyCode operand.length) opFrame).output 0 [b]
    rw [copyCode_regs]
    rfl
  have htable := liveBlock (fun e => RunAction.prepare (.bit e))
    (fun f c e h => LiveStep.prepareBit f c e h) f6 (copyCode r.bits.length) tableFrame [b] hv6
  let f7 := liveRestore f6 (cellOfFrame (bitRun (copyCode r.bits.length) tableFrame) [b])
  have hprep := (LiveExec.single (LiveStep.selectOperand f3)).trans
    (hop.trans ((LiveExec.single (LiveStep.prepareTableau f5)).trans htable))
  let f8 := { f7 with port := InputPort.work, work := f7.output, output := [], head := 0 }
  let measureFrame := rawMeasureFrame r operand b
  have hv8 : liveCell f8 = cellOfFrame measureFrame [b] := by
    change CellConfig.mk (prepareInput r.bits operand regs)
      (bitRun (copyCode r.bits.length) tableFrame).regs [] 0 [b] =
      CellConfig.mk (prepareInput r.bits operand regs) regs [] 0 [b]
    rw [copyCode_regs]
    rfl
  have hmeasure := liveBlock RunAction.bit (fun f c e h => LiveStep.bit f c e h)
    f8 (measuredTableauCode (n := n) a) measureFrame [b] hv8
  let f9 := liveRestore f8 (cellOfFrame (bitRun (measuredTableauCode (n := n) a) measureFrame) [b])
  let f11 := { f9 with stack := [], outcomes := b :: r.outcomes }
  have hw : LiveStep { f9 with outcomes := false :: f9.outcomes } (.recordWrite b) f11 :=
    .recordWrite { f9 with stack := [], outcomes := r.outcomes } b false [] r.outcomes
  have hbank : bankRead f11.regs 7 = b := by
    change bankRead (bitRun (measuredTableauCode (n := n) a) measureFrame).regs 7 = b
    rw [measuredTableauCode_register7]
    simp [measureFrame, rawMeasureFrame]
  let f12 := { f11 with control := if b then onTrue else onFalse, branches := none }
  have hb : LiveStep f11 (.branch b) f12 := LiveStep.branch f11 b onFalse onTrue hbank
  have hend := LiveExec.cons (LiveStep.recordLeft f9)
    (LiveExec.cons hw (LiveExec.cons hb (LiveExec.single (LiveStep.swapOutput f12))))
  have hall :=
      hp.trans (hprep.trans ((LiveExec.single (LiveStep.selectWork f7)).trans (hmeasure.trans hend)))
  simpa only [rawRandomTrace, prepareTrace, List.map_cons, List.map_append, List.map_map,
    Function.comp_def, List.append_assoc, List.cons_append, List.nil_append] using! hall

/-- Every successful raw execution has a live execution of the same trace ending in the embedded
final raw state with halted control. -/
theorem rawRun_liveExec {n m : ℕ} (program : RawProgram n m) :
    ∀ (r : RawState) (rr : RawResult) (oldOperand : List Bool), rawRun program r = some rr →
      ∃ operand, LiveExec (liveOfRaw program r oldOperand) rr.trace (liveOfRaw .halt rr.state operand) := by
  induction program with
  | halt =>
    intro r rr oldOperand hr
    cases hr
    exact ⟨oldOperand, LiveExec.single (LiveStep.halt (liveOfRaw .halt r oldOperand))⟩
  | gate g next ih =>
    intro r rr oldOperand hr
    have hr' : (rawRun next (rawGateStep (m := m) r g)).map
        (RawResult.prepend (rawGateTrace (m := m) r g)) = some rr := hr
    obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
    subst rr
    obtain ⟨operand, hrec⟩ := ih _ rr' oldOperand hn
    exact ⟨operand, (rawGateTrace_liveExec r g next oldOperand).trans hrec⟩
  | random a operand onFalse onTrue ihFalse ihTrue =>
    intro r rr oldOperand hr
    cases ht : r.tape with
    | nil => simp [rawRun, ht] at hr
    | cons b rest =>
      cases b with
      | false =>
        have hr' : (rawRun onFalse (rawRandomStep (n := n) r a operand false rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) r a operand false)) = some rr := by
          simpa only [rawRun, ht] using! hr
        obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
        subst rr
        obtain ⟨finalOperand, hrec⟩ := ihFalse _ rr' operand hn
        have hs := rawRandomTrace_liveExec r a operand false rest ht onFalse onTrue oldOperand
        exact ⟨finalOperand, hs.trans hrec⟩
      | true =>
        have hr' : (rawRun onTrue (rawRandomStep (n := n) r a operand true rest)).map
            (RawResult.prepend (rawRandomTrace (n := n) r a operand true)) = some rr := by
          simpa only [rawRun, ht] using! hr
        obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
        subst rr
        obtain ⟨finalOperand, hrec⟩ := ihTrue _ rr' operand hn
        have hs := rawRandomTrace_liveExec r a operand true rest ht onFalse onTrue oldOperand
        exact ⟨finalOperand, hs.trans hrec⟩
  | deterministic b next ih =>
    intro r rr oldOperand hr
    have hr' : (rawRun next (rawDeterministicStep r b)).map
        (RawResult.prepend (rawDeterministicTrace b)) = some rr := hr
    obtain ⟨rr', hn, hrr⟩ := Option.map_eq_some_iff.mp hr'
    subst rr
    obtain ⟨operand, hrec⟩ := ih _ rr' oldOperand hn
    exact ⟨operand, (rawDeterministicTrace_liveExec r b next oldOperand).trans hrec⟩

/-- The live bit space of an embedded raw state is its tableau bit length plus its outcome count
and eight registers. -/
theorem liveOfRaw_space {n m : ℕ} (p : RawProgram n m) (r : RawState) (operand : List Bool) :
    liveBitSpace (liveOfRaw p r operand) = r.bits.length + r.outcomes.length + 8 := by
  simp [liveBitSpace, liveOfRaw, liveCell, cellSpace]

/-- A valid program with sufficient tape and `m ≤ n` has matching raw, physical, and live
executions satisfying the stated state, probability, tape, and trace guarantees. Every
executable prefix of the live trace also satisfies the explicit bit-space bound. -/
theorem rawFrontier {n m : ℕ} (program : Program n m) (t : Tableau n m) (tape : List Bool)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) (hm : m ≤ n)
    (hv : Program.Valid t program) (ht : Qatlib.Concepts.PauliClifford.PauliAlgebra.ConsistentTableau t)
    (hn : Qatlib.Foundations.PureStateMath.Normalized ψ) (hψ : ψ ∈ codeSpace t)
    (hbudget : program.maxFairBits ≤ tape.length) :
    ∃ rr pr operand,
      rawRun (encodeProgram program) (rawInitial (tableauBits t) tape) = some rr ∧
      physicalExecute program (initial t tape) ψ = some pr ∧ RepresentsMachine rr.state pr.machine ∧
      Qatlib.Foundations.PureStateMath.Normalized pr.state ∧ pr.state ∈ codeSpace pr.machine.tableau ∧
      pr.jointMass = (1 / 2 : ℝ) ^ fairReads rr.trace ∧
      fairReads rr.trace + rr.state.tape.length = tape.length ∧
      rr.trace.length ≤ 1 + program.maxSteps * rawStepBound n n ∧
      LiveExec (liveOfRaw (encodeProgram program) (rawInitial (tableauBits t) tape) []) rr.trace
        (liveOfRaw .halt rr.state operand) ∧
      ∀ pre suf cfg, rr.trace = pre ++ suf →
        LiveExec (liveOfRaw (encodeProgram program) (rawInitial (tableauBits t) tape) []) pre cfg →
        liveBitSpace cfg ≤ m * rowWidth n + 8 + 1 + program.maxSteps * rawStepBound n n := by
  obtain ⟨rr, pr, hr, hp, hrep, hnorm, hcode, hmass, hfair, htime⟩ :=
    rawPhysicalTime program t tape ψ hm hv ht hn hψ hbudget
  obtain ⟨operand, hframes⟩ := rawRun_liveExec _ _ _ [] hr
  refine ⟨rr, pr, operand, hr, hp, hrep, hnorm, hcode, hmass, hfair, htime, hframes, ?_⟩
  intro pre suf cfg htr hcfg
  have h := liveExec_prefix_space _ rr.trace pre suf htr cfg hcfg
  have hinit : liveBitSpace (liveOfRaw (encodeProgram program) (rawInitial (tableauBits t) tape) []) =
      m * rowWidth n + 8 := by
    rw [liveOfRaw_space]
    simp only [rawInitial, List.length_nil, Nat.add_zero, tableau_bits_length]
    rfl
  rw [hinit] at h
  omega

end Qatlib.Concepts.CliffordTheory.TableauSim.BitExecution
