/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3BoundarySubgoal
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Concepts.LchsSimulation.StaticLchs.ReadoutError

/-!
# Prepared Grover search from the zero register

`PreparedGroverCircuit` prepares the uniform state with `HadamardN` before running the Grover
iterations. This module proves its exact query, macro-gate, and depth counts, its known-count
success guarantee, and a probability error bound for a perturbed unitary oracle.

For the mathematical background, see [Grover1997].

## Main statements

* `preparedGrover_knownCount_query_upper`: For a positive marked count at most half the register
  size, the prescribed iteration count is a fixed-space query upper bound with success at least
  1/2.

## References

* [Grover, 1997][Grover1997]
-/

set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Concepts.SearchStopping.KnownCount

/-- A query-free unitary preparation of the uniform n-qubit state from `ZeroStr n` using
`HadamardN n`. -/
noncomputable def groverPrepare (n : ℕ) : HasPrepare (Uniform (Reg n)) (ZeroStr n) where
  prep := [Step.gate (HadamardN n)]
  unitary :=
    (isUnitaryCircuit_gate _ _).mpr ⟨hadamardN_unitary n, isUnitaryCircuit_nil⟩
  query_free := rfl
  produces := by
    simp only [run_gate, run_nil, applyGate_hadamardN_ket_zero]

/-- The circuit consisting of one n-qubit Hadamard gate followed by j Grover iterations. -/
noncomputable def PreparedGroverCircuit (n j : ℕ) : Circuit (Reg n) :=
  Step.gate (HadamardN n) :: GroverCircuit (Reg n) j

/-- Running the prepared circuit from the zero basis state with `SetOracle A` produces
`GroverState A j`. -/
theorem run_preparedGroverCircuit (n j : ℕ) (A : Finset (Reg n)) :
    Run (SetOracle A) (PreparedGroverCircuit n j) (Ket (ZeroStr n)) =
      GroverState A j := by
  rw [PreparedGroverCircuit,
    show Step.gate (HadamardN n) :: GroverCircuit (Reg n) j
      = (groverPrepare n).prep ++ GroverCircuit (Reg n) j from rfl,
    run_append, (groverPrepare n).run_oracle (SetOracle A)]
  rfl

/-- The prepared Grover circuit uses exactly j oracle queries. -/
theorem queryCount_preparedGroverCircuit (n j : ℕ) :
    QueryCount (PreparedGroverCircuit n j) = j := by
  simp only [PreparedGroverCircuit, queryCount_gate, queryCount_groverCircuit]

/-- The prepared Grover circuit contains exactly j + 1 macro gates. -/
theorem gateCount_preparedGroverCircuit (n j : ℕ) :
    GateCount (PreparedGroverCircuit n j) = j + 1 := by
  simp [PreparedGroverCircuit, GroverCircuit, gateCount_repeatCircuit, GroverStep]

/-- The prepared Grover circuit has size 2j + 1. -/
theorem size_preparedGroverCircuit (n j : ℕ) :
    Size (PreparedGroverCircuit n j) = 2 * j + 1 := by
  have hprep : (derive (fun _ : Matrix (Reg n) (Reg n) ℂ => StepProfile.zero)
      (groverPrepare n).prep).depth = 1 := rfl
  have hg2 : Size (GroverStep (Reg n)) = 2 := rfl
  have hgrover : (derive (fun _ : Matrix (Reg n) (Reg n) ℂ => StepProfile.zero)
      (GroverCircuit (Reg n) j)).depth = 2 * j := by
    rw [show GroverCircuit (Reg n) j = RepeatCircuit (GroverStep (Reg n)) j from rfl,
      derive_repeatCircuit, repeatCost_depth, derive_depth, hg2, Nat.mul_comm]
  rw [← derive_depth
      (fun _ : Matrix (Reg n) (Reg n) ℂ => StepProfile.zero)
      (PreparedGroverCircuit n j),
    show PreparedGroverCircuit n j
      = (groverPrepare n).prep ++ GroverCircuit (Reg n) j from rfl,
    derive_append, ResourceCost.add_depth, hprep, hgrover]
  omega

/-- For any gate profile assignment, the derived resource cost has j queries, j + 1 macro gates,
and depth 2j + 1. -/
theorem resourceCost_preparedGroverCircuit (n j : ℕ)
    (κ : Matrix (Reg n) (Reg n) ℂ → StepProfile) :
    (derive κ (PreparedGroverCircuit n j)).queries = j ∧
      (derive κ (PreparedGroverCircuit n j)).macroGates = j + 1 ∧
      (derive κ (PreparedGroverCircuit n j)).depth = 2 * j + 1 := by
  have hsplit : derive κ (PreparedGroverCircuit n j)
      = derive κ (groverPrepare n).prep + derive κ (GroverCircuit (Reg n) j) := by
    rw [show PreparedGroverCircuit n j
        = (groverPrepare n).prep ++ GroverCircuit (Reg n) j from rfl,
      derive_append]
  have hprepQueries : QueryCount (groverPrepare n).prep = 0 := (groverPrepare n).query_free
  have hgates : GateCount (GroverCircuit (Reg n) j) = j := by
    rw [show GroverCircuit (Reg n) j = RepeatCircuit (GroverStep (Reg n)) j from rfl,
      gateCount_repeatCircuit, show GateCount (GroverStep (Reg n)) = 1 from rfl]
    exact Nat.mul_one j
  constructor
  · rw [hsplit, ResourceCost.add_queries, derive_queries, derive_queries, hprepQueries,
      queryCount_groverCircuit]
    omega
  constructor
  · rw [hsplit, ResourceCost.add_macroGates, derive_macroGates, derive_macroGates, hgates]
    change 1 + j = j + 1
    omega
  · rw [derive_depth, size_preparedGroverCircuit]

/-- The unitary query algorithm using `PreparedGroverCircuit` with the zero-register basis state
as normalized input. -/
noncomputable def preparedGroverAlgorithm (n j : ℕ) : QueryAlgorithm (Reg n) where
  circuit := PreparedGroverCircuit n j
  start := Ket (ZeroStr n)
  unitary := (isUnitaryCircuit_gate _ _).mpr
    ⟨hadamardN_unitary n, isUnitaryCircuit_groverCircuit Fintype.card_pos j⟩
  normalized := normalized_ket _

/-- The output of the prepared Grover circuit under a set oracle is normalized. -/
theorem normalized_preparedGroverCircuit (n j : ℕ) (A : Finset (Reg n)) :
    Normalized (Run (SetOracle A) (PreparedGroverCircuit n j) (Ket (ZeroStr n))) :=
  (preparedGroverAlgorithm n j).normalized_output (setOracle_unitary A)

/-- When sin²(θ) is the marked fraction and both sin(θ) and cos(θ) are nonzero, prepared Grover
success after j iterations equals sin²((2j + 1)θ). -/
theorem measureProb_preparedGroverCircuit (n j : ℕ) (A : Finset (Reg n)) (θ : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / Fintype.card (Reg n))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    MeasureProb (Run (SetOracle A) (PreparedGroverCircuit n j) (Ket (ZeroStr n))) A =
      (Real.sin ((2 * j + 1) * θ)) ^ 2 := by
  rw [run_preparedGroverCircuit]
  exact measureProb_groverState Fintype.card_pos A θ hθ hs hc j

/-- For a positive marked count m below the register size N, the prescribed known-count
iteration choice gives prepared Grover success at least 1 − m/N. -/
theorem preparedGrover_knownCount_success (n : ℕ) (A : Finset (Reg n))
    {m : ℕ} (hA : A.card = m) (hm : 0 < m) (hmN : m < Fintype.card (Reg n)) :
    1 - (m : ℝ) / Fintype.card (Reg n) ≤
      MeasureProb (Run (SetOracle A)
        (PreparedGroverCircuit n (groverIterations
          (knownCountAngle ((m : ℝ) / Fintype.card (Reg n))))) (Ket (ZeroStr n))) A := by
  rw [run_preparedGroverCircuit]
  exact knownCount_success Fintype.card_pos A hA hm hmN

/-- For a positive marked count at most half the register size, the prescribed iteration count
is a fixed-space query upper bound with success at least 1/2. -/
theorem preparedGrover_knownCount_query_upper (n : ℕ) {m : ℕ}
    (hm : 0 < m) (hmN : 2 * m ≤ Fintype.card (Reg n)) :
    FixedSpaceQueryUpperBound
      (fun A : KnownMarkedSets (Reg n) m => SetOracle A.val) (fun A => A.val) (1 / 2)
      (groverIterations (knownCountAngle ((m : ℝ) / Fintype.card (Reg n)))) := by
  let j := groverIterations (knownCountAngle ((m : ℝ) / Fintype.card (Reg n)))
  let algorithm := preparedGroverAlgorithm n j
  have hcount : QueryCount algorithm.circuit ≤ j :=
    (queryCount_preparedGroverCircuit n j).le
  have hsolve : SolvesWithError
      (fun A : KnownMarkedSets (Reg n) m => SetOracle A.val) (fun A => A.val)
      algorithm.circuit algorithm.start (1 / 2) := by
    intro A
    change 1 - (1 / 2 : ℝ) ≤
      MeasureProb (Run (SetOracle A.val) (PreparedGroverCircuit n j) (Ket (ZeroStr n))) A.val
    rw [run_preparedGroverCircuit]
    have hsuccess := knownCount_success Fintype.card_pos A.val A.property hm (by omega)
    have hNr : (0 : ℝ) < Fintype.card (Reg n) := by positivity
    have hhalf : (m : ℝ) / Fintype.card (Reg n) ≤ 1 / 2 := by
      apply (div_le_iff₀ hNr).mpr
      have hmr : (2 : ℝ) * m ≤ Fintype.card (Reg n) := by exact_mod_cast hmN
      linarith
    dsimp [j]
    linarith
  exact algorithm.queryUpperBound (by norm_num)
    (fun A : KnownMarkedSets (Reg n) m => setOracle_unitary A.val) hcount hsolve

/-- A Grover circuit preserves normalization of a two-amplitude input whose marked and unmarked
squared masses sum to one. -/
theorem normalized_groverRun_of_markedMass {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (a b : ℂ) (j : ℕ)
    (hmass : (A.card : ℝ) * Complex.normSq a +
      ((Fintype.card I : ℝ) - A.card) * Complex.normSq b = 1) :
    Normalized (Run (SetOracle A) (GroverCircuit I j) (MarkedVector A a b)) :=
  (isUnitaryCircuit_groverCircuit hN j).normalized_run (setOracle_unitary A)
    ((normalized_markedVector_iff A a b).mpr hmass)

open scoped Matrix.Norms.L2Operator

/-- Replacing the set oracle by a unitary oracle within operator-norm distance δ changes the
prepared circuit's marked-set probability by at most 2jδ. -/
theorem measureProb_preparedGroverCircuit_oracle_error
    (n j : ℕ) (A : Finset (Reg n)) (P : Matrix (Reg n) (Reg n) ℂ) (δ : ℝ)
    (hP : P ∈ Matrix.unitaryGroup (Reg n) ℂ) (hδ : ‖SetOracle A - P‖ ≤ δ) :
    |MeasureProb (Run (SetOracle A) (PreparedGroverCircuit n j) (Ket (ZeroStr n))) A -
      MeasureProb (Run P (PreparedGroverCircuit n j) (Ket (ZeroStr n))) A| ≤
      2 * (j : ℝ) * δ := by
  have h := measureProb_run_sub_le_queryCount_of_le (SetOracle A) P
    (PreparedGroverCircuit n j) (Ket (ZeroStr n)) A δ (setOracle_unitary A) hP
    (preparedGroverAlgorithm n j).unitary (normalized_ket _) hδ
  simpa only [queryCount_preparedGroverCircuit] using h

end Qatlib.Concepts.SearchStopping.KnownCount
