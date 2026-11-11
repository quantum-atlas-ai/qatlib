/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ActualPhaseProgram

/-!
# Coherent lookup in read-only table memory

This module represents table records by `Memory` and constructs a coherent phase test using the
additive oracle, a table comparison, and the inverse oracle. The circuit `phaseWord` uses two
queries and restores the value register and table on clean inputs, as required by the algorithms
in [BrassardHoyerTapp1998Collision].

The compiler `compile` replaces abstract phase queries by these words. Its correctness, query
count, and unitarity are proved alongside finite memory dimension and record bounds.

## Main statements

* `phaseWord_clean`: On a zero value register and fixed table memory, the phase word implements
  the marked phase while restoring both auxiliary registers.
* `compile_queries`: Compilation uses exactly twice as many additive oracle queries as the
  original circuit has phase queries.
* `compile_run`: On clean auxiliary registers, the compiled circuit realizes the abstract table
  phase circuit and restores the value and memory registers [BrassardHoyerTapp1998Collision].
* `basis_card`: The basis cardinality of the search, value, and table registers is `(|X| * |R|)
  * (|S| * |R|)^k` [BrassardHoyerTapp1998Collision].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

namespace Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable
variable {S X R : Type} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- A table of `k` input-value records indexed by `Fin k`. -/
abbrev Memory (k : ℕ) := Fin k → X × R

/-- The finite set of values stored in the table memory. -/
def values {k : ℕ} (L : Memory (X := S) (R := R) k) : Finset R :=
  Finset.univ.image fun j => (L j).2

/-- The additive function oracle acting on the input-value registers and as the identity on
table memory. -/
def oracle (F : X → R) (k : ℕ) : Matrix ((X × R) × Memory (X := S) (R := R) k) ((X × R) × Memory (X := S) (R := R) k) ℂ :=
  TensorGate (AddOracle F) 1

/-- The diagonal phase comparison marking inputs outside `K` whose value register occurs in the
stored table values. -/
def comparison (K : Finset X) (k : ℕ) : Matrix ((X × R) × Memory (X := S) (R := R) k) ((X × R) × Memory (X := S) (R := R) k) ℂ :=
  Matrix.diagonal fun p => PhaseCompile.tableSign K (values p.2) p.1.1 p.1.2

omit [AddCommGroup R] in

/-- The diagonal table comparison is unitary. -/
theorem comparison_unitary (K : Finset X) (k : ℕ) :
    comparison (S := S) (R := R) K k ∈ Matrix.unitaryGroup ((X × R) × Memory (X := S) (R := R) k) ℂ := by
  rw [comparison, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases h : p.1.1 ∉ K ∧ p.1.2 ∈ values p.2 <;> simp [PhaseCompile.tableSign, h]
  · simp [hpq]

/-- The additive oracle extended by unchanged table memory is unitary. -/
theorem oracle_unitary (F : X → R) (k : ℕ) :
    oracle F k ∈ Matrix.unitaryGroup ((X × R) × Memory (X := S) (R := R) k) ℂ :=
  tensorGate_unitary (addOracle_unitary F) (Submonoid.one_mem _)

/-- On a basis state, the extended oracle adds `F` of the input to the value register and
preserves table memory. -/
theorem oracle_ket (F : X → R) {k : ℕ} (q : X × R) (L : Memory (X := S) (R := R) k) :
    ApplyGate (oracle F k) (Qatlib.Foundations.PureStateMath.Ket (q, L)) =
      Qatlib.Foundations.PureStateMath.Ket ((q.1, q.2 + F q.1), L) := by
  rcases q with ⟨x, z⟩
  rw [oracle, ← tensorState_ket_ket, applyGate_tensorGate, applyGate_addOracle_ket,
    applyGate_one, tensorState_ket_ket]

omit [AddCommGroup R] [DecidableEq X] in

/-- Applying a gate tensored with identity acts independently on each fixed table-memory fiber
of a state. -/
theorem fiber {k : ℕ} (U : Matrix (X × R) (X × R) ℂ)
    (ψ : QState ((X × R) × Memory (X := S) (R := R) k)) (p : X × R) (L : Memory (X := S) (R := R) k) :
    ApplyGate (TensorGate U (1 : Matrix (Memory (X := S) (R := R) k) (Memory (X := S) (R := R) k) ℂ)) ψ (p, L) =
      ApplyGate U (fun q => ψ (q, L)) p := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorGate_apply,
      Matrix.one_apply]

/-- The query word implementing a table phase test by an oracle query, comparison, and inverse
query. -/
def phaseWord (K : Finset X) (k : ℕ) : List (AdjointStep ((X × R) × Memory (X := S) (R := R) k)) :=
  [.backward, .gate (comparison K k), .forward]

omit [AddCommGroup R] [Fintype S] [Fintype X] [Fintype R] in

/-- The table phase word uses exactly two oracle queries. -/
theorem phaseWord_queries (K : Finset X) (k : ℕ) :
    adjointQueryCount (phaseWord (S := S) (R := R) K k) = 2 := rfl

/-- On each amplitude, the phase word multiplies by the table sign evaluated at the input and
the value register shifted by `F`. -/
theorem phaseWord_full (F : X → R) (K : Finset X) (k : ℕ)
    (ψ : QState ((X × R) × Memory (X := S) (R := R) k)) (x : X) (z : R) (L : Memory (X := S) (R := R) k) :
    ApplyGate (evaluate (oracle F k) (phaseWord K k)) ψ ((x, z), L) =
      PhaseCompile.tableSign K (values L) x (z + F x) * ψ ((x, z), L) := by
  simp only [phaseWord, evaluate, instructionMatrix, Matrix.mul_one, applyGate_mul]
  rw [oracle, tensorGate_conjTranspose, addOracle_conjTranspose, Matrix.conjTranspose_one,
    fiber, applyGate_addOracle]
  simp only [Pi.neg_apply, sub_neg_eq_add]
  change ApplyGate (comparison K k) (ApplyGate (TensorGate (AddOracle F) 1) ψ) ((x, z + F x), L) = _
  change (comparison K k *ᵥ ApplyGate (TensorGate (AddOracle F) 1) ψ) ((x, z + F x), L) = _
  rw [comparison, Matrix.mulVec_diagonal, fiber, applyGate_addOracle]
  simp

/-- On a zero value register and fixed table memory, the phase word implements the marked phase
while restoring both auxiliary registers. -/
theorem phaseWord_clean (F : X → R) (K : Finset X) {k : ℕ} (L : Memory (X := S) (R := R) k) (ψ : QState X) :
    ApplyGate (evaluate (oracle F k) (phaseWord K k))
      (TensorState (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket 0)) (Qatlib.Foundations.PureStateMath.Ket L)) =
    TensorState (TensorState (fun x => PhaseCompile.tableSign K (values L) x (F x) * ψ x) (Qatlib.Foundations.PureStateMath.Ket 0)) (Qatlib.Foundations.PureStateMath.Ket L) := by
  funext p
  obtain ⟨⟨x, z⟩, L'⟩ := p
  rw [phaseWord_full]
  by_cases hL : L' = L
  · subst L'
    by_cases hz : z = 0
    · subst z
      simp [TensorState, Qatlib.Foundations.PureStateMath.Ket]
    · simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, hz]
  · simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, hL]

/-- Compiles an abstract phase-query circuit into gates and additive oracle queries on the
enlarged state space with table memory. -/
def compile (K : Finset X) (k : ℕ) : Circuit X → List (AdjointStep ((X × R) × Memory (X := S) (R := R) k))
  | [] => []
  | .gate U :: P => compile K k P ++ [.gate (TensorGate (TensorGate U (1 : Matrix R R ℂ)) 1)]
  | .query :: P => compile K k P ++ phaseWord K k

omit [AddCommGroup R] [Fintype S] [Fintype X] [Fintype R] in

/-- Compilation uses exactly twice as many additive oracle queries as the original circuit has
phase queries. -/
theorem compile_queries (K : Finset X) (k : ℕ) (P : Circuit X) :
    adjointQueryCount (compile (S := S) (R := R) K k P) = 2 * QueryCount P := by
  induction P with
  | nil => rfl
  | cons g P ih =>
    cases g <;> simp only [compile, PhaseCompile.query_append, ih, adjointQueryCount,
      QueryCount, phaseWord_queries]
    all_goals omega

/-- On clean auxiliary registers, the compiled circuit realizes the abstract table phase circuit
and restores the value and memory registers [BrassardHoyerTapp1998Collision]. -/
theorem compile_run (F : X → R) (K : Finset X) {k : ℕ} (L : Memory (X := S) (R := R) k)
    (P : Circuit X) (ψ : QState X) :
    ApplyGate (evaluate (oracle F k) (compile K k P))
      (TensorState (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket 0)) (Qatlib.Foundations.PureStateMath.Ket L)) =
    TensorState (TensorState
      (Run (Matrix.diagonal (fun x => PhaseCompile.tableSign K (values L) x (F x))) P ψ) (Qatlib.Foundations.PureStateMath.Ket 0)) (Qatlib.Foundations.PureStateMath.Ket L) := by
  induction P generalizing ψ with
  | nil => simp only [compile, evaluate, applyGate_one, run_nil]
  | cons g P ih =>
    cases g with
    | gate U =>
      rw [compile, PhaseCompile.eval_append, applyGate_mul]
      simp only [evaluate, instructionMatrix, Matrix.mul_one, applyGate_tensorGate, applyGate_one]
      exact ih (ApplyGate U ψ)
    | query =>
      rw [compile, PhaseCompile.eval_append, applyGate_mul, phaseWord_clean, ih]
      have hd : ApplyGate (Matrix.diagonal (fun x => PhaseCompile.tableSign K (values L) x (F x))) ψ =
          fun x => PhaseCompile.tableSign K (values L) x (F x) * ψ x := by
        funext x
        exact Matrix.mulVec_diagonal _ _ x
      rw [run_query, hd]

/-- The evaluated table phase word is unitary. -/
theorem phaseWord_unitary (F : X → R) (K : Finset X) (k : ℕ) :
    evaluate (oracle F k) (phaseWord K k) ∈ Matrix.unitaryGroup ((X × R) × Memory (X := S) (R := R) k) ℂ := by
  simp only [phaseWord, evaluate, instructionMatrix, Matrix.mul_one]
  exact (Matrix.unitaryGroup _ _).mul_mem
    (_root_.Unitary.star_mem (oracle_unitary F k))
    ((Matrix.unitaryGroup _ _).mul_mem (comparison_unitary K k) (oracle_unitary F k))

/-- Compiling a unitary abstract circuit yields a unitary operator on the enlarged state space. -/
theorem compile_unitary (F : X → R) (K : Finset X) (k : ℕ) (P : Circuit X)
    (hP : IsUnitaryCircuit P) :
    evaluate (oracle F k) (compile K k P) ∈ Matrix.unitaryGroup ((X × R) × Memory (X := S) (R := R) k) ℂ := by
  induction P with
  | nil => exact (Matrix.unitaryGroup _ _).one_mem
  | cons g P ih =>
    cases g with
    | gate U =>
      obtain ⟨hU, htail⟩ := (isUnitaryCircuit_gate U P).mp hP
      rw [compile, PhaseCompile.eval_append]
      simp only [evaluate, instructionMatrix, Matrix.mul_one]
      exact (Matrix.unitaryGroup _ _).mul_mem (ih htail)
        (tensorGate_unitary (tensorGate_unitary hU (Submonoid.one_mem _)) (Submonoid.one_mem _))
    | query =>
      rw [compile, PhaseCompile.eval_append]
      exact (Matrix.unitaryGroup _ _).mul_mem
        (ih ((isUnitaryCircuit_query P).mp hP)) (phaseWord_unitary F K k)

omit [AddCommGroup R] [DecidableEq S] [DecidableEq X] [DecidableEq R] in

/-- The basis cardinality of the search, value, and table registers is `(|X| * |R|) * (|S| *
|R|)^k` [BrassardHoyerTapp1998Collision]. -/
theorem basis_card (k : ℕ) :
    Fintype.card ((X × R) × Memory (X := S) (R := R) k) =
      (Fintype.card X * Fintype.card R) * (Fintype.card S * Fintype.card R) ^ k := by
  simp [Memory]

/-- For `k ≥ 1`, the count `k + 1` lies between `k` and `2 * k`. -/
theorem record_space_bounds (k : ℕ) (hk : 1 ≤ k) : k ≤ k + 1 ∧ k + 1 ≤ 2*k := by omega

end Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable
