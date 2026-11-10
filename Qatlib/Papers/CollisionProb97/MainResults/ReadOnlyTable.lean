/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ActualPhaseProgram
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

abbrev Memory (k : ℕ) := Fin k → X × R

def values {k : ℕ} (L : Memory (X := S) (R := R) k) : Finset R :=
  Finset.univ.image fun j => (L j).2

def oracle (F : X → R) (k : ℕ) : Matrix ((X × R) × Memory (X := S) (R := R) k) ((X × R) × Memory (X := S) (R := R) k) ℂ :=
  TensorGate (AddOracle F) 1

def comparison (K : Finset X) (k : ℕ) : Matrix ((X × R) × Memory (X := S) (R := R) k) ((X × R) × Memory (X := S) (R := R) k) ℂ :=
  Matrix.diagonal fun p => PhaseCompile.tableSign K (values p.2) p.1.1 p.1.2

omit [AddCommGroup R] in

theorem comparison_unitary (K : Finset X) (k : ℕ) :
    comparison (S := S) (R := R) K k ∈ Matrix.unitaryGroup ((X × R) × Memory (X := S) (R := R) k) ℂ := by
  rw [comparison, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases h : p.1.1 ∉ K ∧ p.1.2 ∈ values p.2 <;> simp [PhaseCompile.tableSign, h]
  · simp [hpq]

theorem oracle_unitary (F : X → R) (k : ℕ) :
    oracle F k ∈ Matrix.unitaryGroup ((X × R) × Memory (X := S) (R := R) k) ℂ :=
  tensorGate_unitary (addOracle_unitary F) (Submonoid.one_mem _)

theorem oracle_ket (F : X → R) {k : ℕ} (q : X × R) (L : Memory (X := S) (R := R) k) :
    ApplyGate (oracle F k) (Qatlib.Foundations.PureStateMath.Ket (q, L)) =
      Qatlib.Foundations.PureStateMath.Ket ((q.1, q.2 + F q.1), L) := by
  rcases q with ⟨x, z⟩
  rw [oracle, ← tensorState_ket_ket, applyGate_tensorGate, applyGate_addOracle_ket,
    applyGate_one, tensorState_ket_ket]

omit [AddCommGroup R] [DecidableEq X] in

theorem fiber {k : ℕ} (U : Matrix (X × R) (X × R) ℂ)
    (ψ : QState ((X × R) × Memory (X := S) (R := R) k)) (p : X × R) (L : Memory (X := S) (R := R) k) :
    ApplyGate (TensorGate U (1 : Matrix (Memory (X := S) (R := R) k) (Memory (X := S) (R := R) k) ℂ)) ψ (p, L) =
      ApplyGate U (fun q => ψ (q, L)) p := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorGate_apply,
      Matrix.one_apply]

def phaseWord (K : Finset X) (k : ℕ) : List (AdjointStep ((X × R) × Memory (X := S) (R := R) k)) :=
  [.backward, .gate (comparison K k), .forward]

omit [AddCommGroup R] [Fintype S] [Fintype X] [Fintype R] in

theorem phaseWord_queries (K : Finset X) (k : ℕ) :
    adjointQueryCount (phaseWord (S := S) (R := R) K k) = 2 := rfl

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

def compile (K : Finset X) (k : ℕ) : Circuit X → List (AdjointStep ((X × R) × Memory (X := S) (R := R) k))
  | [] => []
  | .gate U :: P => compile K k P ++ [.gate (TensorGate (TensorGate U (1 : Matrix R R ℂ)) 1)]
  | .query :: P => compile K k P ++ phaseWord K k

omit [AddCommGroup R] [Fintype S] [Fintype X] [Fintype R] in

theorem compile_queries (K : Finset X) (k : ℕ) (P : Circuit X) :
    adjointQueryCount (compile (S := S) (R := R) K k P) = 2 * QueryCount P := by
  induction P with
  | nil => rfl
  | cons g P ih =>
    cases g <;> simp only [compile, PhaseCompile.query_append, ih, adjointQueryCount,
      QueryCount, phaseWord_queries]
    all_goals omega

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

theorem phaseWord_unitary (F : X → R) (K : Finset X) (k : ℕ) :
    evaluate (oracle F k) (phaseWord K k) ∈ Matrix.unitaryGroup ((X × R) × Memory (X := S) (R := R) k) ℂ := by
  simp only [phaseWord, evaluate, instructionMatrix, Matrix.mul_one]
  exact (Matrix.unitaryGroup _ _).mul_mem
    (_root_.Unitary.star_mem (oracle_unitary F k))
    ((Matrix.unitaryGroup _ _).mul_mem (comparison_unitary K k) (oracle_unitary F k))

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

theorem basis_card (k : ℕ) :
    Fintype.card ((X × R) × Memory (X := S) (R := R) k) =
      (Fintype.card X * Fintype.card R) * (Fintype.card S * Fintype.card R) ^ k := by
  simp [Memory]

theorem record_space_bounds (k : ℕ) (hk : 1 ≤ k) : k ≤ k + 1 ∧ k + 1 ≤ 2*k := by omega

end Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable
