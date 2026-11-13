/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamDecodedQI25.MainResults.Source.PaperModel
import QuantumInfo.ForMathlib.HermitianMat.LogExp
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# HamDecodedQI25 — density matrices, Gibbs states and preparation procedures

Fixed arXiv:2510.07913 (v1).  This module supplies the operator layer used by the
state-preparation claims (Theorems 1–5, 12–13, 22–23, 25–26, 31, 38–39, 60, 64
and their supporting lemmas):

* `Mat d` is the algebra of `d × d` complex matrices, used to represent both
  density matrices (`d = 2^n`) and, via coefficient matrices on `(A, B)`, vectors
  of a bipartite space;
* `traceDistance` is the trace distance `½ ‖ρ - σ‖₁` (Eqn. (28) etc.);
* `hmExp` is the matrix exponential of a Hermitian matrix (continuous functional
  calculus), `gibbsState` the Gibbs state `e^{-βH}/Tr e^{-βH}`, and `polyState`
  the polynomial Hamiltonian state `P²(H)/Tr P²(H)` (Eqn. (26), (30), (45));
* `Procedure` is a specification record, with no implementation guarantee.
* `PreparationModel` supplies an external operational semantics and its operation
  traces. `PreparesIn` requires a program in that supplied model, with output and
  trace length matching the specification. No such model or preparation algorithm
  is constructed here. The trace-distance lemmas below are unconditional.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexOrder
open Matrix

namespace Qatlib.Papers.HamDecodedQI25.MainResults

/-- Complex `d × d` matrices; a density matrix on `d` levels is an element of
`Mat d` with unit trace, positivity and hermiticity (those side conditions are
carried as hypotheses where needed). -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Trace distance `½ ‖ρ - σ‖₁` of two matrices (Eqn. (28) of the paper). -/
def traceDistance {d : ℕ} (ρ σ : Mat d) : ℝ := (1 / 2) * traceNorm (ρ - σ)

/-- Matrix exponential of a Hermitian matrix, via the continuous functional
calculus (`cfc Real.exp`); on the eigenbasis this is `diag (e^{λ_i})`. -/
def hmExp {d : ℕ} (A : Mat d) : Mat d := cfc Real.exp A

/-- The Gibbs state `e^{-βH} / Tr[e^{-βH}]` (Eqn. (28)). -/
def gibbsState {d : ℕ} (β : ℝ) (H : Mat d) : Mat d :=
  (trace (hmExp (-(β • H))))⁻¹ • hmExp (-(β • H))

/-- The polynomial Hamiltonian state `P²(H)/Tr[P²(H)]` (Eqn. (26), (30), (45)),
where `P(H)` is the polynomial functional calculus `Polynomial.aeval H P` and
`P²(H) = P(H) * P(H)`. -/
def polyState {d : ℕ} (P : Polynomial ℂ) (H : Mat d) : Mat d :=
  let M := Polynomial.aeval H P
  (trace (M * M))⁻¹ • (M * M)

/-- Output and budget specification; this record alone is not a preparation algorithm. -/
structure Procedure (d : ℕ) where
  /-- Specified output matrix. -/
  state : Mat d
  /-- Declared resource count of the procedure. -/
  cost : ℕ

/-- External preparation semantics. The caller must supply a physical model in
which `operations` lists all charged operations and `execute` is its output.
This interface does not construct or certify that physical interpretation. -/
structure PreparationModel (d : ℕ) where
  Program : Type
  Operation : Type
  operations : Program → List Operation
  execute : Program → Mat d

/-- A specification is realized relative to the supplied operational model. -/
def Procedure.Realized {d : ℕ} (M : PreparationModel d) (Q : Procedure d) : Prop :=
  ∃ p : M.Program, M.execute p = Q.state ∧ (M.operations p).length = Q.cost

/-- Conditional preparation assertion in an explicitly supplied model; an arbitrary
matrix and budget record no longer suffices as a witness. -/
def PreparesIn {d : ℕ} (M : PreparationModel d) (ρ : Mat d) (T : ℕ) : Prop :=
  ∃ p : M.Program, M.execute p = ρ ∧ (M.operations p).length ≤ T

/-- A realized specification transfers its budget bound to the supplied model. -/
theorem preparesIn_of_realized {d : ℕ} {M : PreparationModel d}
    {Q : Procedure d} (h : Q.Realized M) {T : ℕ} (hT : Q.cost ≤ T) :
    PreparesIn M Q.state T := by
  obtain ⟨p, hp, hc⟩ := h
  exact ⟨p, hp, hc.trans_le hT⟩

/-- Trace distance is symmetric. -/
theorem traceDistance_symm {d : ℕ} (ρ σ : Mat d) :
    traceDistance ρ σ = traceDistance σ ρ := by
  unfold traceDistance
  rw [show σ - ρ = -(ρ - σ) by abel, traceNorm_neg]

/-- Trace distance vanishes on equal states. -/
@[simp] theorem traceDistance_self {d : ℕ} (ρ : Mat d) : traceDistance ρ ρ = 0 := by
  unfold traceDistance
  rw [sub_self, traceNorm_zero, mul_zero]

end Qatlib.Papers.HamDecodedQI25.MainResults
