/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# DQIQuadOpt25 — source model

Optimization of Quadratic Constraints by Decoded Quantum Interferometry,
fixed arXiv:2510.08061v2 (2025-10; the PDF carries a 2026-03-11 date line, the
body a 2026-03-09 disclaimer).  This module fixes the paper-local objects:

* the field-parameterised constraint functions `f_i : F_p → {+1,-1}`
  (Definition 1, with the ±1 values represented by integers);
* the max-QUADSAT instance of Definition 1, its objective
  `f(x) = ∑_i f_i(b_iᵀx + xᵀC_ix)` and the diagonal / linear-term-free
  sub-family used in Theorem 1;
* the evaluation of a diagonal quadratic form, `xᵀ diag(c) x = ∑_j c_j x_j²`;
* the DQI state of Definition 2, `|P(f)⟩ = ∑_x P(f(x)) |x⟩`, represented by
  its amplitude function;
* the max-LINSAT instance used in Theorem 3, `f(x) = ∑_i f_i(B_i x)`;
* the number of satisfied constraints and the identity
  `∑_i f_i = 2·(#satisfied) − m` for sign-valued constraints.

Boundary: the finite field `F_p` is `ZMod p`; primality is carried as a
hypothesis of the theorem layer, not of the definitions.  Polynomials of the
objective are `Polynomial ℂ` evaluated at the integer objective value.  The
amplitude vector is not normalised (the paper never uses the normalisation in
Theorems 1–3).  No circuit compiler, oracle tape or classical preprocessing
machine is modelled here; those appear only through the lightweight procedure
model of `AlgorithmModel.lean`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIQuadOpt25.MainResults.Source

universe u

/-! ## Constraint functions and the max-QUADSAT objective -/

/-- A constraint function `f_i : F_p → {+1,−1}` (Definition 1).  Values are
integers so that sums of satisfied constraints can be taken in `ℤ`. -/
abbrev SignFunc (p : ℕ) := ZMod p → ℤ

/-- `g` really takes only the values `+1` and `−1`. -/
def IsSignValued {p : ℕ} (g : SignFunc p) : Prop := ∀ x, g x = 1 ∨ g x = -1

/-- The max-QUADSAT instance of Definition 1: constraint functions `f_i`,
linear parts `b_i` and symmetric matrices `C_i` over `F_p`. -/
structure QUADSATInstance (p n m : ℕ) where
  /-- Constraint functions `f_1, …, f_m`. -/
  f : Fin m → SignFunc p
  /-- Linear parts `b_1, …, b_m ∈ F_p^n`. -/
  b : Fin m → Fin n → ZMod p
  /-- Quadratic-form matrices `C_1, …, C_m ∈ F_p^{n×n}`. -/
  C : Fin m → Matrix (Fin n) (Fin n) (ZMod p)

/-- The linear part `b_iᵀ x` of the `i`-th constraint. -/
def linearTerm {p n m : ℕ} (inst : QUADSATInstance p n m) (x : Fin n → ZMod p)
    (i : Fin m) : ZMod p :=
  ∑ j, inst.b i j * x j

/-- The quadratic part `xᵀ C_i x` of the `i`-th constraint. -/
def quadTerm {p n m : ℕ} (inst : QUADSATInstance p n m) (x : Fin n → ZMod p)
    (i : Fin m) : ZMod p :=
  x ⬝ᵥ (inst.C i).mulVec x

/-- The argument `b_iᵀ x + xᵀ C_i x` of the `i`-th constraint (Definition 1). -/
def constraintArg {p n m : ℕ} (inst : QUADSATInstance p n m) (x : Fin n → ZMod p)
    (i : Fin m) : ZMod p :=
  linearTerm inst x i + quadTerm inst x i

/-- The max-QUADSAT objective `f(x) = ∑_{i=1}^m f_i(b_iᵀ x + xᵀ C_i x)`
(Definition 1). -/
def objective {p n m : ℕ} (inst : QUADSATInstance p n m) (x : Fin n → ZMod p) : ℤ :=
  ∑ i, inst.f i (constraintArg inst x i)

/-- All constraints of the instance are sign-valued. -/
def IsSignValuedInstance {p n m : ℕ} (inst : QUADSATInstance p n m) : Prop :=
  ∀ i y, inst.f i y = 1 ∨ inst.f i y = -1

/-- `C` is a diagonal matrix. -/
def IsDiagonalMatrix {p n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod p)) : Prop :=
  ∀ i j, i ≠ j → C i j = 0

/-- `C` is a symmetric matrix (part of Definition 1). -/
def IsSymmetricMatrix {p n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod p)) : Prop :=
  ∀ i j, C i j = C j i

/-- A diagonal matrix is symmetric (Definition 1 asks for symmetric `C_i`; the
diagonal instances of Theorem 1 automatically satisfy this). -/
theorem isSymmetric_of_isDiagonal {p n : ℕ} {C : Matrix (Fin n) (Fin n) (ZMod p)}
    (hC : IsDiagonalMatrix C) : IsSymmetricMatrix C := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · rw [hC i j hij, hC j i (Ne.symm hij)]

/-- The diagonal / linear-term-free sub-family of Theorem 1: `b_i = 0` and
every `C_i` is diagonal. -/
def IsDiagonalInstance {p n m : ℕ} (inst : QUADSATInstance p n m) : Prop :=
  (∀ i j, inst.b i j = 0) ∧ ∀ i, IsDiagonalMatrix (inst.C i)

/-- The diagonal of `C_i`, viewed as the column vector `(C_i)_{jj}`.  For a
diagonal instance these vectors are the columns of the parity-check matrix of
Theorem 1. -/
def diagVector {p n m : ℕ} (inst : QUADSATInstance p n m) (i : Fin m) : Fin n → ZMod p :=
  fun j => inst.C i j j

/-! ## Diagonal quadratic forms -/

/-- Expansion of a quadratic form with a diagonal matrix:
`xᵀ diag(c) x = ∑_j c_j x_j²`.  This is the form taken by the constraints in
Theorem 1 (and by the quadratic-OPI embedding of Theorem 2). -/
theorem dotProduct_mulVec_of_diagonal {p n : ℕ}
    (C : Matrix (Fin n) (Fin n) (ZMod p)) (hC : IsDiagonalMatrix C)
    (x : Fin n → ZMod p) :
    x ⬝ᵥ C.mulVec x = ∑ j, C j j * x j * x j := by
  have hCd : C = Matrix.diagonal (fun j => C j j) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [hC i j h, Matrix.diagonal_apply_ne _ h]
  rw [hCd]
  simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- On a diagonal instance with no linear terms, the constraint argument is the
diagonal quadratic form `∑_j (C_i)_{jj} x_j²`. -/
theorem constraintArg_diagonal {p n m : ℕ}
    (inst : QUADSATInstance p n m) (hinst : IsDiagonalInstance inst)
    (x : Fin n → ZMod p) (i : Fin m) :
    constraintArg inst x i = ∑ j, inst.C i j j * x j * x j := by
  have hb : linearTerm inst x i = 0 := by
    unfold linearTerm
    exact Finset.sum_eq_zero fun j _ => by rw [hinst.1 i j, zero_mul]
  unfold constraintArg quadTerm
  rw [hb, zero_add]
  exact dotProduct_mulVec_of_diagonal (inst.C i) (hinst.2 i) x

/-! ## The DQI state (Definition 2) -/

/-- The DQI amplitude of Definition 2: the coefficient of `|x⟩` is
`P(f(x))`, with `f` the max-QUADSAT objective. -/
def dqiAmplitude {p n m : ℕ} (inst : QUADSATInstance p n m) (P : Polynomial ℂ)
    (x : Fin n → ZMod p) : ℂ :=
  P.eval ((objective inst x : ℤ) : ℂ)

/-- The vector `ψ` is the DQI state of a degree-`≤ ℓ` polynomial applied to the
objective of `inst` (Definition 2, Eq. (7)). -/
def IsDQIState {p n m : ℕ} (inst : QUADSATInstance p n m) (ℓ : ℕ)
    (ψ : (Fin n → ZMod p) → ℂ) : Prop :=
  ∃ P : Polynomial ℂ, P.natDegree ≤ ℓ ∧ ψ = dqiAmplitude inst P

/-- The DQI state itself (Definition 2, Eq. (7)): `∑_x P(f(x)) |x⟩`, encoded by
its amplitude function. -/
def dqiState {p n m : ℕ} (inst : QUADSATInstance p n m) (P : Polynomial ℂ) :
    (Fin n → ZMod p) → ℂ :=
  dqiAmplitude inst P

/-- The state prepared is a DQI state of the instance at degree `ℓ`. -/
theorem dqiState_isDQIState {p n m : ℕ} (inst : QUADSATInstance p n m) (P : Polynomial ℂ)
    (ℓ : ℕ) (h : P.natDegree ≤ ℓ) : IsDQIState inst ℓ (dqiState inst P) :=
  ⟨P, h, rfl⟩

/-! ## Satisfied constraints -/

/-- The number of satisfied constraints of an instance at `x`: the number of
indices `i` with `f_i(b_iᵀx + xᵀC_ix) = +1`. -/
def satCount {p n m : ℕ} (inst : QUADSATInstance p n m) (x : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun i => inst.f i (constraintArg inst x i) = 1).card

/-- For sign-valued constraints the objective is twice the number of satisfied
constraints minus the number of constraints:
`∑_i f_i = 2·#{i : f_i = +1} − m`. -/
theorem sum_sign_eq_two_satCount_sub {m : ℕ} (g : Fin m → ℤ)
    (hg : ∀ i, g i = 1 ∨ g i = -1) :
    ∑ i, g i = 2 * ((Finset.univ.filter fun i => g i = 1).card : ℤ) - (m : ℤ) := by
  have h : ∀ i, g i = 2 * (if g i = 1 then (1 : ℤ) else 0) - 1 := by
    intro i
    rcases hg i with h1 | h1 <;> simp [h1]
  calc ∑ i, g i = ∑ i, (2 * (if g i = 1 then (1 : ℤ) else 0) - 1) :=
        Finset.sum_congr rfl fun i _ => h i
    _ = 2 * (∑ i, (if g i = 1 then (1 : ℤ) else 0)) - ∑ _i : Fin m, (1 : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * ((Finset.univ.filter fun i => g i = 1).card : ℤ) - (m : ℤ) := by
        rw [Finset.sum_boole]
        simp

/-- The objective of a sign-valued instance is `2·satCount − m`. -/
theorem objective_eq_two_satCount_sub {p n m : ℕ} (inst : QUADSATInstance p n m)
    (hinst : IsSignValuedInstance inst) (x : Fin n → ZMod p) :
    objective inst x = 2 * (satCount inst x : ℤ) - (m : ℤ) := by
  unfold objective satCount
  exact sum_sign_eq_two_satCount_sub _ (fun i => hinst i (constraintArg inst x i))

/-! ## max-LINSAT (used in Theorem 3) -/

/-- A max-LINSAT instance: constraint functions `f_i` and a matrix
`B ∈ F_p^{m×n}` whose rows are the linear functionals (Theorem 3). -/
structure LINSATInstance (p n m : ℕ) where
  /-- Constraint functions `f_1, …, f_m`. -/
  f : Fin m → SignFunc p
  /-- The matrix `B` of the linear constraints. -/
  B : Matrix (Fin m) (Fin n) (ZMod p)

/-- The argument `B_i x = ∑_j B_{ij}x_j` of the `i`-th max-LINSAT constraint. -/
def linsatArg {p n m : ℕ} (inst : LINSATInstance p n m) (x : Fin n → ZMod p)
    (i : Fin m) : ZMod p :=
  ∑ j, inst.B i j * x j

/-- The max-LINSAT objective `f(x) = ∑_i f_i(B_i x)` (Theorem 3). -/
def linsatObjective {p n m : ℕ} (inst : LINSATInstance p n m) (x : Fin n → ZMod p) : ℤ :=
  ∑ i, inst.f i (linsatArg inst x i)

/-- The max-LINSAT DQI amplitude: `|P(f)⟩ = ∑_x P(f(x)) |x⟩` (Definition 2
specialised to max-LINSAT). -/
def linsatDQIAmp {p n m : ℕ} (inst : LINSATInstance p n m) (P : Polynomial ℂ)
    (x : Fin n → ZMod p) : ℂ :=
  P.eval ((linsatObjective inst x : ℤ) : ℂ)

/-- The number of satisfied max-LINSAT constraints at `x`. -/
def linsatSatCount {p n m : ℕ} (inst : LINSATInstance p n m) (x : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun i => inst.f i (linsatArg inst x i) = 1).card

end Qatlib.Papers.DQIQuadOpt25.MainResults.Source
