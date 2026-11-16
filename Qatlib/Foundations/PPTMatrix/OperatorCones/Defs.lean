/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Tactic.Module

@[expose] public section


noncomputable section



/-!
# PPT maps, separability, entanglement breaking and Schmidt number: definitions

Definitions for the formalization of *Entanglement Breaking after `2(d-1)` PPT Maps*
(PSI manuscript, October 2026 draft): PPT means completely positive and completely copositive,
and the entanglement-breaking index is the least `m ≥ 1` with `T^m` entanglement breaking.

Conventions.

* `M_d` is `Matrix (Fin d) (Fin d) ℂ`; most definitions allow an arbitrary index type.
* A bipartite operator on `ℂ^κ ⊗ ℂ^n` is a `Matrix (κ × n) (κ × n) ℂ`. The **first** factor `κ` is
  the reference and the second factor `n` is the system on which maps act.
* "Positive" means `Matrix.PosSemidef` (Hermitian with nonnegative quadratic form). Operators
  are never assumed normalized and maps are never assumed trace preserving.
* A "map" is a complex-linear map between matrix algebras.
* The definitions make sense for arbitrary index types, where `Matrix.PosSemidef` refers to
  finitely supported vectors; the manuscript is finite-dimensional and every statement about it
  uses `Fin d` or a `Fintype`.

This file is part of the trusted statement layer: it contains definitions only, no proof holes.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n p : Type*}

/-! ### Blocks and `id ⊗ Φ` -/

/-- The `(i, j)` block of an operator on `ℂ^κ ⊗ ℂ^n` with respect to the reference basis. -/
def block {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) (i j : κ) : Matrix n n ℂ :=
  Matrix.of fun a b => X (i, a) (j, b)

/-- Establishes `block_apply`: `block X i j a b = X (i, a) (j, b)`, for the stated parameters. -/
@[simp]
theorem block_apply {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) (i j : κ) (a b : n) :
    block X i j a b = X (i, a) (j, b) :=
  rfl

/-- Establishes `block_add`: `block (X + Y) i j = block X i j + block Y i j`, for the stated parameters. -/
theorem block_add {κ : Type*} (X Y : Matrix (κ × n) (κ × n) ℂ) (i j : κ) :
    block (X + Y) i j = block X i j + block Y i j := by
  ext a b
  simp

/-- Establishes `block_smul`: `block (c • X) i j = c • block X i j`, for the stated parameters. -/
theorem block_smul {κ : Type*} (c : ℂ) (X : Matrix (κ × n) (κ × n) ℂ) (i j : κ) :
    block (c • X) i j = c • block X i j := by
  ext a b
  simp

/-- The map `id_κ ⊗ Φ` on `M_κ ⊗ M_n`: it applies `Φ` to every block,
`((id ⊗ Φ) X)_{(i,a),(j,b)} = Φ(X_{ij})_{ab}` where `X_{ij}` is the `(i, j)` block of `X`. -/
def refMap (κ : Type*) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :
    Matrix (κ × n) (κ × n) ℂ →ₗ[ℂ] Matrix (κ × p) (κ × p) ℂ where
  toFun X := Matrix.of fun x y => Φ (block X x.1 y.1) x.2 y.2
  map_add' X Y := by
    ext x y
    simp [block_add]
  map_smul' c X := by
    ext x y
    simp [block_smul]

/-- Establishes `refMap_apply`: `refMap κ Φ X x y = Φ (block X x.1 y.1) x.2 y.2`, for the stated parameters. -/
@[simp]
theorem refMap_apply {κ : Type*} (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) (x y : κ × p) :
    refMap κ Φ X x y = Φ (block X x.1 y.1) x.2 y.2 :=
  rfl

/-- Matrix transposition `t(N) = Nᵀ` as a complex-linear map. -/
def transposeMap (p : Type*) : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ :=
  (Matrix.transposeLinearEquiv p p ℂ ℂ).toLinearMap

/-- Establishes `transposeMap_apply`: `transposeMap p X = Xᵀ`, for the stated parameters. -/
@[simp]
theorem transposeMap_apply (X : Matrix p p ℂ) : transposeMap p X = Xᵀ :=
  rfl

/-! ### Completely positive, completely copositive and PPT maps -/

/-- `Φ` is completely positive: `id_k ⊗ Φ` maps positive operators to positive operators for
every reference dimension `k`. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), X.PosSemidef →
    (refMap (Fin k) Φ X).PosSemidef

/-- `Φ` is completely copositive: `t ∘ Φ` is completely positive, where `t` is transposition on
the output algebra. -/
def IsCompletelyCopositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  IsCompletelyPositive (transposeMap p ∘ₗ Φ)

/-- A PPT map is a linear map that is both completely positive and completely copositive.
No trace-preservation is assumed. -/
def IsPPTMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  IsCompletelyPositive Φ ∧ IsCompletelyCopositive Φ

/-! ### Separability and entanglement breaking -/

/-- A bipartite operator is separable if it is a finite sum of tensor products of positive
operators. No normalization is imposed; the empty sum shows that `0` is separable. -/
def IsSeparable {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) : Prop :=
  ∃ (N : ℕ) (A : Fin N → Matrix κ κ ℂ) (B : Fin N → Matrix n n ℂ),
    (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧ X = ∑ i, A i ⊗ₖ B i

/-- A completely positive map is entanglement breaking if `(id_k ⊗ Φ)(X)` is separable for every
reference dimension `k` and every positive bipartite input `X` (not necessarily normalized). -/
def IsEntanglementBreaking (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop :=
  IsCompletelyPositive Φ ∧
    ∀ (k : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), X.PosSemidef →
      IsSeparable (refMap (Fin k) Φ X)

/-- The ordered composition `Φ_N ∘ ⋯ ∘ Φ_1` of a list `[Φ_1, …, Φ_N]` of endomorphisms; the head
of the list is applied first, and the empty composition is the identity. -/
def compList (L : List (Module.End ℂ (Matrix n n ℂ))) : Module.End ℂ (Matrix n n ℂ) :=
  L.foldl (fun acc φ => φ ∘ₗ acc) LinearMap.id

/-- The entanglement-breaking index `n(T) = min {m ≥ 1 : T^m is entanglement breaking}`, with
value `⊤` when no positive power of `T` is entanglement breaking. -/
noncomputable def ebIndex (T : Module.End ℂ (Matrix n n ℂ)) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : 1 ≤ m) (_ : IsEntanglementBreaking (T ^ m)), (m : ℕ∞)

/-! ### Partial transposition and qubit-reference block operators -/

/-- Partial transposition `X ↦ X^{Γ_R}` on the reference factor: it swaps the block indices
without transposing the blocks themselves. -/
def partialTransposeRef {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) : Matrix (κ × n) (κ × n) ℂ :=
  Matrix.of fun x y => X (y.1, x.2) (x.1, y.2)

/-- Establishes `partialTransposeRef_apply`: `partialTransposeRef X x y = X (y.1, x.2) (x.1, y.2)`, for the stated parameters. -/
@[simp]
theorem partialTransposeRef_apply {κ : Type*} (X : Matrix (κ × n) (κ × n) ℂ) (x y : κ × n) :
    partialTransposeRef X x y = X (y.1, x.2) (x.1, y.2) :=
  rfl

/-- The operator on `ℂ² ⊗ ℂ^n` whose blocks in the reference basis are `[[A, B], [C, D]]`. -/
def qubitBlocks (A B C D : Matrix n n ℂ) : Matrix (Fin 2 × n) (Fin 2 × n) ℂ :=
  Matrix.of fun x y =>
    (!![A, B; C, D] : Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) x.1 y.1 x.2 y.2

/-! ### Schmidt rank and Schmidt number -/

/-- The coefficient matrix `V` of a bipartite vector `v = ∑ V_{ij} |i⟩ ⊗ |j⟩`. -/
def coeffMatrix {κ : Type*} (v : κ × n → ℂ) : Matrix κ n ℂ :=
  Matrix.of fun i a => v (i, a)

/-- Establishes `coeffMatrix_apply`: `coeffMatrix v i a = v (i, a)`, for the stated parameters. -/
@[simp]
theorem coeffMatrix_apply {κ : Type*} (v : κ × n → ℂ) (i : κ) (a : n) :
    coeffMatrix v i a = v (i, a) :=
  rfl

/-- The Schmidt rank of a bipartite vector: the rank of its coefficient matrix. -/
noncomputable def schmidtRank {κ : Type*} [Fintype n] (v : κ × n → ℂ) : ℕ :=
  (coeffMatrix v).rank

/-- The (unnormalized) pure operator `P_v = |v⟩⟨v|`. -/
def pureState {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec v (star v)

/-- `X` admits a decomposition `X = ∑_α P_{v_α}` into finitely many pure operators whose vectors
all have Schmidt rank at most `k`. For positive `X` this says `SN(X) ≤ k`. -/
def HasSchmidtNumberLE {κ : Type*} [Fintype n] (k : ℕ) (X : Matrix (κ × n) (κ × n) ℂ) : Prop :=
  ∃ (N : ℕ) (v : Fin N → κ × n → ℂ), (∀ α, schmidtRank (v α) ≤ k) ∧ X = ∑ α, pureState (v α)

/-- The Schmidt number `SN(X)`: the smallest `k` such that `X` is a finite sum of pure operators
of Schmidt rank at most `k`. The empty sum gives `SN(0) = 0`. Only meaningful for positive `X`
(for other `X` no such `k` exists and the value is the junk value `0`). -/
noncomputable def schmidtNumber {κ : Type*} [Fintype n] (X : Matrix (κ × n) (κ × n) ℂ) : ℕ :=
  sInf {k | HasSchmidtNumberLE k X}

end Qatlib.Foundations.PPTMatrix.OperatorCones
