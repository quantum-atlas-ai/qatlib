/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper layer for *A New Quantum Algorithm for Linear Systems beyond the Condition Number*
(QLSBeyondCond25), fixed source version arXiv:2510.05588v3.

This file formalises the two linear-algebra results that the quantum-walk construction of
Section 3 rests on:

* Lemma 2.6 (paper page 11): every vector `ψ₀ ∈ ℝ^{N+1}` has a *unique* orthogonal
  decomposition `ψ₀ = u + v` with `u` in the null space of the augmented matrix `H = [A, -b]`
  and `v` in the row space of `H`.
* Theorem 2.7 (paper page 12, Eq. (1)): the vector decomposition theorem
  `ψ₀ = (1/(1+‖y‖₂²)) • (θ - θ⊥)` with `θ = [y; 1] ∈ Null(H)` and `θ⊥ = [y; -‖y‖₂²] = Hᵀ p`,
  together with the minimum-ℓ₂-norm characterisation of `y = A⁺b`.

All declarations below are proved outright; no trusted assumptions are added.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace

namespace Qatlib.Papers.QLSBeyondCond25.MainResults.LinearAlgebra

variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

/-! ## Lemma 2.6: orthogonal decomposition into null space and row space -/

/-- The null space of a matrix `H`, viewed as a submodule of `EuclideanSpace ℝ (Sum N (Fin 1))`.
Paper page 11: `Null(H) = {x | H x = 0}`. -/
def nullSpace (H : Matrix M (Sum N (Fin 1)) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Sum N (Fin 1))) :=
  (Matrix.toEuclideanLin H).ker

/-- The row space of a matrix `H`: the range of the transpose acting on column vectors.
Paper page 11: `Row(H) = span{rows of H}`. -/
def rowSpace (H : Matrix M (Sum N (Fin 1)) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Sum N (Fin 1))) :=
  (Matrix.toEuclideanLin Hᵀ).range

/-- Lemma 2.5 (Fundamental Theorem of Linear Algebra, Part 1 and 2, quoted in the paper on
page 11): the row space and the null space of `H` are orthogonal complements. -/
theorem orthogonal_nullSpace_eq_rowSpace (H : Matrix M (Sum N (Fin 1)) ℝ) :
    (nullSpace H)ᗮ = rowSpace H := by
  unfold nullSpace rowSpace
  rw [LinearMap.orthogonal_ker]
  congr 1
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Consequence used in the proof of Lemma 2.6: the row space is the orthogonal complement of
the null space. -/
theorem rowSpace_eq_orthogonal_nullSpace (H : Matrix M (Sum N (Fin 1)) ℝ) :
    rowSpace H = (nullSpace H)ᗮ :=
  (orthogonal_nullSpace_eq_rowSpace H).symm

/-- Lemma 2.6 (paper page 11, equation `ψ₀ = u + v`): every vector `ψ₀` of `ℝ^{N+1}`
decomposes uniquely as `ψ₀ = u + v` with `u ∈ Null(H)`, `v ∈ Row(H)` and `⟨u, v⟩ = 0`.

The proof is the paper's proof: `Row(H)` and `Null(H)` are orthogonal complements
(Lemma 2.5, formalised above), so an orthogonal decomposition exists; uniqueness follows
because `Null(H) ⊓ Row(H) = ⊥`. -/
theorem lemma26_orthogonal_decomposition (H : Matrix M (Sum N (Fin 1)) ℝ)
    (ψ₀ : EuclideanSpace ℝ (Sum N (Fin 1))) :
    ∃ u v : EuclideanSpace ℝ (Sum N (Fin 1)),
      u ∈ nullSpace H ∧ v ∈ rowSpace H ∧
      ψ₀ = u + v ∧ ⟪u, v⟫_ℝ = 0 ∧
      ∀ u' v', u' ∈ nullSpace H → v' ∈ rowSpace H →
        ψ₀ = u' + v' → u' = u ∧ v' = v := by
  -- Existence: orthogonal decomposition along the row space.
  obtain ⟨v, hv, u, hu, hsum⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := rowSpace H) ψ₀
  -- `u ∈ (rowSpace H)ᗮ = (nullSpace H)ᗮᗮ = nullSpace H`
  have huN : u ∈ nullSpace H := by
    have h1 : u ∈ ((nullSpace H)ᗮ)ᗮ := by
      rwa [rowSpace_eq_orthogonal_nullSpace H] at hu
    rwa [Submodule.orthogonal_orthogonal] at h1
  have hinner : ⟪u, v⟫_ℝ = 0 := by
    have h := Submodule.inner_right_of_mem_orthogonal (K := rowSpace H) hv hu
    rwa [real_inner_comm] at h
  have hsumuv : ψ₀ = u + v := by rw [hsum, add_comm]
  refine ⟨u, v, huN, hv, hsumuv, hinner, ?_⟩
  -- Uniqueness.
  intro u' v' hu' hv' hsum'
  have hlinear : u' + v' = v + u := hsum'.symm.trans hsum
  have hdiff : u' - u = v - v' := by
    calc u' - u = (u' + v') - v' - u := by abel
      _ = (v + u) - v' - u := by rw [hlinear]
      _ = v - v' := by abel
  have hmemN : u' - u ∈ nullSpace H := (nullSpace H).sub_mem hu' huN
  have hmemR : u' - u ∈ (nullSpace H)ᗮ := by
    rw [← rowSpace_eq_orthogonal_nullSpace H]
    rw [hdiff]
    exact (rowSpace H).sub_mem hv hv'
  have hzero : u' - u = 0 := by
    have horth : ⟪u' - u, u' - u⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hmemN hmemR
    exact inner_self_eq_zero.mp horth
  have huu : u' = u := sub_eq_zero.mp hzero
  refine ⟨huu, ?_⟩
  have h : u + v' = u + v := by
    calc u + v' = u' + v' := by rw [huu]
      _ = ψ₀ := hsum'.symm
      _ = v + u := hsum
      _ = u + v := add_comm v u
  exact add_left_cancel h

/-! ## Theorem 2.7: the vector decomposition theorem for `H = [A, -b]` -/

/-- The augmented matrix `H = [A, -b]` of the linear system `A y = b` (paper page 12). -/
def augmentedMatrix (A : Matrix M N ℝ) (b : M → ℝ) : Matrix M (Sum N (Fin 1)) ℝ :=
  Matrix.of fun i => Sum.elim (fun j => A i j) (fun _ => -b i)

/-- The `inl` entry of the augmented matrix `H = [A, -b]` is `A i j`. -/
@[simp] theorem augmentedMatrix_inl (A : Matrix M N ℝ) (b : M → ℝ) (i : M) (j : N) :
    augmentedMatrix A b i (Sum.inl j) = A i j := rfl

/-- The `inr` entry of the augmented matrix `H = [A, -b]` is `-b i`. -/
@[simp] theorem augmentedMatrix_inr (A : Matrix M N ℝ) (b : M → ℝ) (i : M) (k : Fin 1) :
    augmentedMatrix A b i (Sum.inr k) = -b i := rfl

/-- The vector `θ = [y; 1]` of Eq. (2) of the proof of Theorem 2.7 (paper page 12). -/
def augmentSolution (y : N → ℝ) : Sum N (Fin 1) → ℝ :=
  Sum.elim y (fun _ => 1)

/-- The `inl` entry of `θ = [y; 1]` is `y j`. -/
@[simp] theorem augmentSolution_inl (y : N → ℝ) (j : N) :
    augmentSolution y (Sum.inl j) = y j := rfl

/-- The `inr` entry of `θ = [y; 1]` is `1`. -/
@[simp] theorem augmentSolution_inr (y : N → ℝ) (k : Fin 1) :
    augmentSolution y (Sum.inr k) = 1 := rfl

/-- The row-space component `θ⊥ = [y; -‖y‖₂²]` of the proof of Theorem 2.7 (paper page 12). -/
def rowPerpComponent (y : N → ℝ) : Sum N (Fin 1) → ℝ :=
  Sum.elim y (fun _ => -(y ⬝ᵥ y))

/-- The `inl` entry of `θ⊥ = [y; -‖y‖₂²]` is `y j`. -/
@[simp] theorem rowPerpComponent_inl (y : N → ℝ) (j : N) :
    rowPerpComponent y (Sum.inl j) = y j := rfl

/-- The `inr` entry of `θ⊥ = [y; -‖y‖₂²]` is `-‖y‖₂²`. -/
@[simp] theorem rowPerpComponent_inr (y : N → ℝ) (k : Fin 1) :
    rowPerpComponent y (Sum.inr k) = -(y ⬝ᵥ y) := rfl

/-- The distinguished vector `ψ₀ = [0, …, 0, 1]ᵀ` of Theorem 2.7 (paper page 12). -/
def psiZero : Sum N (Fin 1) → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

/-- The `inl` entry of `ψ₀ = [0, …, 0, 1]ᵀ` is `0`. -/
@[simp] theorem psiZero_inl (j : N) : psiZero (Sum.inl j : Sum N (Fin 1)) = 0 := rfl

/-- The `inr` entry of `ψ₀ = [0, …, 0, 1]ᵀ` is `1`. -/
@[simp] theorem psiZero_inr (k : Fin 1) : psiZero (Sum.inr k : Sum N (Fin 1)) = 1 := rfl

/-- Helper: `p ᵥ* A = Aᵀ *ᵥ p` for real matrices (`vecMul` is `dotProduct` on the left). -/
theorem vecMul_eq_transpose_mulVec (A : Matrix M N ℝ) (p : M → ℝ) :
    p ᵥ* A = Aᵀ *ᵥ p := by
  funext j
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

/-- Theorem 2.7, first claim: `θ = [y; 1]` lies in the null space of `H = [A, -b]`
because `H θ = A y - b = 0` (paper page 12, right after Eq. (2)). -/
theorem augmentedMatrix_mulVec_augmentSolution (A : Matrix M N ℝ) (b : M → ℝ) (y : N → ℝ)
    (hy : A *ᵥ y = b) : augmentedMatrix A b *ᵥ augmentSolution y = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, augmentedMatrix_inl,
    augmentedMatrix_inr, augmentSolution_inl, augmentSolution_inr]
  -- `∑ j, A i j * y j = b i` and the single extra column contributes `-b i`.
  have hi : (∑ j, A i j * y j) = b i := by
    have := congrFun hy i
    simpa [Matrix.mulVec, dotProduct] using this
  rw [hi]
  simp

/-- Theorem 2.7, second claim: the row-space component `θ⊥ = [y; -‖y‖₂²]` is `Hᵀ p`
for `p` any dual witness of `y` (`Aᵀ p = y`).  In the paper `p = (AAᵀ)⁺b`; the two facts
`Aᵀ p = y` and `p·b = ‖y‖₂²` are exactly what is used. -/
theorem rowPerpComponent_eq_transpose_mulVec (A : Matrix M N ℝ) (b : M → ℝ) (y : N → ℝ)
    (p : M → ℝ) (hy : A *ᵥ y = b) (hp : Aᵀ *ᵥ p = y) :
    (augmentedMatrix A b)ᵀ *ᵥ p = rowPerpComponent y := by
  -- `p · b = p · (A y) = (Aᵀ p) · y = y · y`
  have hdot : p ⬝ᵥ b = y ⬝ᵥ y := by
    calc p ⬝ᵥ b = p ⬝ᵥ (A *ᵥ y) := by rw [hy]
      _ = (p ᵥ* A) ⬝ᵥ y := dotProduct_mulVec p A y
      _ = (Aᵀ *ᵥ p) ⬝ᵥ y := by rw [vecMul_eq_transpose_mulVec]
      _ = y ⬝ᵥ y := by rw [hp]
  funext s
  cases s with
  | inl j =>
    have hj : (∑ i, A i j * p i) = y j := by
      have := congrFun hp j
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, augmentedMatrix_inl,
      rowPerpComponent_inl]
    exact hj
  | inr k =>
    have hk : (∑ i, (-b i) * p i) = -(y ⬝ᵥ y) := by
      have h1 : (∑ i, (-b i) * p i) = -(∑ i, b i * p i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h2 : (∑ i, b i * p i) = b ⬝ᵥ p := rfl
      rw [h1, h2, dotProduct_comm, hdot]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, augmentedMatrix_inr,
      rowPerpComponent_inr]
    exact hk

/-- Theorem 2.7, Eq. (1) (paper page 12): `ψ₀ = (1/(1+‖y‖₂²)) • (θ - θ⊥)`.
This is the algebraic identity `[y;1] - [y;-‖y‖₂²] = [0; 1+‖y‖₂²]` rescaled. -/
theorem augmentSolution_decomposition (y : N → ℝ) :
    (1 / (1 + y ⬝ᵥ y)) • (augmentSolution y - rowPerpComponent y) = psiZero := by
  have hpos : 0 < 1 + y ⬝ᵥ y := by
    have hnn : 0 ≤ y ⬝ᵥ y := by
      simpa using dotProduct_star_self_nonneg (v := y)
    linarith
  funext s
  cases s with
  | inl j => simp
  | inr k =>
    have hne : (1 + y ⬝ᵥ y) ≠ 0 := ne_of_gt hpos
    have hmain : (1 : ℝ) / (1 + y ⬝ᵥ y) * (1 + y ⬝ᵥ y) = 1 :=
      div_mul_cancel₀ 1 hne
    simpa [Pi.smul_apply, Pi.sub_apply, augmentSolution_inr, rowPerpComponent_inr,
      psiZero_inr, sub_neg_eq_add] using hmain

/-- Theorem 2.7, additional claim: a solution `y` that has a dual witness `p` (`Aᵀ p = y`)
has minimum ℓ₂ norm among all solutions of `A y' = b` (paper page 12, last paragraph).
The proof is the paper's: `y` is orthogonal to `y' - y ∈ Null(A)`, so the Pythagorean
identity gives `‖y'‖² = ‖y‖² + ‖y' - y‖² ≥ ‖y‖²`. -/
theorem min_norm_of_dual_witness (A : Matrix M N ℝ) (b : M → ℝ) (y : N → ℝ) (p : M → ℝ)
    (hy : A *ᵥ y = b) (hp : Aᵀ *ᵥ p = y) :
    ∀ y' : N → ℝ, A *ᵥ y' = b → y ⬝ᵥ y ≤ y' ⬝ᵥ y' := by
  intro y' hy'
  -- `y · (y' - y) = (Aᵀ p) · (y' - y) = p · (A (y' - y)) = 0`
  have horth : y ⬝ᵥ (y' - y) = 0 := by
    calc y ⬝ᵥ (y' - y) = (Aᵀ *ᵥ p) ⬝ᵥ (y' - y) := by rw [hp]
      _ = (p ᵥ* A) ⬝ᵥ (y' - y) := by rw [vecMul_eq_transpose_mulVec]
      _ = p ⬝ᵥ (A *ᵥ (y' - y)) := (dotProduct_mulVec p A (y' - y)).symm
      _ = p ⬝ᵥ (A *ᵥ y' - A *ᵥ y) := by rw [Matrix.mulVec_sub]
      _ = p ⬝ᵥ (b - b) := by rw [hy', hy]
      _ = 0 := by simp
  -- Decompose `y' = y + (y' - y)` and expand the square.
  have hdecomp : y' = y + (y' - y) := by abel
  have hexp : y' ⬝ᵥ y' = y ⬝ᵥ y + (y' - y) ⬝ᵥ (y' - y) := by
    have hcomm : (y' - y) ⬝ᵥ y = 0 := by rw [dotProduct_comm]; exact horth
    conv_lhs => rw [hdecomp]
    rw [add_dotProduct, dotProduct_add, dotProduct_add, horth, hcomm]
    ring
  have hnn : 0 ≤ (y' - y) ⬝ᵥ (y' - y) := by
    simpa using dotProduct_star_self_nonneg (v := y' - y)
  linarith

/-- Theorem 2.7 assembled: for the augmented system `H = [A, -b]` with `A y = b` and a dual
witness `Aᵀ p = y`, the vector `θ = [y;1]` is in the null space of `H`, the vector
`θ⊥ = [y; -‖y‖₂²] = Hᵀ p` is in the row space of `H`, Eq. (1) holds, and `y` has minimum
ℓ₂ norm among all solutions.

This is the exact content of Theorem 2.7 (paper page 12).  Note that the paper states the
result for an arbitrary solution `y`; the row-space membership of `θ⊥` (and the minimum-norm
statement) requires the dual witness `Aᵀ p = y`, which is precisely the content of
`y = A⁺b`.  We therefore state it as an explicit hypothesis, as it is needed for
`θ⊥ ∈ Row(H)`. -/
theorem theorem27_vector_decomposition (A : Matrix M N ℝ) (b : M → ℝ) (y : N → ℝ) (p : M → ℝ)
    (hy : A *ᵥ y = b) (hp : Aᵀ *ᵥ p = y) :
    augmentedMatrix A b *ᵥ augmentSolution y = 0 ∧
    (augmentedMatrix A b)ᵀ *ᵥ p = rowPerpComponent y ∧
    (1 / (1 + y ⬝ᵥ y)) • (augmentSolution y - rowPerpComponent y) = psiZero ∧
    (∀ y' : N → ℝ, A *ᵥ y' = b → y ⬝ᵥ y ≤ y' ⬝ᵥ y') :=
  ⟨augmentedMatrix_mulVec_augmentSolution A b y hy,
    rowPerpComponent_eq_transpose_mulVec A b y p hy hp,
    augmentSolution_decomposition y,
    min_norm_of_dual_witness A b y p hy hp⟩

end Qatlib.Papers.QLSBeyondCond25.MainResults.LinearAlgebra
