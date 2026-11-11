/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceDiracOperator — the Hermitian boundary operator and its square

Lloyd--Garnerone--Zanardi, *Quantum algorithms for topological and geometric analysis of
big data*, fixed arXiv:1408.3106v1 (2014).

Section 2, Eq. (6) (PDF p. 12): the boundary map `∂_k` is not Hermitian, so it is embedded
in the Hermitian matrix

  `B_k = [[0, ∂_k], [∂_k†, 0]]`,

which acts on `W_{k-1} ⊕ W_k`. Section 3, Eqs. (9)--(10) (PDF p. 14): the full graded
boundary operator `B^ε` has `∂̃_k` on the superdiagonal and `∂̃_k†` on the subdiagonal,
and, because `∂̃_k ∂̃_{k+1} = 0`, its square is block diagonal,

  `B^{ε²} = ∆_0 ⊕ ∆_1 ⊕ … ⊕ ∆_n`,
  `∆_k = ∂̃_k† ∂̃_k + ∂̃_{k+1} ∂̃_{k+1}†`.

This file formalises the two algebraic facts behind Eqs. (6) and (10), in matrix language:

* `diracBlock p` is the two-block matrix `[[0, p], [pᴴ, 0]]` of Eq. (6); it is Hermitian
  (`diracBlock_conjTranspose`) and its square is the diagonal matrix
  `[[p pᴴ, 0], [0, pᴴ p]]` (`diracBlock_mul_self`), the pair of diagonal blocks appearing
  in Eq. (10);
* `gradedDirac3 p q` is the three-degree window
  `[[0, p, 0], [pᴴ, 0, q], [0, qᴴ, 0]]` of Eq. (9) on degrees `(k-1, k, k+1)`; it is
  Hermitian (`gradedDirac3_conjTranspose`) and, **under the chain condition**
  `p * q = 0` (`∂_k ∂_{k+1} = 0`), its square is block diagonal with diagonal blocks
  `p pᴴ` (degree `k-1`), `pᴴ p + q qᴴ = ∆_k` (degree `k`) and `qᴴ q` (degree `k+1`)
  (`gradedDirac3_mul_self`). The chain condition is exactly what kills the two
  off-diagonal blocks; assembling this identity over all `k` gives
  `B^{ε²} = ⊕_k ∆_k`.

Indexing: `α` indexes degree `k-1`, `β` indexes degree `k`, `γ` indexes degree `k+1`;
`p : Matrix α β` is `∂_k` (rows `k-1`, columns `k`) and `q : Matrix β γ` is `∂_{k+1}`.

Boundary: this file proves the block-linear-algebra identities of Eqs. (6), (9), (10)
for an abstract boundary pair. It does not formalise the concrete sign rule of Eq. (5),
the projectors `P^ε` onto the simplicial subspace, nor the quantum phase-estimation
algorithm that is applied to `B^ε`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TopoData14.MainResults

open Matrix

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ## Eq. (6): the two-block Hermitian boundary operator -/

/-- Fixed arXiv:1408.3106v1, Eq. (6) (PDF p. 12): the Hermitian embedding
`B_k = [[0, ∂_k], [∂_k†, 0]]` of the boundary map `p = ∂_k`, acting on
`W_{k-1} ⊕ W_k` (here `α` indexes `W_{k-1}`, `β` indexes `W_k`). -/
def diracBlock (p : Matrix α β ℂ) : Matrix (α ⊕ β) (α ⊕ β) ℂ :=
  fromBlocks 0 p (conjTranspose p) 0

omit [Fintype α] [Fintype β] in
/-- Fixed arXiv:1408.3106v1, Eq. (6) (PDF p. 12): `B_k` is Hermitian,
`B_k† = B_k`, which is what makes it a valid input for the quantum phase algorithm. -/
theorem diracBlock_conjTranspose (p : Matrix α β ℂ) :
    (diracBlock p)ᴴ = diracBlock p := by
  unfold diracBlock
  rw [fromBlocks_conjTranspose]
  simp [conjTranspose_conjTranspose]

/-- Fixed arXiv:1408.3106v1, Eq. (6) and Eq. (10) (PDF p. 12, 14): the square of the
two-block Hermitian boundary operator is block diagonal,
`B_k² = [[∂_k ∂_k†, 0], [0, ∂_k† ∂_k]]`. The two diagonal blocks are the degree-`k-1`
and degree-`k` pieces of the combinatorial Laplacian of Eq. (10). -/
theorem diracBlock_mul_self (p : Matrix α β ℂ) :
    diracBlock p * diracBlock p =
      fromBlocks (p * conjTranspose p) 0 0 (conjTranspose p * p) := by
  unfold diracBlock
  rw [fromBlocks_multiply]
  simp [mul_zero, add_zero, zero_add]

/-! ## Eqs. (9)--(10): the graded boundary operator on a three-degree window -/

/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): the upper off-diagonal block of the graded
operator `B^ε`: in the window
of degrees `(k-1, k, k+1)` it carries `q = ∂_{k+1}` from degree `k` to degree `k+1` and
is zero on the degree-`k-1` rows. -/
def dirac3Upper (q : Matrix β γ ℂ) : Matrix (α ⊕ β) γ ℂ :=
  of fun i j => match i with
    | Sum.inl _ => 0
    | Sum.inr b => q b j

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): evaluation of the upper off-diagonal
block on a degree-`k-1` row is zero. -/
theorem dirac3Upper_apply_inl (q : Matrix β γ ℂ) (a : α) (j : γ) :
    dirac3Upper (α := α) q (Sum.inl a) j = 0 := rfl

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): evaluation of the upper off-diagonal
block on a degree-`k` row is the boundary entry `q b j`. -/
theorem dirac3Upper_apply_inr (q : Matrix β γ ℂ) (b : β) (j : γ) :
    dirac3Upper (α := α) q (Sum.inr b) j = q b j := rfl

/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): the lower off-diagonal block of the graded
operator `B^ε`: in the window
of degrees `(k-1, k, k+1)` it carries `q† = ∂_{k+1}†` from degree `k+1` to degree `k` and
is zero on the degree-`k-1` columns. -/
def dirac3Lower (q : Matrix β γ ℂ) : Matrix γ (α ⊕ β) ℂ :=
  of fun i j => match j with
    | Sum.inl _ => 0
    | Sum.inr b => conjTranspose q i b

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): evaluation of the lower off-diagonal
block on a degree-`k-1` column is zero. -/
theorem dirac3Lower_apply_inl (q : Matrix β γ ℂ) (i : γ) (a : α) :
    dirac3Lower (α := α) q i (Sum.inl a) = 0 := rfl

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): evaluation of the lower off-diagonal
block on a degree-`k` column is the conjugate boundary entry `(q b i)*`. -/
theorem dirac3Lower_apply_inr (q : Matrix β γ ℂ) (i : γ) (b : β) :
    dirac3Lower (α := α) q i (Sum.inr b) = conjTranspose q i b := rfl

/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the block of `B^ε * B^ε` sitting in
the degree-`k-1` rows and degree-`k+1` columns:
a matrix supported on the `α` rows only. -/
def dirac3UpperLeft (r : Matrix α γ ℂ) : Matrix (α ⊕ β) γ ℂ :=
  of fun i j => match i with
    | Sum.inl a => r a j
    | Sum.inr _ => 0

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the `α`-row-supported block,
evaluated on a degree-`k-1` row, is the entry `r a j`. -/
theorem dirac3UpperLeft_apply_inl (r : Matrix α γ ℂ) (a : α) (j : γ) :
    dirac3UpperLeft (β := β) r (Sum.inl a) j = r a j := rfl

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the `α`-row-supported block
vanishes on the degree-`k` rows. -/
theorem dirac3UpperLeft_apply_inr (r : Matrix α γ ℂ) (b : β) (j : γ) :
    dirac3UpperLeft (β := β) r (Sum.inr b) j = 0 := rfl

/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the block of `B^ε * B^ε` sitting in
the degree-`k+1` rows and degree-`k-1` columns:
a matrix supported on the `α` columns only. -/
def dirac3LowerLeft (s : Matrix γ α ℂ) : Matrix γ (α ⊕ β) ℂ :=
  of fun i j => match j with
    | Sum.inl a => s i a
    | Sum.inr _ => 0

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the `α`-column-supported block,
evaluated on a degree-`k-1` column, is `s i a`. -/
theorem dirac3LowerLeft_apply_inl (s : Matrix γ α ℂ) (i : γ) (a : α) :
    dirac3LowerLeft (β := β) s i (Sum.inl a) = s i a := rfl

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the `α`-column-supported block
vanishes on the degree-`k` columns. -/
theorem dirac3LowerLeft_apply_inr (s : Matrix γ α ℂ) (i : γ) (b : β) :
    dirac3LowerLeft (β := β) s i (Sum.inr b) = 0 := rfl

/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): the graded Hermitian boundary operator
`B^ε` restricted to three consecutive degrees `(k-1, k, k+1)`,
`[[0, p, 0], [p†, 0, q], [0, q†, 0]]`, where `p = ∂_k` and `q = ∂_{k+1}`. -/
def gradedDirac3 (p : Matrix α β ℂ) (q : Matrix β γ ℂ) :
    Matrix ((α ⊕ β) ⊕ γ) ((α ⊕ β) ⊕ γ) ℂ :=
  fromBlocks (diracBlock p) (dirac3Upper q) (dirac3Lower q) 0

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): the conjugate transpose of the upper
off-diagonal block is the lower one, `(∂_{k+1})ᴴ = ∂_{k+1}†`. -/
theorem dirac3Upper_conjTranspose (q : Matrix β γ ℂ) :
    (dirac3Upper (α := α) q)ᴴ = dirac3Lower (α := α) q := by
  ext i j
  rcases j with a | b <;>
    simp [dirac3Upper, dirac3Lower, conjTranspose_apply]

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): the conjugate transpose of the lower
off-diagonal block is the upper one, `(∂_{k+1}†)ᴴ = ∂_{k+1}`. -/
theorem dirac3Lower_conjTranspose (q : Matrix β γ ℂ) :
    (dirac3Lower (α := α) q)ᴴ = dirac3Upper (α := α) q := by
  rw [← dirac3Upper_conjTranspose]
  simp

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Fixed arXiv:1408.3106v1, Eq. (9) (PDF p. 14): the graded boundary operator `B^ε` is
Hermitian on the three-degree window. -/
theorem gradedDirac3_conjTranspose (p : Matrix α β ℂ) (q : Matrix β γ ℂ) :
    (gradedDirac3 p q)ᴴ = gradedDirac3 p q := by
  unfold gradedDirac3
  rw [fromBlocks_conjTranspose]
  simp [diracBlock_conjTranspose, dirac3Upper_conjTranspose, dirac3Lower_conjTranspose]

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the upper off-diagonal block is
zero for the zero boundary map. -/
theorem dirac3Upper_zero : dirac3Upper (α := α) (0 : Matrix β γ ℂ) = 0 := by
  ext i j
  rcases i with a | b <;> simp [dirac3Upper]

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the lower off-diagonal block is
zero for the zero boundary map. -/
theorem dirac3Lower_zero : dirac3Lower (α := α) (0 : Matrix β γ ℂ) = 0 := by
  ext i j
  rcases j with a | b <;> simp [dirac3Lower]

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the `α`-supported square block is
zero for the zero composite boundary. -/
theorem dirac3UpperLeft_zero : dirac3UpperLeft (β := β) (0 : Matrix α γ ℂ) = 0 := by
  ext i j
  rcases i with a | b <;> simp [dirac3UpperLeft]

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the `α`-column-supported square
block is zero for the zero composite boundary. -/
theorem dirac3LowerLeft_zero : dirac3LowerLeft (β := β) (0 : Matrix γ α ℂ) = 0 := by
  ext i j
  rcases j with a | b <;> simp [dirac3LowerLeft]

/-! ### Blockwise products used in the square identity -/

omit [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the two-block Dirac matrix times
the upper off-diagonal block is the `α`-supported block of the composite boundary `p * q`. -/
theorem diracBlock_mul_dirac3Upper (p : Matrix α β ℂ) (q : Matrix β γ ℂ) :
    diracBlock p * dirac3Upper (α := α) q = dirac3UpperLeft (β := β) (p * q) := by
  ext i j
  rcases i with a | b <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, diracBlock, dirac3Upper, dirac3UpperLeft]

omit [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): the lower off-diagonal block times
the two-block Dirac matrix is the `α`-column-supported block of `(p * q)ᴴ`. -/
theorem dirac3Lower_mul_diracBlock (p : Matrix α β ℂ) (q : Matrix β γ ℂ) :
    dirac3Lower (α := α) q * diracBlock p =
      dirac3LowerLeft (β := β) (conjTranspose (p * q)) := by
  ext i j
  rcases j with a | b <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, diracBlock, dirac3Lower,
      dirac3LowerLeft, conjTranspose_apply, mul_comm]

omit [Fintype α] [Fintype β] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): upper off-diagonal block times
lower off-diagonal block is `q * qᴴ`, the degree-`k` diagonal position. -/
theorem dirac3Upper_mul_dirac3Lower (q : Matrix β γ ℂ) :
    dirac3Upper (α := α) q * dirac3Lower (α := α) q =
      fromBlocks 0 0 0 (q * conjTranspose q) := by
  ext i j
  rcases i with a | b <;> rcases j with a' | b' <;>
    simp [Matrix.mul_apply, dirac3Upper, dirac3Lower, conjTranspose_apply]

omit [Fintype γ] in
/-- Supports Eq. (10), fixed arXiv:1408.3106v1 (PDF p. 14): lower off-diagonal block times
upper off-diagonal block is `qᴴ * q`, the degree-`k+1` diagonal block. -/
theorem dirac3Lower_mul_dirac3Upper (q : Matrix β γ ℂ) :
    dirac3Lower (α := α) q * dirac3Upper (α := α) q = conjTranspose q * q := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, dirac3Upper, dirac3Lower,
    conjTranspose_apply]

/-- Fixed arXiv:1408.3106v1, Eq. (10) (PDF p. 14): on the three-degree window, the chain
condition `∂_k ∂_{k+1} = 0` (`p * q = 0`) makes the square of the graded Hermitian
boundary operator block diagonal, with diagonal blocks `p pᴴ`, `pᴴ p + q qᴴ = ∆_k` and
`qᴴ q`. This is the local form of `B^{ε²} = ∆_0 ⊕ … ⊕ ∆_n`. -/
theorem gradedDirac3_mul_self (p : Matrix α β ℂ) (q : Matrix β γ ℂ)
    (hchain : p * q = 0) :
    gradedDirac3 p q * gradedDirac3 p q =
      fromBlocks (fromBlocks (p * conjTranspose p) 0 0
        (conjTranspose p * p + q * conjTranspose q)) 0 0 (conjTranspose q * q) := by
  unfold gradedDirac3
  rw [fromBlocks_multiply]
  have h11 : diracBlock p * diracBlock p =
      fromBlocks (p * conjTranspose p) 0 0 (conjTranspose p * p) :=
    diracBlock_mul_self p
  have h12 : diracBlock p * dirac3Upper (α := α) q = 0 := by
    rw [diracBlock_mul_dirac3Upper, hchain, dirac3UpperLeft_zero]
  have h21 : dirac3Lower (α := α) q * diracBlock p = 0 := by
    rw [dirac3Lower_mul_diracBlock, hchain, conjTranspose_zero, dirac3LowerLeft_zero]
  have h22 : dirac3Upper (α := α) q * dirac3Lower (α := α) q =
      fromBlocks 0 0 0 (q * conjTranspose q) :=
    dirac3Upper_mul_dirac3Lower q
  have h33 : dirac3Lower (α := α) q * dirac3Upper (α := α) q =
      conjTranspose q * q :=
    dirac3Lower_mul_dirac3Upper q
  simp only [h11, h12, h21, h22, h33, mul_zero, add_zero, zero_add]
  rw [fromBlocks_add]
  simp

end Qatlib.Papers.TopoData14.MainResults
