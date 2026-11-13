/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs

/-!
# Theorem 11 Hermitian block embedding

This module defines `blockHam U` with off-diagonal blocks `U` and `U.conjTranspose`, proves its
block entries and Hermitian property, and shows that it is a unitary involution when `U` is
unitary. The result `theorem11_exact_unitary_implementation` collects these matrix identities
with scalar parameter and cost comparisons for `Λmax ≤ X ≤ 2 * Λmax`.

These algebraic ingredients accompany the unitary implementation analysis of Theorem 11 in
[BerryChilds2012].

## Main statements

* `blockHam_sq` proves the block embedding is an involution for unitary input.
* `theorem11_exact_unitary_implementation` collects the block identities and scalar comparisons.

## References

* [Berry and Childs, 2012][BerryChilds2012]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Unitary

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

/-- The Hermitian block matrix with zero diagonal blocks and off-diagonal blocks `U` and
`U.conjTranspose`. -/
def blockHam {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 0 U U.conjTranspose 0

/-- The upper-left block of `blockHam U` is zero. -/
theorem blockHam_apply_inl_inl {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    blockHam U (Sum.inl i) (Sum.inl j) = 0 := by
  unfold blockHam
  rw [Matrix.fromBlocks_apply₁₁]
  rfl

/-- The upper-right block of `blockHam U` is `U`. See [Berry and Childs, Theorem
11][BerryChilds2012]. -/
theorem blockHam_apply_inl_inr {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    blockHam U (Sum.inl i) (Sum.inr j) = U i j := by
  unfold blockHam
  rw [Matrix.fromBlocks_apply₁₂]

/-- The lower-left entry of `blockHam U` at indices `i, j` is the conjugate of `U j i`. -/
theorem blockHam_apply_inr_inl {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    blockHam U (Sum.inr i) (Sum.inl j) = star (U j i) := by
  unfold blockHam
  rw [Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]

/-- The lower-right block of `blockHam U` is zero. -/
theorem blockHam_apply_inr_inr {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    blockHam U (Sum.inr i) (Sum.inr j) = 0 := by
  unfold blockHam
  rw [Matrix.fromBlocks_apply₂₂]
  rfl

/-- The block embedding `blockHam U` is Hermitian for every complex matrix `U`. See [Berry and
Childs, Theorem 11][BerryChilds2012]. -/
theorem blockHam_isHermitian {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) :
    (blockHam U).IsHermitian := by
  unfold blockHam
  rw [Matrix.isHermitian_fromBlocks_iff]
  exact ⟨Matrix.isHermitian_zero, rfl, Matrix.conjTranspose_conjTranspose U,
    Matrix.isHermitian_zero⟩

/-- For unitary `U`, the block embedding satisfies `blockHam U * blockHam U = 1`. See [Berry and
Childs, Theorem 11][BerryChilds2012]. -/
theorem blockHam_sq {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    blockHam U * blockHam U = 1 := by
  unfold blockHam
  rw [Matrix.fromBlocks_multiply]
  have h1 : U * U.conjTranspose = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hU
    simpa [Matrix.star_eq_conjTranspose] using! this
  have h2 : U.conjTranspose * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU
    simpa [Matrix.star_eq_conjTranspose] using! this
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, h1, h2]
  rw [Matrix.fromBlocks_one]

/-- For unitary `U`, its Hermitian block embedding is also unitary. See [Berry and Childs,
Theorem 11][BerryChilds2012]. -/
theorem blockHam_mem_unitaryGroup {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    blockHam U ∈ Matrix.unitaryGroup (Fin N ⊕ Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [show star (blockHam U) = blockHam U by
    rw [Matrix.star_eq_conjTranspose]
    exact (blockHam_isHermitian U).eq]
  exact blockHam_sq U hU

/-- For positive `N`, `Λ1`, and `Λmax`, any `X ≥ Λmax` satisfies `Λ1 / (N * X) ≤ Λ1 / (N *
Λmax)`. See [Berry and Childs, Theorem 11][BerryChilds2012]. -/
theorem theorem11_eps_le {N : ℕ} {Λ1 Λmax X : ℝ} (hN : 0 < N) (hΛ1 : 0 < Λ1)
    (hΛmax : 0 < Λmax) (hX : Λmax ≤ X) :
    Λ1 / ((N : ℝ) * X) ≤ Λ1 / ((N : ℝ) * Λmax) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hX0 : 0 < X := lt_of_lt_of_le hΛmax hX
  rw [div_le_div_iff₀ (mul_pos hNpos hX0) (mul_pos hNpos hΛmax)]
  have hkey : Λ1 * ((N : ℝ) * Λmax) ≤ Λ1 * ((N : ℝ) * X) := by
    gcongr
  linarith

/-- For positive `N`, `Λmax`, and `c`, the bound `X ≤ 2 * Λmax` implies `c * (N * X) ≤ (2 * c) *
(N * Λmax)`. See [Berry and Childs, Theorem 11][BerryChilds2012]. -/
theorem theorem11_query_transfer {N : ℕ} {Λmax X c : ℝ} (hN : 0 < N) (hΛmax : 0 < Λmax)
    (hc : 0 < c) (hX : X ≤ 2 * Λmax) :
    c * ((N : ℝ) * X) ≤ (2 * c) * ((N : ℝ) * Λmax) := by
  have hNpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [hc, hΛmax, hNpos, mul_nonneg hNpos (le_of_lt hΛmax),
    mul_le_mul_of_nonneg_left hX (mul_nonneg (le_of_lt hc) hNpos)]

/-- For unitary `U` and `Λmax ≤ X ≤ 2 * Λmax`, collect the Hermitian, involution, unitary, and
block entry properties of `blockHam U` with the scalar parameter and cost comparisons. These
are algebraic ingredients for Theorem 11 of [BerryChilds2012]. -/
theorem theorem11_exact_unitary_implementation
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hN : 0 < N) {Λmax : ℝ} (hΛmax : unitaryMaxEntry U ≤ Λmax) (hΛmax0 : 0 < Λmax)
    {Λ1 X : ℝ} (hΛ1 : 0 < Λ1) (hX : Λmax ≤ X) (hX2 : X ≤ 2 * Λmax) :
    (blockHam U).IsHermitian ∧ blockHam U * blockHam U = 1 ∧
      blockHam U ∈ Matrix.unitaryGroup (Fin N ⊕ Fin N) ℂ ∧
      (∀ i j : Fin N, blockHam U (Sum.inl i) (Sum.inl j) = 0) ∧
      (∀ i j : Fin N, blockHam U (Sum.inl i) (Sum.inr j) = U i j) ∧
      (∀ i j : Fin N, blockHam U (Sum.inr i) (Sum.inl j) = star (U j i)) ∧
      (∀ i j : Fin N, blockHam U (Sum.inr i) (Sum.inr j) = 0) ∧
      Λ1 / ((N : ℝ) * X) ≤ Λ1 / ((N : ℝ) * Λmax) ∧
      (∀ c : ℝ, 0 < c → c * ((N : ℝ) * X) ≤ (2 * c) * ((N : ℝ) * Λmax)) := by
  refine ⟨blockHam_isHermitian U, blockHam_sq U hU, blockHam_mem_unitaryGroup U hU,
    blockHam_apply_inl_inl U, blockHam_apply_inl_inr U, blockHam_apply_inr_inl U,
    blockHam_apply_inr_inr U, theorem11_eps_le hN hΛ1 hΛmax0 hX, ?_⟩
  intro c hc
  exact theorem11_query_transfer hN hΛmax0 hc hX2

end Qatlib.Papers.BlackBoxHam09.MainResults.Unitary
