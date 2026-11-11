/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Elementary Temperley-Lieb projector and product identities

An explicit two-dimensional projector satisfies idempotence and specified
actions on two vectors. Scaling it by `d` gives the relation `E² = d E`.
The remaining lemmas separate distinct odd indices and show that a product of
odd-indexed factors vanishes whenever one of those factors is zero.

These are elementary ingredients for the Jones-polynomial framework of
[AharonovJonesLandau2009]; see
[Aharonov, Jones & Landau, the path-model construction][AharonovJonesLandau2009].
This module proves the displayed low-dimensional and product identities.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.JonesPoly06.MainResults

/-- The diagonal 2 × 2 matrix with entries zero and one. -/
def tlE1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The diagonal 2 × 2 matrix projecting onto the second coordinate. -/
def tlT2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The matrix `tlT2` is idempotent. -/
theorem tlT2_idem : tlT2 * tlT2 = tlT2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tlT2, Matrix.mul_apply]

/-- The matrix `tlE1` is idempotent. -/
theorem tlE1_idem : tlE1 * tlE1 = tlE1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tlE1, Matrix.mul_apply]

/-- The first standard coordinate vector (1, 0). -/
def rowVec : Fin 2 → ℂ := ![1, 0]

/-- The second standard coordinate vector (0, 1). -/
def colVec : Fin 2 → ℂ := ![0, 1]

/-- The matrix `tlE1` annihilates `rowVec`. -/
theorem tlE1_mul_row : tlE1 *ᵥ rowVec = 0 := by
  ext i
  fin_cases i <;>
    simp [tlE1, rowVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The matrix `tlE1` fixes `colVec`. -/
theorem tlE1_mul_col : tlE1 *ᵥ colVec = colVec := by
  ext i
  fin_cases i <;>
    simp [tlE1, colVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The explicit two-dimensional projector has the scaled idempotence and
vector actions used in the Temperley-Lieb setting of
[Aharonov, Jones & Landau][AharonovJonesLandau2009]. -/
theorem SourceLemma51_two (d : ℂ) :
    (d • tlE1 = d • tlT2) ∧
    ((d • tlE1) * (d • tlE1) = d • (d • tlE1)) ∧
    ((d • tlE1) *ᵥ rowVec = 0) ∧
    ((d • tlE1) *ᵥ colVec = d • colVec) := by
  refine ⟨by rw [tlE1, tlT2], ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, tlE1_idem]
  · rw [Matrix.smul_mulVec, tlE1_mul_row, smul_zero]
  · rw [Matrix.smul_mulVec, tlE1_mul_col]

/-- Distinct natural indices give odd indices separated by more than one, in one of the two
possible orders; see [WocjanYard2006]. -/
theorem odd_indices_not_adjacent {i j : ℕ} (h : i ≠ j) :
    (2 * i + 1) + 1 < 2 * j + 1 ∨ (2 * j + 1) + 1 < 2 * i + 1 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- The ordered product of E at the first p positive odd indices. -/
def oddProd {R : Type*} [Monoid R] (p : ℕ) (E : ℕ → R) : R :=
  ((List.range p).map (fun j => E (2 * j + 1))).prod

/-- A list in a monoid with zero has zero product if one of its entries is zero. -/
theorem list_prod_eq_zero_of_mem {M : Type*} [MonoidWithZero M] :
    ∀ {l : List M} {a : M}, a ∈ l → a = 0 → l.prod = 0
  | [], _, hmem, _ => by simp at hmem
  | b :: l, a, hmem, ha => by
      rw [List.prod_cons]
      rcases List.mem_cons.mp hmem with rfl | htl
      · rw [ha, zero_mul]
      · rw [list_prod_eq_zero_of_mem htl ha, mul_zero]

/-- If one of the first p odd-indexed factors is zero, then `oddProd p E` is zero; see
[WocjanYard2006]. -/
theorem oddProd_zero_of_factor {R : Type*} [MonoidWithZero R] (p : ℕ) (E : ℕ → R)
    (i : ℕ) (hi : i < p) (h : E (2 * i + 1) = 0) : oddProd p E = 0 := by
  unfold oddProd
  have hmem : E (2 * i + 1) ∈ (List.range p).map (fun j => E (2 * j + 1)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  exact list_prod_eq_zero_of_mem hmem h

end Qatlib.Papers.JonesPoly06.MainResults
