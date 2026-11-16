/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.SingularValueDecomposition
public import Qatlib.Foundations.PPTMatrix.OperatorCones.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section




/-!
# The literal SVD formula for a contraction as an average of two unitaries.

Every square contraction with singular values in [0,1] is the average of two unitaries. The two diagonal phase factors are s ± i√(1−s²), inserted between the actual left and right singular-vector unitaries; their average reconstructs the contraction.
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The literal plus sign in canonical Eq.(5). -/
noncomputable def svdUnitaryPlus (U V : Matrix n n ℂ) (s : n → ℝ) : Matrix n n ℂ :=
  U * diagonal (fun j => (s j : ℂ) + Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) * Vᴴ

/-- The literal minus sign in canonical Eq.(5). -/
noncomputable def svdUnitaryMinus (U V : Matrix n n ℂ) (s : n → ℝ) : Matrix n n ℂ :=
  U * diagonal (fun j => (s j : ℂ) - Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) * Vᴴ

/-- Establishes `phase_plus_mem_unitary`: `(s : ℂ) + Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ) ∈ unitary ℂ`, for the stated parameters. -/
private theorem phase_plus_mem_unitary {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (s : ℂ) + Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ) ∈ unitary ℂ := by
  have hn : ‖s‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs0] using hs1
  apply Unitary.mem_iff_star_mul_self.mpr
  change (starRingEnd ℂ) ((s : ℂ) + Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ)) *
    ((s : ℂ) + Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ)) = 1
  rw [← Complex.normSq_eq_conj_mul_self]
  simpa only [Complex.ofReal_one] using
    congrArg (fun x : ℝ => (x : ℂ))
      (Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hn)

/-- Establishes `phase_minus_mem_unitary`: `(s : ℂ) - Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ) ∈ unitary ℂ`, for the stated parameters. -/
private theorem phase_minus_mem_unitary {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (s : ℂ) - Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ) ∈ unitary ℂ := by
  have hn : ‖s‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs0] using hs1
  apply Unitary.mem_iff_star_mul_self.mpr
  change (starRingEnd ℂ) ((s : ℂ) - Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ)) *
    ((s : ℂ) - Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ)) = 1
  rw [← Complex.normSq_eq_conj_mul_self]
  simpa only [Complex.ofReal_one] using
    congrArg (fun x : ℝ => (x : ℂ))
      (Complex.normSq_ofReal_sub_I_mul_sqrt_one_sub hn)

/-- Establishes `diagonal_mem_unitary_of_forall`: `diagonal d ∈ unitary (Matrix n n ℂ)`, for the stated parameters. -/
private theorem diagonal_mem_unitary_of_forall {d : n → ℂ} (hd : ∀ j, d j ∈ unitary ℂ) :
    diagonal d ∈ unitary (Matrix n n ℂ) := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  exact (hd j).2

/-- Establishes `svdUnitaryPlus_mem`: `svdUnitaryPlus U V s ∈ unitary (Matrix n n ℂ)`, for the stated parameters. -/
theorem svdUnitaryPlus_mem (U V : Matrix n n ℂ) (s : n → ℝ)
    (hU : U ∈ unitary (Matrix n n ℂ)) (hV : V ∈ unitary (Matrix n n ℂ))
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : ∀ j, s j ≤ 1) :
    svdUnitaryPlus U V s ∈ unitary (Matrix n n ℂ) := by
  have hD : diagonal (fun j => (s j : ℂ) +
      Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) ∈ unitary (Matrix n n ℂ) := by
    apply diagonal_mem_unitary_of_forall
    intro j
    exact phase_plus_mem_unitary (hs0 j) (hs1 j)
  change U * diagonal (fun j => (s j : ℂ) +
    Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) * star V ∈ unitary (Matrix n n ℂ)
  exact (unitary (Matrix n n ℂ)).mul_mem
    ((unitary (Matrix n n ℂ)).mul_mem hU hD) (Unitary.star_mem hV)

/-- Establishes `svdUnitaryMinus_mem`: `svdUnitaryMinus U V s ∈ unitary (Matrix n n ℂ)`, for the stated parameters. -/
theorem svdUnitaryMinus_mem (U V : Matrix n n ℂ) (s : n → ℝ)
    (hU : U ∈ unitary (Matrix n n ℂ)) (hV : V ∈ unitary (Matrix n n ℂ))
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : ∀ j, s j ≤ 1) :
    svdUnitaryMinus U V s ∈ unitary (Matrix n n ℂ) := by
  have hD : diagonal (fun j => (s j : ℂ) -
      Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) ∈ unitary (Matrix n n ℂ) := by
    apply diagonal_mem_unitary_of_forall
    intro j
    exact phase_minus_mem_unitary (hs0 j) (hs1 j)
  change U * diagonal (fun j => (s j : ℂ) -
    Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) * star V ∈ unitary (Matrix n n ℂ)
  exact (unitary (Matrix n n ℂ)).mul_mem
    ((unitary (Matrix n n ℂ)).mul_mem hU hD) (Unitary.star_mem hV)

/-- The average identity is purely algebraic, including all zero slots. -/
theorem svdUnitary_average (U V : Matrix n n ℂ) (s : n → ℝ) :
    (1 / 2 : ℂ) • (svdUnitaryPlus U V s + svdUnitaryMinus U V s) =
      U * diagonal (fun j => (s j : ℂ)) * Vᴴ := by
  have hD :
      diagonal (fun j => (s j : ℂ) + Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) +
        diagonal (fun j => (s j : ℂ) - Complex.I * (Real.sqrt (1 - s j ^ 2) : ℂ)) =
      (2 : ℂ) • diagonal (fun j => (s j : ℂ)) := by
    rw [Matrix.diagonal_add, ← Matrix.diagonal_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  unfold svdUnitaryPlus svdUnitaryMinus
  rw [← Matrix.add_mul, ← Matrix.mul_add, hD, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul]
  norm_num

/-- An actual SVD of `Y` has `s_j ≤ 1` when `Y Yᴴ ≤ 1`.
The Loewner inequality is stated with the project's literal PSD definition. -/
theorem svd_coeff_le_one_of_contraction (Y U V : Matrix n n ℂ) (s : n → ℝ)
    (hU : U ∈ unitary (Matrix n n ℂ)) (hV : V ∈ unitary (Matrix n n ℂ))
    (hY : Y = U * diagonal (fun j => (s j : ℂ)) * Vᴴ)
    (hcontraction : (1 - Y * Yᴴ).PosSemidef) : ∀ j, s j ≤ 1 := by
  let D : Matrix n n ℂ := diagonal (fun j => (s j : ℂ))
  change Y = U * D * Vᴴ at hY
  have hD : Dᴴ = D := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    simp
  have hU1 : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have hV1 : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  have hYY : Uᴴ * (Y * Yᴴ) * U = D * D := by
    calc
      Uᴴ * (Y * Yᴴ) * U = Uᴴ * ((U * D * Vᴴ) * (V * D * Uᴴ)) * U := by
        simp only [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
          Matrix.mul_assoc]
      _ = (Uᴴ * U) * D * (Vᴴ * V) * D * (Uᴴ * U) := by
        simp only [Matrix.mul_assoc]
      _ = D * D := by rw [hU1, hV1]; simp
  have hDD : D * D = diagonal (fun j => (s j : ℂ) ^ 2) := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    exact (pow_two (s j : ℂ)).symm
  have hdiag : (diagonal (fun j => (1 : ℂ) - (s j : ℂ) ^ 2)).PosSemidef := by
    have h := hcontraction.conjTranspose_mul_mul_same U
    have heq : Uᴴ * (1 - Y * Yᴴ) * U =
        diagonal (fun j => (1 : ℂ) - (s j : ℂ) ^ 2) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1, hYY, hDD]
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rw [heq] at h
    exact h
  intro j
  have hc : (0 : ℂ) ≤ (1 : ℂ) - (s j : ℂ) ^ 2 :=
    (Matrix.posSemidef_diagonal_iff.mp hdiag) j
  have heq : ((1 - s j ^ 2 : ℝ) : ℂ) = (1 : ℂ) - (s j : ℂ) ^ 2 := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  rw [← heq] at hc
  have hr : 0 ≤ 1 - s j ^ 2 := Complex.zero_le_real.mp hc
  nlinarith [sq_nonneg (s j - 1)]

/-- Literal Eq.(5) for genuine SVD factors; all matrices have the same index type.
The existence of such `U,V,s` is proved separately (`exists_svd_two_unitary_formula`
below); no enlarged-space dilation is used. -/
theorem svd_two_unitary_formula (Y U V : Matrix n n ℂ) (s : n → ℝ)
    (hU : U ∈ unitary (Matrix n n ℂ)) (hV : V ∈ unitary (Matrix n n ℂ))
    (hs : ∀ j, 0 ≤ s j)
    (hY : Y = U * diagonal (fun j => (s j : ℂ)) * Vᴴ)
    (hcontraction : (1 - Y * Yᴴ).PosSemidef) :
    svdUnitaryPlus U V s ∈ unitary (Matrix n n ℂ) ∧
      svdUnitaryMinus U V s ∈ unitary (Matrix n n ℂ) ∧
      Y = (1 / 2 : ℂ) • (svdUnitaryPlus U V s + svdUnitaryMinus U V s) := by
  have hs1 := svd_coeff_le_one_of_contraction Y U V s hU hV hY hcontraction
  exact ⟨svdUnitaryPlus_mem U V s hU hV hs hs1,
    svdUnitaryMinus_mem U V s hU hV hs hs1,
    hY.trans (svdUnitary_average U V s).symm⟩

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Canonical Eq.(5), including the existence of its same-space SVD factors
and the literal square-root formula for its two unitary matrices. -/
theorem exists_svd_two_unitary_formula (Y : Matrix n n ℂ)
    (hcontraction : (1 - Y * Yᴴ).PosSemidef) :
    ∃ (U V : Matrix n n ℂ) (s : n → ℝ),
      U ∈ unitary (Matrix n n ℂ) ∧ V ∈ unitary (Matrix n n ℂ) ∧
      (∀ j, 0 ≤ s j) ∧ (∀ j, s j ≤ 1) ∧
      Y = U * diagonal (fun j => (s j : ℂ)) * Vᴴ ∧
      svdUnitaryPlus U V s ∈ unitary (Matrix n n ℂ) ∧
      svdUnitaryMinus U V s ∈ unitary (Matrix n n ℂ) ∧
      Y = (1 / 2 : ℂ) • (svdUnitaryPlus U V s + svdUnitaryMinus U V s) := by
  obtain ⟨U, V, s, hU, hV, hs, hY⟩ := exists_square_svd Y
  exact ⟨U, V, s, hU, hV, hs,
    svd_coeff_le_one_of_contraction Y U V s hU hV hY hcontraction,
    hY, svd_two_unitary_formula Y U V s hU hV hs hY hcontraction⟩

/-- The same-space two-unitary average as a direct existential consequence. -/
theorem exists_two_unitaries_average (Y : Matrix n n ℂ)
    (hcontraction : (1 - Y * Yᴴ).PosSemidef) :
    ∃ Wplus Wminus : Matrix n n ℂ,
      Wplus ∈ unitary (Matrix n n ℂ) ∧ Wminus ∈ unitary (Matrix n n ℂ) ∧
      Y = (1 / 2 : ℂ) • (Wplus + Wminus) := by
  obtain ⟨U, V, s, _, _, _, _, _, hplus, hminus, havg⟩ :=
    exists_svd_two_unitary_formula Y hcontraction
  exact ⟨svdUnitaryPlus U V s, svdUnitaryMinus U V s, hplus, hminus, havg⟩

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD
