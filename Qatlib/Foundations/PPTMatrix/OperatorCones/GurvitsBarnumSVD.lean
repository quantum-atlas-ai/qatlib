/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.TwoUnitaryFormula
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.UnitaryEigenbasis
public import Qatlib.Foundations.PPTMatrix.OperatorCones.QubitNormalization

@[expose] public section




/-!
# Equal-diagonal separability through the two-unitary formula and eigenbasis identity.

Normalize a positive block matrix with equal diagonal corners on the support of that corner. The normalized off-diagonal contraction is the average of two unitaries; their eigenbasis product decompositions prove separability. Local filtering transports the result back, including singular corners.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptGB

/-- Establishes `separable_system_submatrix`: `IsSeparable (X.submatrix (fun x : κ × m => (x.1, f x.2)) (fun x : κ × m => (x.1, f x.2)))`, for the stated parameters. -/
private theorem separable_system_submatrix {κ n m : Type*}
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : IsSeparable X) (f : m → n) :
    IsSeparable (X.submatrix (fun x : κ × m => (x.1, f x.2))
      (fun x : κ × m => (x.1, f x.2))) := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := hX
  refine ⟨N, A, fun j => (B j).submatrix f f, hA,
    fun j => (hB j).submatrix f, ?_⟩
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kronecker_apply]

/-- Establishes `qubitBlocks_system_submatrix`: `(qubitBlocks A B C D).submatrix (fun x : Fin 2 × m => (x.1, f x.2)) (fun x : Fin 2 × m => (x.1, f x.2)) = qubitBlocks (A.submatrix f f) (B.submatrix f f) (C.submatrix f f) (D.submatrix f f)`, for the stated parameters. -/
private theorem qubitBlocks_system_submatrix {n m : Type*} (f : m → n)
    (A B C D : Matrix n n ℂ) :
    (qubitBlocks A B C D).submatrix (fun x : Fin 2 × m => (x.1, f x.2))
      (fun x : Fin 2 × m => (x.1, f x.2)) =
        qubitBlocks (A.submatrix f f) (B.submatrix f f)
          (C.submatrix f f) (D.submatrix f f) := by
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Establishes `separable_smul_nonneg`: `IsSeparable (c • X)`, for the stated parameters. -/
private theorem separable_smul_nonneg {κ n : Type*}
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : IsSeparable X)
    (c : ℂ) (hc : 0 ≤ c) : IsSeparable (c • X) := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := hX
  refine ⟨N, fun j => c • A j, B, fun j => (hA j).smul hc, hB, ?_⟩
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (Matrix.smul_kronecker c (A j) (B j)).symm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eq.(6)'s separability consequence transported from Fin d to any finite
index type. This is a coordinate renaming, not a doubled-space dilation. -/
theorem isSeparable_unitary_block (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) :
    IsSeparable (qubitBlocks (1 : Matrix n n ℂ) W Wᴴ 1) := by
  classical
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let Wf : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    W.submatrix e.symm e.symm
  have hWf : Wfᴴ * Wf = 1 := by
    change (W.submatrix e.symm e.symm)ᴴ * W.submatrix e.symm e.symm = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      hW, Matrix.submatrix_one_equiv]
  have hFin := ManuscriptEigenbasis.isSeparable_qubit_unitary_from_eigenbasis
    (Fintype.card n) Wf hWf
  have hBack := separable_system_submatrix hFin e
  rw [qubitBlocks_system_submatrix] at hBack
  simp [Wf, Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
    Function.comp_def] at hBack
  have hid (A : Matrix n n ℂ) :
      A.submatrix (fun x => x) (fun x => x) = A := by
    apply Matrix.ext
    intro i j
    rfl
  simpa only [hid] using hBack

/-- The identity-diagonal case, through the actual SVD formulas for W₊,W₋
and the literal eigenbasis product decomposition for each of those unitaries. -/
theorem isSeparable_identity_block_of_contraction (Y : Matrix n n ℂ)
    (hcontraction : (1 - Y * Yᴴ).PosSemidef) :
    IsSeparable (qubitBlocks (1 : Matrix n n ℂ) Y Yᴴ 1) := by
  obtain ⟨Wplus, Wminus, hplus, hminus, hY⟩ :=
    ManuscriptSVD.exists_two_unitaries_average Y hcontraction
  have hplusSep := isSeparable_unitary_block Wplus (Unitary.star_mul_self_of_mem hplus)
  have hminusSep := isSeparable_unitary_block Wminus (Unitary.star_mul_self_of_mem hminus)
  have hhalf : (0 : ℂ) ≤ 1 / 2 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      using (Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  have hSep := separable_smul_nonneg (hplusSep.add hminusSep) (1 / 2 : ℂ) hhalf
  have hdiag : (1 / 2 : ℂ) • ((1 : Matrix n n ℂ) + 1) = 1 := by module
  have hadj : (1 / 2 : ℂ) • (Wplusᴴ + Wminusᴴ) = Yᴴ := by
    rw [hY, Matrix.conjTranspose_smul, Matrix.conjTranspose_add]
    simp
  have hblocks : (1 / 2 : ℂ) •
      (qubitBlocks (1 : Matrix n n ℂ) Wplus Wplusᴴ 1 + qubitBlocks 1 Wminus Wminusᴴ 1) =
        qubitBlocks (1 : Matrix n n ℂ) Y Yᴴ 1 := by
    rw [← qubitBlocks_add, ← qubitBlocks_smul, hdiag, ← hY, hadj]
  exact hblocks ▸ hSep

/-- Establishes `support_projection_idempotent`: `(D * pinv D) * (D * pinv D) = D * pinv D`, for the stated parameters. -/
private theorem support_projection_idempotent (D : Matrix n n ℂ)
    (hD : D.IsHermitian) : (D * pinv D) * (D * pinv D) = D * pinv D := by
  calc
    (D * pinv D) * (D * pinv D) = (D * pinv D * D) * pinv D := by
      simp only [Matrix.mul_assoc]
    _ = D * pinv D := by rw [mul_pinv_mul hD]

/-- Establishes `support_complement_posSemidef`: `(1 - D * pinv D).PosSemidef`, for the stated parameters. -/
private theorem support_complement_posSemidef (D : Matrix n n ℂ)
    (hD : D.IsHermitian) : (1 - D * pinv D).PosSemidef := by
  have hP := (isHermitian_mul_pinv hD).eq
  have hPP := support_projection_idempotent D hD
  have hGram : (1 - D * pinv D)ᴴ * (1 - D * pinv D) = 1 - D * pinv D := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
      Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP,
      sub_self, sub_zero]
  rw [← hGram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Establishes `pinvSqrt_normalizes_support`: `pinvSqrt D * D * pinvSqrt D = D * pinv D`, for the stated parameters. -/
private theorem pinvSqrt_normalizes_support (D : Matrix n n ℂ)
    (hD : D.PosSemidef) : pinvSqrt D * D * pinvSqrt D = D * pinv D := by
  calc
    pinvSqrt D * D * pinvSqrt D =
        pinvSqrt D * (psqrt D * psqrt D) * pinvSqrt D := by
      rw [psqrt_mul_psqrt hD]
    _ = (pinvSqrt D * psqrt D) * (psqrt D * pinvSqrt D) := by
      simp only [Matrix.mul_assoc]
    _ = (D * pinv D) * (D * pinv D) := by
      rw [pinvSqrt_mul_psqrt hD, psqrt_mul_pinvSqrt hD]
    _ = D * pinv D := support_projection_idempotent D hD.isHermitian

/-- Lemma2 with its actual Eq.(5) and Eq.(6) proof dependencies.
Singular D is handled by support normalization and extension on the kernel;
no invertibility, positive dimension, or normalization hypothesis is added. -/
theorem isSeparable_equal_diagonal_by_svd_and_eigenbasis
    (D Y : Matrix n n ℂ) (h : (qubitBlocks D Y Yᴴ D).PosSemidef) :
    IsSeparable (qubitBlocks D Y Yᴴ D) := by
  have hblocks := posSemidef_qubitBlocks_iff.mp h
  obtain ⟨hD, hYP, _⟩ := posSemidef_fromBlocks_pinv hblocks
  obtain ⟨_, hPY, _⟩ := posSemidef_fromBlocks_pinv' hblocks
  let S := psqrt D
  let T := pinvSqrt D
  let P := D * pinv D
  let Z := T * Y * T
  have hS : Sᴴ = S := (isHermitian_psqrt hD).eq
  have hT : Tᴴ = T := (isHermitian_pinvSqrt hD).eq
  have hSS : S * S = D := psqrt_mul_psqrt hD
  have hST : S * T = P := psqrt_mul_pinvSqrt hD
  have hTS : T * S = P := pinvSqrt_mul_psqrt hD
  have hTDT : T * D * T = P := pinvSqrt_normalizes_support D hD
  have hZadj : T * Yᴴ * T = Zᴴ := by
    dsimp [Z]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hT]
    simp only [Matrix.mul_assoc]
  have hNorm : (qubitBlocks P Z Zᴴ P).PosSemidef := by
    have hh := h.mul_mul_conjTranspose_same ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T)
    rw [qubitBlocks_sysConj, hT, hTDT, hZadj] at hh
    exact hh
  have hComp : (qubitBlocks (1 - P) (0 : Matrix n n ℂ) 0 (1 - P)).PosSemidef := by
    have hh := (Matrix.PosSemidef.one : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef).kronecker
      (support_complement_posSemidef D hD.isHermitian)
    simpa [kronecker_eq_qubitBlocks, P] using hh
  have hOne : (qubitBlocks (1 : Matrix n n ℂ) Z Zᴴ 1).PosSemidef := by
    have hh := hNorm.add hComp
    rw [← qubitBlocks_add] at hh
    have hPI : P + (1 - P) = (1 : Matrix n n ℂ) := by abel
    simpa only [hPI, add_zero] using hh
  have hZcontract : (1 - Z * Zᴴ).PosSemidef := by
    have hh := (posSemidef_fromBlocks_pinv (posSemidef_qubitBlocks_iff.mp hOne)).2.2
    simpa only [pinv_one_matrix, Matrix.mul_one] using hh
  have hZsep := isSeparable_identity_block_of_contraction Z hZcontract
  have hSZS : S * Z * S = Y := by
    calc
      S * Z * S = (S * T) * Y * (T * S) := by
        dsimp [Z]
        simp only [Matrix.mul_assoc]
      _ = P * Y * P := by rw [hST, hTS]
      _ = Y := by
        change (D * pinv D) * Y * (D * pinv D) = Y
        rw [hPY, hYP]
  have hSZstarS : S * Zᴴ * S = Yᴴ := by
    have hh := congrArg Matrix.conjTranspose hSZS
    simpa only [Matrix.conjTranspose_mul, hS, Matrix.mul_assoc] using hh
  have hBack := hZsep.sysConj S
  rw [qubitBlocks_sysConj, hS, Matrix.mul_one, hSS, hSZS, hSZstarS] at hBack
  exact hBack

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptGB
