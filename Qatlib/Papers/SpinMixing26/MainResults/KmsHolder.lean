/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DirichletForm.KmsDirichlet.KmsInnerProduct

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults — KMS Hölder inequality (Lemma II.2)

Bergamaschi–Chen, *Fast Mixing of Quantum Spin Chains at All Temperatures*,
fixed arXiv:2510.08533v2, Lemma II.2, Eqs. (2.10)–(2.11), p. 12.

原文在 KMS 范数 `‖X‖_ρ = ‖ρ^{1/4} X ρ^{1/4}‖_2`（式 (2.9)）下给出两条 Hölder 型界：
`‖A O‖_ρ ≤ ‖ρ^{1/4} A ρ^{−1/4}‖ · ‖O‖_ρ` 与 `‖O A‖_ρ ≤ ‖ρ^{−1/4} A ρ^{1/4}‖ · ‖O‖_ρ`，
对任意满秩态 `ρ` 与任意算符 `A, O` 成立。证明把两条 KMS 范数都写成 Frobenius 范数
`‖ρ^{1/4} (·) ρ^{1/4}‖_2`，再对左侧/右侧算符用算子范数的次乘性；此处 `ρ^{1/4}` 取
`CFC.sqrt (CFC.sqrt ρ)`，逆由 `ρ.PosDef` 的行列式非零给出。

复用的 Frozen 基础设施：`kmsInner`、`kmsNorm`、`kmsInner_self_eq`（把 KMS 自配对写成
`ρ^{1/4} X ρ^{1/4}` 的 Hilbert–Schmidt 迹）、`kmsInner_re_self_nonneg`。
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.DirichletForm.KmsDirichlet
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.SpinMixing26.MainResults

variable {D : ℕ}

/-- The quarter power `ρ^{1/4} = (ρ^{1/2})^{1/2}` used in Lemma II.2, Eqs. (2.10)–(2.11). -/
noncomputable def kmsQuarter (ρ : Operator D) : Operator D :=
  CFC.sqrt (CFC.sqrt ρ)

/-- Internal: `(X * S)ᴴ * (X * S)` has trace equal to the sum of the squared Euclidean norms
of the columns of `X * S`. -/
private theorem trace_gram_columns (A : Operator D) :
    Matrix.trace (Aᴴ * A) =
      ((∑ j, ‖toEuclidean_fromVec (fun i => A i j)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    norm_toEuclidean_fromVec_sq,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]

/-- Internal Gram bound: `‖X S‖_F ≤ ‖X‖ ‖S‖_F`, with the operator norm acting on the left
factor (the matrix analogue of Eq. (2.12)). -/
private theorem trace_gram_mul_le (X S : Operator D) :
    Matrix.trace ((X * S)ᴴ * (X * S)) ≤
      ((‖X‖ : ℝ) ^ 2 : ℂ) * Matrix.trace (Sᴴ * S) := by
  rw [trace_gram_columns,trace_gram_columns,← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.real_le_real,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hn := Matrix.l2_opNorm_mulVec X (toEuclidean_fromVec (fun i => S i j))
  change ‖toEuclidean_fromVec (fun i => (X * S) i j)‖ ≤
    ‖X‖ * ‖toEuclidean_fromVec (fun i => S i j)‖ at hn
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- Internal Gram bound with the operator norm on the right factor, used for Eq. (2.11). -/
private theorem trace_gram_mul_le_right (S X : Operator D) :
    Matrix.trace ((S * X)ᴴ * (S * X)) ≤
      Matrix.trace (Sᴴ * S) * ((‖X‖ : ℝ) ^ 2 : ℂ) := by
  have h := trace_gram_mul_le (X := Xᴴ) (S := Sᴴ)
  have h1 : (Xᴴ * Sᴴ)ᴴ = S * X := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  calc Matrix.trace ((S * X)ᴴ * (S * X))
      = Matrix.trace ((S * X) * (S * X)ᴴ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((S * X) * (Xᴴ * Sᴴ)) := by rw [Matrix.conjTranspose_mul]
    _ = Matrix.trace (((Xᴴ * Sᴴ)ᴴ) * (Xᴴ * Sᴴ)) := by rw [h1]
    _ ≤ ((‖Xᴴ‖ : ℝ) ^ 2 : ℂ) * Matrix.trace (((Sᴴ)ᴴ) * (Sᴴ)) := h
    _ = ((‖X‖ : ℝ) ^ 2 : ℂ) * Matrix.trace (S * Sᴴ) := by
        rw [Matrix.l2_opNorm_conjTranspose, Matrix.conjTranspose_conjTranspose]
    _ = Matrix.trace (Sᴴ * S) * ((‖X‖ : ℝ) ^ 2 : ℂ) := by
        rw [Matrix.trace_mul_comm S Sᴴ, mul_comm]

/-- The quarter power of a positive definite state is invertible. -/
private theorem kmsQuarter_det_ne_zero {ρ : Operator D} (hρ : ρ.PosDef) :
    (kmsQuarter ρ).det ≠ 0 := by
  have hρ0 : 0 ≤ ρ := Matrix.PosSemidef.nonneg (Matrix.PosDef.posSemidef hρ)
  have hρdet : ρ.det ≠ 0 := (Matrix.PosDef.det_pos hρ).ne'
  have hSS : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ0
  have hPP : kmsQuarter ρ * kmsQuarter ρ = CFC.sqrt ρ :=
    CFC.sqrt_mul_sqrt_self (CFC.sqrt ρ) (CFC.sqrt_nonneg ρ)
  intro h
  apply hρdet
  rw [← hSS, ← hPP, Matrix.det_mul, Matrix.det_mul, h]
  ring

/-- Lemma II.2 (Hölder in the KMS norm), Eq. (2.10): for a full-rank state `ρ` and operators
`A`, `O`, `‖A O‖_ρ ≤ ‖ρ^{1/4} A ρ^{−1/4}‖ · ‖O‖_ρ`. -/
theorem kmsNorm_mul_le_quarter_opNorm {ρ A O : Operator D} (hρ : ρ.PosDef) :
    kmsNorm ρ (A * O) ≤ ‖kmsQuarter ρ * A * (kmsQuarter ρ)⁻¹‖ * kmsNorm ρ O := by
  have hdetP : (kmsQuarter ρ).det ≠ 0 := kmsQuarter_det_ne_zero hρ
  have hPunit : IsUnit (kmsQuarter ρ).det := IsUnit.mk0 _ hdetP
  have hPL : (kmsQuarter ρ)⁻¹ * kmsQuarter ρ = 1 := Matrix.nonsing_inv_mul _ hPunit
  have halg : kmsQuarter ρ * (A * O) * kmsQuarter ρ
      = (kmsQuarter ρ * A * (kmsQuarter ρ)⁻¹) * (kmsQuarter ρ * O * kmsQuarter ρ) := by
    have h1 : (kmsQuarter ρ * A) * (O * kmsQuarter ρ)
        = (kmsQuarter ρ * A * (kmsQuarter ρ)⁻¹) * (kmsQuarter ρ * O * kmsQuarter ρ) := by
      rw [Matrix.mul_assoc (kmsQuarter ρ * A) (kmsQuarter ρ)⁻¹
        (kmsQuarter ρ * O * kmsQuarter ρ)]
      rw [show (kmsQuarter ρ)⁻¹ * (kmsQuarter ρ * O * kmsQuarter ρ)
          = ((kmsQuarter ρ)⁻¹ * kmsQuarter ρ) * (O * kmsQuarter ρ) by
        simp only [Matrix.mul_assoc]]
      rw [hPL, Matrix.one_mul]
    calc kmsQuarter ρ * (A * O) * kmsQuarter ρ
        = (kmsQuarter ρ * A) * (O * kmsQuarter ρ) := by simp only [Matrix.mul_assoc]
      _ = _ := h1
  have htr := trace_gram_mul_le (kmsQuarter ρ * A * (kmsQuarter ρ)⁻¹)
    (kmsQuarter ρ * O * kmsQuarter ρ)
  rw [← halg] at htr
  have hre : (kmsInner ρ (A * O) (A * O)).re
      ≤ ‖kmsQuarter ρ * A * (kmsQuarter ρ)⁻¹‖ ^ 2 * (kmsInner ρ O O).re := by
    rw [kmsInner_self_eq, kmsInner_self_eq]
    have h := (Complex.le_def.mp htr).1
    simp only [Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h
    simpa only [kmsQuarter] using h
  have hAO : kmsNorm ρ (A * O) ^ 2 = (kmsInner ρ (A * O) (A * O)).re :=
    Real.sq_sqrt (kmsInner_re_self_nonneg ρ (A * O))
  have hO : kmsNorm ρ O ^ 2 = (kmsInner ρ O O).re :=
    Real.sq_sqrt (kmsInner_re_self_nonneg ρ O)
  have hsq : kmsNorm ρ (A * O) ^ 2
      ≤ (‖kmsQuarter ρ * A * (kmsQuarter ρ)⁻¹‖ * kmsNorm ρ O) ^ 2 := by
    rw [hAO, mul_pow, hO]
    exact hre
  have hx : 0 ≤ kmsNorm ρ (A * O) := Real.sqrt_nonneg _
  have hy : 0 ≤ ‖kmsQuarter ρ * A * (kmsQuarter ρ)⁻¹‖ * kmsNorm ρ O :=
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [hsq, hx, hy]

/-- Lemma II.2 (Hölder in the KMS norm), Eq. (2.11): for a full-rank state `ρ` and operators
`A`, `O`, `‖O A‖_ρ ≤ ‖ρ^{−1/4} A ρ^{1/4}‖ · ‖O‖_ρ`. -/
theorem kmsNorm_mul_le_opNorm_quarter {ρ A O : Operator D} (hρ : ρ.PosDef) :
    kmsNorm ρ (O * A) ≤ ‖(kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ‖ * kmsNorm ρ O := by
  have hdetP : (kmsQuarter ρ).det ≠ 0 := kmsQuarter_det_ne_zero hρ
  have hPunit : IsUnit (kmsQuarter ρ).det := IsUnit.mk0 _ hdetP
  have hPR : kmsQuarter ρ * (kmsQuarter ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPunit
  have halg : kmsQuarter ρ * (O * A) * kmsQuarter ρ
      = (kmsQuarter ρ * O * kmsQuarter ρ) * ((kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ) := by
    have h1 : (kmsQuarter ρ * O) * (A * kmsQuarter ρ)
        = (kmsQuarter ρ * O * kmsQuarter ρ) * ((kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ) := by
      rw [Matrix.mul_assoc (kmsQuarter ρ * O) (kmsQuarter ρ)
        ((kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ)]
      rw [show kmsQuarter ρ * ((kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ)
          = (kmsQuarter ρ * (kmsQuarter ρ)⁻¹) * (A * kmsQuarter ρ) by
        simp only [Matrix.mul_assoc]]
      rw [hPR, Matrix.one_mul]
    calc kmsQuarter ρ * (O * A) * kmsQuarter ρ
        = (kmsQuarter ρ * O) * (A * kmsQuarter ρ) := by simp only [Matrix.mul_assoc]
      _ = _ := h1
  have htr := trace_gram_mul_le_right (kmsQuarter ρ * O * kmsQuarter ρ)
    ((kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ)
  rw [← halg] at htr
  have hre : (kmsInner ρ (O * A) (O * A)).re
      ≤ ‖(kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ‖ ^ 2 * (kmsInner ρ O O).re := by
    rw [kmsInner_self_eq, kmsInner_self_eq]
    have h := (Complex.le_def.mp htr).1
    simp only [Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at h
    simpa only [kmsQuarter, mul_comm] using h
  have hOA : kmsNorm ρ (O * A) ^ 2 = (kmsInner ρ (O * A) (O * A)).re :=
    Real.sq_sqrt (kmsInner_re_self_nonneg ρ (O * A))
  have hO : kmsNorm ρ O ^ 2 = (kmsInner ρ O O).re :=
    Real.sq_sqrt (kmsInner_re_self_nonneg ρ O)
  have hsq : kmsNorm ρ (O * A) ^ 2
      ≤ (‖(kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ‖ * kmsNorm ρ O) ^ 2 := by
    rw [hOA, mul_pow, hO]
    exact hre
  have hx : 0 ≤ kmsNorm ρ (O * A) := Real.sqrt_nonneg _
  have hy : 0 ≤ ‖(kmsQuarter ρ)⁻¹ * A * kmsQuarter ρ‖ * kmsNorm ρ O :=
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [hsq, hx, hy]

end Qatlib.Papers.SpinMixing26.MainResults
