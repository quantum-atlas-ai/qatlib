/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# KMS inner products and norm bounds

This module defines the square-root-weighted trace pairing `kmsInner`, its associated quantity
`kmsNorm`, and centering by the state expectation through `kmsCenter`. It proves conjugate
symmetry, nonnegativity, a commutator identity, and comparison with the operator norm for
density operators.

Positive definiteness of the state gives definiteness of the KMS norm. A one-dimensional
counterexample records why the identity for pairing with the identity operator requires
positivity. Matrix square roots and trace inequalities are treated in [Bhatia1997].

## Main statements

* `kmsInner`: The KMS trace pairing `tr(Xᴴ √ρ Y √ρ)`, using the continuous functional calculus
  square root.
* `kmsNorm_le_opNorm`: For a density operator `ρ`, the KMS norm of `X` is bounded by its
  operator norm.
* `kmsNorm_eq_zero_iff`: For positive definite `ρ`, the KMS norm of `X` vanishes exactly when
  `X` is zero.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Foundations.DirichletForm.KmsDirichlet

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D : ℕ}

/-- The KMS trace pairing `tr(Xᴴ √ρ Y √ρ)`, using the continuous functional calculus square
root. -/
noncomputable def kmsInner (ρ : Operator D) (X Y : Operator D) : ℂ :=
  Matrix.trace (Xᴴ * CFC.sqrt ρ * Y * CFC.sqrt ρ)

/-- The square root of the real part of `kmsInner ρ X X`. -/
noncomputable def kmsNorm (ρ : Operator D) (X : Operator D) : ℝ :=
  Real.sqrt (Complex.re (kmsInner ρ X X))

/-- The operator obtained by subtracting `tr(ρ O)` times the identity from `O`. -/
noncomputable def kmsCenter (ρ : Operator D) (O : Operator D) : Operator D :=
  O - (Matrix.trace (ρ * O)) • (1 : Operator D)

section Proofs

open scoped Matrix.Norms.L2Operator

/-- For positive semidefinite `ρ`, pairing the identity with `Y` gives `tr(Y ρ)`. -/
theorem kmsInner_one_left (ρ Y : Operator D) (hρ : 0 ≤ ρ) :
    kmsInner ρ 1 Y = Matrix.trace (Y * ρ) := by
  simp only [kmsInner,Matrix.conjTranspose_one,Matrix.one_mul]
  rw [Matrix.trace_mul_cycle (CFC.sqrt ρ) Y (CFC.sqrt ρ),
    CFC.sqrt_mul_sqrt_self ρ hρ,Matrix.trace_mul_comm]

/-- Centering an operator with respect to a density operator makes its KMS pairing with the
identity vanish. -/
theorem kmsInner_center_one_left {ρ : Operator D} (hρ : IsDensityOperator ρ)
    (O : Operator D) : kmsInner ρ 1 (kmsCenter ρ O) = 0 := by
  rw [kmsInner_one_left _ _ hρ.1.nonneg,kmsCenter,Matrix.sub_mul,
    Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul,hρ.2,
    smul_eq_mul,mul_one,Matrix.trace_mul_comm,sub_self]

/-- The trace of a positive semidefinite matrix is nonnegative in the complex order. -/
theorem trace_nonneg_of_nonneg {Q : Operator D} (hQ : 0 ≤ Q) :
    (0 : ℂ) ≤ Matrix.trace Q :=
  Matrix.PosSemidef.trace_nonneg (Matrix.nonneg_iff_posSemidef.mp hQ)

/-- The matrix trace preserves the positive semidefinite order. -/
theorem trace_mono_nonneg {P Q : Operator D} (h : P ≤ Q) :
    Matrix.trace P ≤ Matrix.trace Q := by
  have h1 := trace_nonneg_of_nonneg (sub_nonneg.mpr h)
  rw [Matrix.trace_sub] at h1
  have h2 := Complex.le_def.mp h1
  have h3 : Complex.re (Matrix.trace Q) - Complex.re (Matrix.trace P) ≥ 0 := by
    simpa using h2.1
  have h4 : Complex.im (Matrix.trace Q) - Complex.im (Matrix.trace P) = 0 := by
    have := h2.2
    simp at this
    linarith
  exact Complex.le_def.mpr ⟨by linarith, by linarith⟩

/-- The KMS trace pairing is conjugate symmetric. -/
theorem kmsInner_conjSym (ρ X Y : Operator D) :
    kmsInner ρ X Y = star (kmsInner ρ Y X) := by
  have hS : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).1
  show Matrix.trace (Xᴴ * CFC.sqrt ρ * Y * CFC.sqrt ρ)
      = star (Matrix.trace (Yᴴ * CFC.sqrt ρ * X * CFC.sqrt ρ))
  rw [← Matrix.trace_conjTranspose]
  rw [show (Yᴴ * CFC.sqrt ρ * X * CFC.sqrt ρ)ᴴ
      = CFC.sqrt ρ * Xᴴ * CFC.sqrt ρ * Y from by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS,
      Matrix.mul_assoc]]
  exact (Matrix.trace_mul_comm (Xᴴ * CFC.sqrt ρ * Y) (CFC.sqrt ρ)).trans
    (by simp only [Matrix.mul_assoc])

/-- The KMS self-pairing is the trace of the Gram matrix of `ρ^(1/4) X ρ^(1/4)`, with fractional
powers expressed by iterated square roots. -/
theorem kmsInner_self_eq (ρ X : Operator D) :
    kmsInner ρ X X = Matrix.trace
      ((CFC.sqrt (CFC.sqrt ρ) * X * CFC.sqrt (CFC.sqrt ρ))ᴴ *
        (CFC.sqrt (CFC.sqrt ρ) * X * CFC.sqrt (CFC.sqrt ρ))) := by
  have hS : 0 ≤ CFC.sqrt ρ := CFC.sqrt_nonneg ρ
  set P := CFC.sqrt (CFC.sqrt ρ) with hPdef
  have hPst : Pᴴ = P :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (CFC.sqrt ρ))).1
  have hPP : P * P = CFC.sqrt ρ := CFC.sqrt_mul_sqrt_self (CFC.sqrt ρ) hS
  have e1 : (P * X * P)ᴴ = P * Xᴴ * P := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPst]
    simp only [Matrix.mul_assoc]
  show Matrix.trace (Xᴴ * CFC.sqrt ρ * X * CFC.sqrt ρ)
      = Matrix.trace ((P * X * P)ᴴ * (P * X * P))
  rw [e1, Matrix.trace_mul_comm (P * Xᴴ * P) (P * X * P)]
  rw [show (P * X * P) * (P * Xᴴ * P) = (P * X) * (P * P) * (Xᴴ * P) from by
      simp only [Matrix.mul_assoc]]
  rw [hPP, Matrix.trace_mul_cycle (P * X) (CFC.sqrt ρ) (Xᴴ * P)]
  rw [show Xᴴ * P * (P * X) * CFC.sqrt ρ = Xᴴ * CFC.sqrt ρ * X * CFC.sqrt ρ from by
      simp only [Matrix.mul_assoc, ← hPP]]

/-- The KMS self-pairing is nonnegative in the complex order. -/
theorem kmsInner_self_nonneg (ρ X : Operator D) : (0 : ℂ) ≤ kmsInner ρ X X := by
  have h1 : (0 : ℂ) ≤ Matrix.trace
      ((CFC.sqrt (CFC.sqrt ρ) * X * CFC.sqrt (CFC.sqrt ρ))ᴴ *
        (CFC.sqrt (CFC.sqrt ρ) * X * CFC.sqrt (CFC.sqrt ρ))) :=
    trace_nonneg_of_nonneg
      (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self _))
  rw [kmsInner_self_eq]
  exact h1

/-- The real part of the KMS self-pairing is nonnegative. -/
theorem kmsInner_re_self_nonneg (ρ X : Operator D) :
    0 ≤ Complex.re (kmsInner ρ X X) :=
  (Complex.le_def.mp (kmsInner_self_nonneg ρ X)).1

/-- For positive semidefinite `ρ`, the squared Hilbert–Schmidt norm of the commutator of `√ρ`
and `X` equals the sum of the two weighted quadratic traces minus twice the KMS
self-pairing. -/
theorem kms_commutator_identity (ρ X : Operator D) (hρ0 : 0 ≤ ρ) :
    Matrix.trace ((CFC.sqrt ρ * X - X * CFC.sqrt ρ)ᴴ * (CFC.sqrt ρ * X - X * CFC.sqrt ρ))
      = Matrix.trace (ρ * Xᴴ * X) + Matrix.trace (ρ * X * Xᴴ)
        - 2 * Matrix.trace (Xᴴ * CFC.sqrt ρ * X * CFC.sqrt ρ) := by
  have hSst : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).1
  have hSS : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ0
  have tAC : Matrix.trace ((Xᴴ * CFC.sqrt ρ) * (CFC.sqrt ρ * X))
      = Matrix.trace (ρ * X * Xᴴ) := by
    rw [show (Xᴴ * CFC.sqrt ρ) * (CFC.sqrt ρ * X)
        = Xᴴ * (CFC.sqrt ρ * CFC.sqrt ρ) * X from by
      simp only [← Matrix.mul_assoc],
      hSS, Matrix.trace_mul_cycle Xᴴ ρ X, Matrix.trace_mul_comm (X * Xᴴ) ρ]
    rw [Matrix.mul_assoc ρ X Xᴴ]
  have tAD : Matrix.trace ((Xᴴ * CFC.sqrt ρ) * (X * CFC.sqrt ρ))
      = Matrix.trace (Xᴴ * CFC.sqrt ρ * X * CFC.sqrt ρ) := by
    rw [Matrix.mul_assoc (Xᴴ * CFC.sqrt ρ) X (CFC.sqrt ρ)]
  have tBC : Matrix.trace ((CFC.sqrt ρ * Xᴴ) * (CFC.sqrt ρ * X))
      = Matrix.trace (Xᴴ * CFC.sqrt ρ * X * CFC.sqrt ρ) := by
    rw [Matrix.trace_mul_cycle (CFC.sqrt ρ) Xᴴ (CFC.sqrt ρ * X),
      Matrix.trace_mul_cycle (CFC.sqrt ρ * X) (CFC.sqrt ρ) Xᴴ,
      ← Matrix.mul_assoc Xᴴ (CFC.sqrt ρ) X]
  have tBD : Matrix.trace ((CFC.sqrt ρ * Xᴴ) * (X * CFC.sqrt ρ))
      = Matrix.trace (ρ * Xᴴ * X) := by
    rw [show (CFC.sqrt ρ * Xᴴ) * (X * CFC.sqrt ρ)
        = CFC.sqrt ρ * ((Xᴴ * X) * CFC.sqrt ρ) from by
      simp only [← Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show ((Xᴴ * X) * CFC.sqrt ρ) * CFC.sqrt ρ = (Xᴴ * X) * ρ from by
        rw [Matrix.mul_assoc (Xᴴ * X) (CFC.sqrt ρ) (CFC.sqrt ρ), hSS],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hSst,
    Matrix.conjTranspose_mul, hSst]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.trace_sub, tAC, tAD, tBC, tBD]
  ring

/-- The identity `kmsInner ρ 1 Y = tr(Y ρ)` does not hold for all one-dimensional operators
without a positivity hypothesis. -/
theorem kmsInner_one_left_unrestricted_false :
    ¬ (∀ (ρ Y : Operator 1), kmsInner ρ 1 Y = Matrix.trace (Y * ρ)) := by
  intro h
  have hn := kmsInner_self_nonneg (-(1 : Operator 1)) 1
  rw [h] at hn
  norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_one] at hn

/-- The trace of `Aᴴ A` is the sum of the squared Euclidean norms of the columns of `A`. -/
private theorem kms_trace_gram_columns (A : Operator D) :
    Matrix.trace (Aᴴ * A) =
      ((∑ j, ‖toEuclidean_fromVec (fun i => A i j)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    norm_toEuclidean_fromVec_sq,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]

/-- The trace of the Gram matrix of `X S` is at most `‖X‖²` times the trace of the Gram matrix
of `S`. -/
private theorem kms_trace_gram_mul_bound (X S : Operator D) :
    Matrix.trace ((X * S)ᴴ * (X * S)) ≤
      ((‖X‖ : ℝ) ^ 2 : ℂ) * Matrix.trace (Sᴴ * S) := by
  rw [kms_trace_gram_columns,kms_trace_gram_columns,← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.real_le_real,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hn := Matrix.l2_opNorm_mulVec X (toEuclidean_fromVec (fun i => S i j))
  change ‖toEuclidean_fromVec (fun i => (X * S) i j)‖ ≤
    ‖X‖ * ‖toEuclidean_fromVec (fun i => S i j)‖ at hn
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- For positive semidefinite `ρ`, the weighted trace of `Xᴴ X` is bounded by `‖X‖² tr(ρ)`. -/
private theorem kms_trace_conjTranspose_mul_bound {ρ : Operator D} (hρ0 : 0 ≤ ρ)
    (X : Operator D) :
    Matrix.trace (ρ * (Xᴴ * X)) ≤ ((‖X‖ : ℝ) ^ 2 : ℂ) * Matrix.trace ρ := by
  let S := CFC.sqrt ρ
  have hS : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).1
  have hSS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ0
  have he : Matrix.trace ((X * S)ᴴ * (X * S)) = Matrix.trace (ρ * (Xᴴ * X)) := by
    calc _ = Matrix.trace (S * (Xᴴ * X) * S) := by
           simp only [Matrix.conjTranspose_mul,hS,Matrix.mul_assoc]
         _ = Matrix.trace (ρ * (Xᴴ * X)) := by
           rw [Matrix.trace_mul_cycle S (Xᴴ * X) S,hSS]
  have ht : Matrix.trace (Sᴴ * S) = Matrix.trace ρ := by rw [hS,hSS]
  simpa only [he,ht] using kms_trace_gram_mul_bound X S

/-- For positive semidefinite `ρ`, either quadratic product `Xᴴ X` or `X Xᴴ` has weighted trace
at most `‖X‖² tr(ρ)`. -/
theorem kms_trace_bound {ρ : Operator D} (hρ0 : 0 ≤ ρ) {X Q : Operator D}
    (hQ : Q = Xᴴ * X ∨ Q = X * Xᴴ) :
    Matrix.trace (ρ * Q) ≤ ((‖X‖ : ℝ) ^ 2 : ℂ) * Matrix.trace ρ := by
  rcases hQ with rfl | rfl
  · exact kms_trace_conjTranspose_mul_bound hρ0 X
  · simpa only [Matrix.conjTranspose_conjTranspose,Matrix.l2_opNorm_conjTranspose]
      using kms_trace_conjTranspose_mul_bound hρ0 Xᴴ

/-- For a density operator `ρ`, the KMS norm of `X` is bounded by its operator norm. -/
theorem kmsNorm_le_opNorm {ρ : Operator D} (hρ : IsDensityOperator ρ) (X : Operator D) :
    kmsNorm ρ X ≤ ‖X‖ := by
  have hρ0 : 0 ≤ ρ := hρ.1.nonneg
  have h1 := (Complex.le_def.mp (kms_trace_bound hρ0 (X := X) (Or.inl rfl))).1
  have h2 := (Complex.le_def.mp (kms_trace_bound hρ0 (X := X) (Or.inr rfl))).1
  rw [hρ.2,mul_one,← Complex.ofReal_pow,Complex.ofReal_re] at h1 h2
  have hn := (Complex.le_def.mp (trace_nonneg_of_nonneg
    (Matrix.posSemidef_conjTranspose_mul_self
      (CFC.sqrt ρ * X - X * CFC.sqrt ρ)).nonneg)).1
  rw [kms_commutator_identity ρ X hρ0] at hn
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re] at hn
  norm_num at hn
  change 2 * (kmsInner ρ X X).re ≤
    (Matrix.trace (ρ * Xᴴ * X)).re + (Matrix.trace (ρ * X * Xᴴ)).re at hn
  rw [Matrix.mul_assoc,Matrix.mul_assoc] at hn
  have hs : (kmsNorm ρ X)^2 = (kmsInner ρ X X).re :=
    Real.sq_sqrt (kmsInner_re_self_nonneg ρ X)
  have hnonneg : 0 ≤ kmsNorm ρ X := Real.sqrt_nonneg _
  nlinarith [norm_nonneg X]

/-- For positive definite `ρ`, the KMS norm of `X` vanishes exactly when `X` is zero. -/
theorem kmsNorm_eq_zero_iff {ρ : Operator D} (hρ : ρ.PosDef) (X : Operator D) :
    kmsNorm ρ X = 0 ↔ X = 0 := by
  have hρpsd : ρ.PosSemidef := Matrix.PosDef.posSemidef hρ
  have hρ0 : 0 ≤ ρ := Matrix.PosSemidef.nonneg hρpsd
  have hρdet : ρ.det ≠ 0 := (Matrix.PosDef.det_pos hρ).ne'
  have hSS : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ0
  have hPP : CFC.sqrt (CFC.sqrt ρ) * CFC.sqrt (CFC.sqrt ρ) = CFC.sqrt ρ :=
    CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg ρ)
  have hSdet : (CFC.sqrt ρ).det ≠ 0 := by
    intro h
    apply hρdet
    rw [hSS.symm, Matrix.det_mul, h, zero_mul]
  have hPdet : (CFC.sqrt (CFC.sqrt ρ)).det ≠ 0 := by
    intro h
    apply hSdet
    rw [hPP.symm, Matrix.det_mul, h, zero_mul]
  have hPunit : IsUnit (CFC.sqrt (CFC.sqrt ρ)).det := IsUnit.mk0 _ hPdet
  have hPL : (CFC.sqrt (CFC.sqrt ρ))⁻¹ * CFC.sqrt (CFC.sqrt ρ) = 1 :=
    Matrix.nonsing_inv_mul _ hPunit
  have hPR : CFC.sqrt (CFC.sqrt ρ) * (CFC.sqrt (CFC.sqrt ρ))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hPunit
  constructor
  · intro h0
    have hre : Complex.re (kmsInner ρ X X) = 0 := by
      have h := (Real.sqrt_eq_zero (kmsInner_re_self_nonneg ρ X)).mp h0
      simpa [kmsNorm] using h
    have hzz : kmsInner ρ X X = 0 := by
      obtain ⟨hre2, him⟩ := Complex.le_def.mp (kmsInner_self_nonneg ρ X)
      refine Complex.ext ?_ ?_
      · show Complex.re (kmsInner ρ X X) = Complex.re 0
        simp only [Complex.zero_re]
        linarith
      · simpa using him.symm
    rw [kmsInner_self_eq] at hzz
    have hpxp : CFC.sqrt (CFC.sqrt ρ) * X * CFC.sqrt (CFC.sqrt ρ) = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzz
    have hfin : (CFC.sqrt (CFC.sqrt ρ))⁻¹ * (CFC.sqrt (CFC.sqrt ρ) * X *
        CFC.sqrt (CFC.sqrt ρ)) * (CFC.sqrt (CFC.sqrt ρ))⁻¹ = 0 := by
      rw [hpxp, Matrix.mul_zero, Matrix.zero_mul]
    rw [show (CFC.sqrt (CFC.sqrt ρ))⁻¹ * (CFC.sqrt (CFC.sqrt ρ) * X *
        CFC.sqrt (CFC.sqrt ρ)) * (CFC.sqrt (CFC.sqrt ρ))⁻¹ = X from by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPL, Matrix.one_mul,
        Matrix.mul_assoc, hPR, Matrix.mul_one]] at hfin
    exact hfin
  · intro h
    subst h
    simp [kmsNorm, kmsInner]

end Proofs

end Qatlib.Foundations.DirichletForm.KmsDirichlet
