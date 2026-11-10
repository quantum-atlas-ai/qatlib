/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DirichletForm.KmsDirichlet.KmsInnerProduct
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.DirichletForm.KmsDirichlet

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D : ℕ}

noncomputable def kmsGenerator (ρ A : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  (LinearMap.mulRight ℂ (CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹)).comp
      (LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A)
    - (LinearMap.mulLeft ℂ ((CFC.sqrt ρ)⁻¹ * Aᴴ * CFC.sqrt ρ)).comp
      (LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A)

theorem kmsGenerator_apply (ρ A X : Operator D) :
    kmsGenerator ρ A X =
      (A * X - X * A) * (CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹)
        - ((CFC.sqrt ρ)⁻¹ * Aᴴ * CFC.sqrt ρ) * (A * X - X * A) := rfl

noncomputable def kmsGeneratorFam {ι : Type*} [Fintype ι] (ρ : Operator D)
    (A : ι → Operator D) : Operator D →ₗ[ℂ] Operator D :=
  ∑ i, kmsGenerator ρ (A i)

noncomputable def kmsDirichlet (ρ : Operator D) (N : Operator D →ₗ[ℂ] Operator D)
    (O : Operator D) : ℝ :=
  Complex.re (kmsInner ρ O (-(N O)))

noncomputable def kmsVariance (ρ : Operator D) (O : Operator D) : ℝ :=
  (kmsNorm ρ (kmsCenter ρ O)) ^ 2

def KmsSelfAdjoint (ρ : Operator D) (N : Operator D →ₗ[ℂ] Operator D) : Prop :=
  ∀ X Y, kmsInner ρ X (N Y) = kmsInner ρ (N X) Y

def KmsGapAtLeast (ρ : Operator D) (N : Operator D →ₗ[ℂ] Operator D) (r : ℝ) : Prop :=
  ∀ O, r * kmsVariance ρ O ≤ kmsDirichlet ρ N O

section Proofs

open scoped Matrix.Norms.L2Operator

theorem kmsInner_add_right (ρ X U V : Operator D) :
    kmsInner ρ X (U + V) = kmsInner ρ X U + kmsInner ρ X V := by
  show Matrix.trace (Xᴴ * CFC.sqrt ρ * (U + V) * CFC.sqrt ρ) = _
  rw [show Xᴴ * CFC.sqrt ρ * (U + V) * CFC.sqrt ρ
      = Xᴴ * CFC.sqrt ρ * U * CFC.sqrt ρ + Xᴴ * CFC.sqrt ρ * V * CFC.sqrt ρ from by
    rw [Matrix.mul_add, Matrix.add_mul],
    Matrix.trace_add]
  rfl

theorem kmsInner_neg_right (ρ X Y : Operator D) :
    kmsInner ρ X (-(Y : Operator D)) = -(kmsInner ρ X Y) := by
  show Matrix.trace (Xᴴ * CFC.sqrt ρ * (-(Y : Operator D)) * CFC.sqrt ρ) = _
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg]
  rfl

theorem kmsInner_sub_right (ρ X U V : Operator D) :
    kmsInner ρ X (U - V) = kmsInner ρ X U - kmsInner ρ X V := by
  rw [show U - V = U + (-(V : Operator D)) from (sub_eq_add_neg U V).symm,
    kmsInner_add_right, kmsInner_neg_right, sub_eq_add_neg]

theorem kmsGenerator_dirichlet {ρ : Operator D} (hρ : ρ.PosDef) (A X Y : Operator D) :
    kmsInner ρ Y (-(kmsGenerator ρ A X)) =
      kmsInner ρ (A * Y - Y * A) (A * X - X * A) := by
  have hρ0 : 0 ≤ ρ := Matrix.PosSemidef.nonneg (Matrix.PosDef.posSemidef hρ)
  have hρdet : ρ.det ≠ 0 := (Matrix.PosDef.det_pos hρ).ne'
  have hSS : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ0
  have hSdet : (CFC.sqrt ρ).det ≠ 0 := by
    intro h
    apply hρdet
    rw [hSS.symm, Matrix.det_mul, h, zero_mul]
  have hSunit : IsUnit (CFC.sqrt ρ).det := IsUnit.mk0 _ hSdet
  have hSL : (CFC.sqrt ρ)⁻¹ * CFC.sqrt ρ = 1 := Matrix.nonsing_inv_mul _ hSunit
  have hSR : CFC.sqrt ρ * (CFC.sqrt ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hSunit
  have eBS : (CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹) * CFC.sqrt ρ = CFC.sqrt ρ * Aᴴ := by
    rw [show CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹ * CFC.sqrt ρ
        = CFC.sqrt ρ * Aᴴ * ((CFC.sqrt ρ)⁻¹ * CFC.sqrt ρ) from Matrix.mul_assoc _ _ _,
      hSL, Matrix.mul_one]
  have eSC : CFC.sqrt ρ * ((CFC.sqrt ρ)⁻¹ * Aᴴ * CFC.sqrt ρ) = Aᴴ * CFC.sqrt ρ := by
    rw [← Matrix.mul_assoc (CFC.sqrt ρ) ((CFC.sqrt ρ)⁻¹ * Aᴴ) (CFC.sqrt ρ),
      ← Matrix.mul_assoc (CFC.sqrt ρ) ((CFC.sqrt ρ)⁻¹) Aᴴ, hSR, Matrix.one_mul]
  have t1 : kmsInner ρ Y ((A * X - X * A) * (CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹))
      = kmsInner ρ (Y * A) (A * X - X * A) := by
    show Matrix.trace (Yᴴ * CFC.sqrt ρ * ((A * X - X * A) *
        (CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹)) * CFC.sqrt ρ)
      = Matrix.trace ((Y * A)ᴴ * CFC.sqrt ρ * (A * X - X * A) * CFC.sqrt ρ)
    rw [Matrix.mul_assoc (Yᴴ * CFC.sqrt ρ)
        ((A * X - X * A) * (CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹)) (CFC.sqrt ρ),
      Matrix.mul_assoc (A * X - X * A) (CFC.sqrt ρ * Aᴴ * (CFC.sqrt ρ)⁻¹) (CFC.sqrt ρ),
      eBS,
      ← Matrix.mul_assoc (Yᴴ * CFC.sqrt ρ) (A * X - X * A) (CFC.sqrt ρ * Aᴴ),
      ← Matrix.mul_assoc (Yᴴ * CFC.sqrt ρ * (A * X - X * A)) (CFC.sqrt ρ) Aᴴ,
      Matrix.trace_mul_cycle (Yᴴ * CFC.sqrt ρ * (A * X - X * A)) (CFC.sqrt ρ) Aᴴ,
      ← Matrix.mul_assoc Aᴴ (Yᴴ * CFC.sqrt ρ) (A * X - X * A),
      ← Matrix.mul_assoc Aᴴ Yᴴ (CFC.sqrt ρ),
      Matrix.conjTranspose_mul]
  have t2 : kmsInner ρ Y ((CFC.sqrt ρ)⁻¹ * Aᴴ * CFC.sqrt ρ * (A * X - X * A))
      = kmsInner ρ (A * Y) (A * X - X * A) := by
    show Matrix.trace (Yᴴ * CFC.sqrt ρ * ((CFC.sqrt ρ)⁻¹ * Aᴴ * CFC.sqrt ρ *
        (A * X - X * A)) * CFC.sqrt ρ)
      = Matrix.trace ((A * Y)ᴴ * CFC.sqrt ρ * (A * X - X * A) * CFC.sqrt ρ)
    rw [Matrix.mul_assoc Yᴴ (CFC.sqrt ρ)
        ((CFC.sqrt ρ)⁻¹ * Aᴴ * CFC.sqrt ρ * (A * X - X * A)),
      ← Matrix.mul_assoc (CFC.sqrt ρ) ((CFC.sqrt ρ)⁻¹ * Aᴴ * CFC.sqrt ρ)
        (A * X - X * A),
      eSC, ← Matrix.mul_assoc Yᴴ (Aᴴ * CFC.sqrt ρ) (A * X - X * A),
      ← Matrix.mul_assoc Yᴴ Aᴴ (CFC.sqrt ρ),
      Matrix.conjTranspose_mul]
  rw [kmsGenerator_apply, kmsInner_neg_right, kmsInner_sub_right, t1, t2, neg_sub,
    kmsInner_conjSym ρ (A * Y - Y * A) (A * X - X * A),
    kmsInner_sub_right ρ (A * X - X * A) (A * Y) (Y * A), star_sub,
    ← kmsInner_conjSym ρ (A * Y) (A * X - X * A),
    ← kmsInner_conjSym ρ (Y * A) (A * X - X * A)]

theorem kmsGenerator_dirichlet_self {ρ : Operator D} (hρ : ρ.PosDef) (A X : Operator D) :
    kmsDirichlet ρ (kmsGenerator ρ A) X = (kmsNorm ρ (A * X - X * A)) ^ 2 := by
  show Complex.re (kmsInner ρ X (-(kmsGenerator ρ A X)))
    = (Real.sqrt (Complex.re (kmsInner ρ (A * X - X * A) (A * X - X * A)))) ^ 2
  rw [kmsGenerator_dirichlet hρ A X X]
  exact (Real.sq_sqrt (kmsInner_re_self_nonneg ρ (A * X - X * A))).symm

theorem kmsInner_sum_right {ι : Type*} (ρ X : Operator D) (s : Finset ι)
    (V : ι → Operator D) :
    kmsInner ρ X (∑ i ∈ s, V i) = ∑ i ∈ s, kmsInner ρ X (V i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kmsInner]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, kmsInner_add_right, ih]

theorem complex_re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.re (∑ i ∈ s, f i) = ∑ i ∈ s, Complex.re (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Complex.add_re, ih]

theorem kmsGeneratorFam_dirichlet_self {ι : Type*} [Fintype ι] {ρ : Operator D}
    (hρ : ρ.PosDef) (A : ι → Operator D) (X : Operator D) :
    kmsDirichlet ρ (kmsGeneratorFam ρ A) X
      = ∑ i, (kmsNorm ρ (A i * X - X * A i)) ^ 2 := by
  show Complex.re (kmsInner ρ X (-((kmsGeneratorFam ρ A) X)))
    = ∑ i, (Real.sqrt (Complex.re (kmsInner ρ (A i * X - X * A i)
        (A i * X - X * A i)))) ^ 2
  rw [kmsGeneratorFam, LinearMap.sum_apply]
  rw [show -(∑ i, kmsGenerator ρ (A i) X) = ∑ i, -(kmsGenerator ρ (A i) X) from
    (Finset.sum_neg_distrib _).symm]
  rw [kmsInner_sum_right, complex_re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact kmsGenerator_dirichlet_self hρ (A i) X

theorem kmsGenerator_one (ρ A : Operator D) : kmsGenerator ρ A 1 = 0 := by
  rw [kmsGenerator_apply, Matrix.mul_one, Matrix.one_mul, sub_self,
    Matrix.zero_mul, Matrix.mul_zero, sub_zero]

theorem kmsGenerator_selfAdjoint {ρ : Operator D} (hρ : ρ.PosDef) (A : Operator D) :
    KmsSelfAdjoint ρ (kmsGenerator ρ A) := by
  intro X Y
  have h1 : kmsInner ρ X (-(kmsGenerator ρ A Y))
      = kmsInner ρ (A * X - X * A) (A * Y - Y * A) :=
    kmsGenerator_dirichlet hρ A Y X
  have h2 : kmsInner ρ Y (-(kmsGenerator ρ A X))
      = kmsInner ρ (A * Y - Y * A) (A * X - X * A) :=
    kmsGenerator_dirichlet hρ A X Y
  have e1 : kmsInner ρ X (kmsGenerator ρ A Y)
      = -(kmsInner ρ X (-(kmsGenerator ρ A Y))) := by
    rw [kmsInner_neg_right, neg_neg]
  have e2 : kmsInner ρ Y (kmsGenerator ρ A X)
      = -(kmsInner ρ Y (-(kmsGenerator ρ A X))) := by
    rw [kmsInner_neg_right, neg_neg]
  show kmsInner ρ X (kmsGenerator ρ A Y) = kmsInner ρ (kmsGenerator ρ A X) Y
  rw [e1, h1, kmsInner_conjSym ρ (kmsGenerator ρ A X) Y, e2, h2, star_neg]
  exact neg_injective (by rw [kmsInner_conjSym])

theorem kmsGenerator_dirichlet_nonneg {ρ : Operator D} (hρ : ρ.PosDef) (A X : Operator D) :
    0 ≤ kmsDirichlet ρ (kmsGenerator ρ A) X := by
  rw [kmsGenerator_dirichlet_self hρ A X]
  exact sq_nonneg _

theorem kmsGeneratorFam_kernel {ι : Type*} [Fintype ι] {ρ : Operator D} (hρ : ρ.PosDef)
    (A : ι → Operator D) (X : Operator D) :
    kmsGeneratorFam ρ A X = 0 ↔ ∀ i, A i * X = X * A i := by
  constructor
  · intro h i
    have hdir0 : kmsDirichlet ρ (kmsGeneratorFam ρ A) X = 0 := by
      show Complex.re (kmsInner ρ X (-((kmsGeneratorFam ρ A) X))) = 0
      rw [h]
      simp [kmsInner]
    have hdir := (kmsGeneratorFam_dirichlet_self hρ A X).symm.trans hdir0
    have hone := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i' _ => sq_nonneg (kmsNorm ρ (A i' * X - X * A i')))).mp hdir i
      (Finset.mem_univ i)
    have hz : kmsNorm ρ (A i * X - X * A i) = 0 := by
      exact (pow_eq_zero_iff two_ne_zero).mp hone
    exact sub_eq_zero.mp ((kmsNorm_eq_zero_iff hρ _).mp hz)
  · intro h
    rw [kmsGeneratorFam, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi := h i
    rw [kmsGenerator_apply, hi, sub_self, Matrix.zero_mul, Matrix.mul_zero, sub_zero]

theorem kmsGap_transfer {ρ : Operator D} {M N : Operator D →ₗ[ℂ] Operator D} {α : ℝ}
    (hα : 0 < α) (hcmp : ∀ O, kmsDirichlet ρ N O ≤ α * kmsDirichlet ρ M O)
    {r : ℝ} (hgap : KmsGapAtLeast ρ N r) : KmsGapAtLeast ρ M (r / α) := by
  intro O
  have h1 := hgap O
  have h2 := hcmp O
  calc (r / α) * kmsVariance ρ O
      = (r * kmsVariance ρ O) / α := div_mul_eq_mul_div r α (kmsVariance ρ O)
    _ ≤ kmsDirichlet ρ N O / α := div_le_div_of_nonneg_right h1 hα.le
    _ ≤ (α * kmsDirichlet ρ M O) / α := div_le_div_of_nonneg_right h2 hα.le
    _ = kmsDirichlet ρ M O := mul_div_cancel_left₀ (kmsDirichlet ρ M O) (ne_of_gt hα)

end Proofs

end Qatlib.Foundations.DirichletForm.KmsDirichlet
