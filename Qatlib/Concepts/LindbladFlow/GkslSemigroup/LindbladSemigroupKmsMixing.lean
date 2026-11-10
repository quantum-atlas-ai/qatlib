/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import QuantumInfo.Channels.Unbundled
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.MeasuredMetropolisChannel
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.Entropy.DPI
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupDirichlet
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

set_option autoImplicit false

open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.DirichletForm.KmsDirichlet


namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Filter
open scoped Topology

noncomputable def hsAdjoint {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Operator E →ₗ[ℂ] Operator D := by
  letI : NormedAddCommGroup (Operator D) := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
  letI : NormedAddCommGroup (Operator E) := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
  letI : SeminormedAddCommGroup (Operator D) :=
    (inferInstance : NormedAddCommGroup (Operator D)).toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (Operator E) :=
    (inferInstance : NormedAddCommGroup (Operator E)).toSeminormedAddCommGroup
  letI : InnerProductSpace ℂ (Operator D) := Matrix.toMatrixInnerProductSpace (1 : Operator D) Matrix.PosSemidef.one
  letI : InnerProductSpace ℂ (Operator E) := Matrix.toMatrixInnerProductSpace (1 : Operator E) Matrix.PosSemidef.one
  exact LinearMap.adjoint T

theorem hsAdjoint_trace {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (X : Operator D) (Y : Operator E) :
    Matrix.trace (Xᴴ * hsAdjoint T Y) = Matrix.trace ((T X)ᴴ * Y) := by
  letI : NormedAddCommGroup (Operator D) := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
  letI : NormedAddCommGroup (Operator E) := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
  letI : SeminormedAddCommGroup (Operator D) :=
    (inferInstance : NormedAddCommGroup (Operator D)).toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (Operator E) :=
    (inferInstance : NormedAddCommGroup (Operator E)).toSeminormedAddCommGroup
  letI : InnerProductSpace ℂ (Operator D) := Matrix.toMatrixInnerProductSpace (1 : Operator D) Matrix.PosSemidef.one
  letI : InnerProductSpace ℂ (Operator E) := Matrix.toMatrixInnerProductSpace (1 : Operator E) Matrix.PosSemidef.one
  have h := LinearMap.adjoint_inner_right T X Y
  change Matrix.trace (hsAdjoint T Y * 1 * Xᴴ) = Matrix.trace (Y * 1 * (T X)ᴴ) at h
  simp only [Matrix.mul_one] at h
  calc
    _ = Matrix.trace (hsAdjoint T Y * Xᴴ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Y * (T X)ᴴ) := h
    _ = _ := Matrix.trace_mul_comm _ _

noncomputable def kmsAdjointMap {D E : ℕ} (ρ : Operator D) (σ : Operator E)
    (T : Operator D →ₗ[ℂ] Operator E) : Operator E →ₗ[ℂ] Operator D :=
  (LinearMap.mulRight ℂ (CFC.sqrt ρ)⁻¹).comp
    ((LinearMap.mulLeft ℂ (CFC.sqrt ρ)⁻¹).comp
      ((hsAdjoint T).comp ((LinearMap.mulRight ℂ (CFC.sqrt σ)).comp
        (LinearMap.mulLeft ℂ (CFC.sqrt σ)))))

theorem kmsAdjointMap_apply {D E : ℕ} (ρ : Operator D) (σ : Operator E)
    (T : Operator D →ₗ[ℂ] Operator E) (Y : Operator E) :
    kmsAdjointMap ρ σ T Y = (CFC.sqrt ρ)⁻¹ *
      hsAdjoint T (CFC.sqrt σ * Y * CFC.sqrt σ) * (CFC.sqrt ρ)⁻¹ := rfl

theorem kmsAdjointMap_inner {D E : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (σ : Operator E) (T : Operator D →ₗ[ℂ] Operator E) (X : Operator D) (Y : Operator E) :
    kmsInner ρ X (kmsAdjointMap ρ σ T Y) = kmsInner σ (T X) Y := by
  let S : Operator D := CFC.sqrt ρ
  have hSS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  have hdet : S.det ≠ 0 := by
    intro h
    have hd := (Matrix.PosDef.det_pos hρ).ne'
    apply hd
    rw [← hSS, Matrix.det_mul, h, zero_mul]
  have hunit : IsUnit S.det := IsUnit.mk0 _ hdet
  have hL : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hunit
  have hR : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcancel (Z : Operator D) : Xᴴ * S * (S⁻¹ * Z * S⁻¹) * S = Xᴴ * Z := by
    simp only [Matrix.mul_assoc, hL, Matrix.mul_one]
    rw [← Matrix.mul_assoc S S⁻¹ Z, hR, Matrix.one_mul]
  rw [kmsInner, kmsInner, kmsAdjointMap_apply]
  change Matrix.trace (Xᴴ * S * (S⁻¹ * hsAdjoint T (CFC.sqrt σ * Y * CFC.sqrt σ) * S⁻¹) * S) = _
  rw [hcancel, hsAdjoint_trace]
  simp only [Matrix.mul_assoc]

theorem kmsAdjointMap_unique {D E : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (σ : Operator E) (T : Operator D →ₗ[ℂ] Operator E) (A : Operator E →ₗ[ℂ] Operator D)
    (hA : ∀ X Y, kmsInner ρ X (A Y) = kmsInner σ (T X) Y) : A = kmsAdjointMap ρ σ T := by
  ext Y a b
  let Z := A Y - kmsAdjointMap ρ σ T Y
  have hzero : kmsInner ρ Z Z = 0 := by
    change kmsInner ρ Z (A Y - kmsAdjointMap ρ σ T Y) = 0
    rw [kmsInner_sub_right, hA, kmsAdjointMap_inner hρ, sub_self]
  have hn : kmsNorm ρ Z = 0 := by simp only [kmsNorm, hzero, Complex.zero_re, Real.sqrt_zero]
  have hz := (kmsNorm_eq_zero_iff hρ Z).mp hn
  have heq : A Y = kmsAdjointMap ρ σ T Y := sub_eq_zero.mp hz
  exact congrFun (congrFun heq a) b

theorem kmsSelfAdjoint_iff_kmsAdjointMap_eq {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (T : Operator D →ₗ[ℂ] Operator D) :
    KmsSelfAdjoint ρ T ↔ kmsAdjointMap ρ ρ T = T := by
  constructor
  · intro h
    exact (kmsAdjointMap_unique hρ ρ T T h).symm
  · intro h X Y
    simpa only [h] using! kmsAdjointMap_inner hρ ρ T X Y

theorem hasDerivAt_lindbladSemigroup {D : ℕ} (G : GKSL D) (σ : Operator D) (t : ℝ) :
    HasDerivAt (fun u : ℝ => lindbladSemigroup G u σ)
      (lindbladApply G (lindbladSemigroup G t σ)) t := by
  letI : NormedAddCommGroup (Operator D) := Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℂ (Operator D) := Matrix.instL2OpNormedSpace
  letI : TopologicalSpace (Operator D) :=
    (inferInstance : NormedAddCommGroup (Operator D)).toUniformSpace.toTopologicalSpace
  letI : Module ℂ (Operator D) := (inferInstance : NormedSpace ℂ (Operator D)).toModule
  let L : Operator D →L[ℂ] Operator D := LinearMap.toContinuousLinearMap (lindbladMap G)
  have heq (u : ℝ) : lindbladSemigroup G u σ = (NormedSpace.exp ((u : ℂ) • L)) σ := by
    have hh := (ContinuousLinearMap.apply ℂ (Operator D) σ).hasSum
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((u : ℂ) • L))
    have ht (k : ℕ) :
        (ContinuousLinearMap.apply ℂ (Operator D) σ)
            (((k.factorial : ℂ)⁻¹) • ((u : ℂ) • L) ^ k) =
          ((u : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) σ := by
      change (((k.factorial : ℂ)⁻¹) • ((u : ℂ) • L) ^ k) σ = _
      rw [ContinuousLinearMap.smul_apply]
      have hpow (k : ℕ) : ((u : ℂ) • L) ^ k = (u : ℂ) ^ k • L ^ k := by
        induction k with
        | zero => simp only [pow_zero, one_smul]
        | succ k ih =>
          rw [pow_succ, ih]
          ext τ
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            map_smul, smul_smul, pow_succ, mul_comm]
      rw [hpow k, ContinuousLinearMap.smul_apply, smul_smul,
        ContinuousLinearMap.coe_pow']
      change ((k.factorial : ℂ)⁻¹ * (u : ℂ) ^ k) • ((lindbladMap G)^[k]) σ = _
      rw [div_eq_mul_inv, mul_comm]
    simp only [ht] at hh
    exact (lindbladSemigroup_hasSum G u σ).unique hh
  have hd := hasDerivAt_exp_smul_const' (𝕂 := ℝ) L t
  have hv :=
      ((ContinuousLinearMap.apply ℂ (Operator D) σ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun u : ℝ => (NormedSpace.exp (u • L)) σ)
    (L ((NormedSpace.exp (t • L)) σ)) t at hv
  have hr (u : ℝ) : u • L = (u : ℂ) • L := by ext X; simp
  simp only [hr, ← heq] at hv
  exact hv

private theorem kmsInner_eq_hs {D : ℕ} (ρ X Y : Operator D) :
    kmsInner ρ X Y = Matrix.trace
      ((CFC.sqrt (CFC.sqrt ρ) * X * CFC.sqrt (CFC.sqrt ρ))ᴴ *
        (CFC.sqrt (CFC.sqrt ρ) * Y * CFC.sqrt (CFC.sqrt ρ))) := by
  let P := CFC.sqrt (CFC.sqrt ρ)
  have hP : Pᴴ = P := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1
  have hPP : P * P = CFC.sqrt ρ := CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg ρ)
  change _ = Matrix.trace ((P * X * P)ᴴ * (P * Y * P))
  have he : (P * X * P)ᴴ = P * Xᴴ * P := by
    simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
  rw [he, Matrix.trace_mul_comm (P * Xᴴ * P) (P * Y * P)]
  rw [show (P * Y * P) * (P * Xᴴ * P) = (P * Y) * (P * P) * (Xᴴ * P) from by
    simp only [Matrix.mul_assoc]]
  rw [hPP, Matrix.trace_mul_cycle (P * Y) (CFC.sqrt ρ) (Xᴴ * P)]
  rw [show Xᴴ * P * (P * Y) * CFC.sqrt ρ = Xᴴ * CFC.sqrt ρ * Y * CFC.sqrt ρ from by
    simp only [Matrix.mul_assoc, ← hPP]]
  rfl

theorem kmsInner_norm_le {D : ℕ} (ρ X Y : Operator D) :
    ‖kmsInner ρ X Y‖ ≤ kmsNorm ρ X * kmsNorm ρ Y := by
  let v (A : Operator D) := toEuclidean_fromVec (fun p : Fin D × Fin D => A p.1 p.2)
  have hi (A B : Operator D) : inner ℂ (v A) (v B) = Matrix.trace (Aᴴ * B) := by
    simp only [v, toEuclidean_fromVec, PiLp.inner_apply, RCLike.inner_apply,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    exact mul_comm _ _
  have hn (A : Operator D) :
      ‖v (CFC.sqrt (CFC.sqrt ρ) * A * CFC.sqrt (CFC.sqrt ρ))‖ = kmsNorm ρ A := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hi, ← kmsInner_self_eq]
    rfl
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (v (CFC.sqrt (CFC.sqrt ρ) * X * CFC.sqrt (CFC.sqrt ρ)))
    (v (CFC.sqrt (CFC.sqrt ρ) * Y * CFC.sqrt (CFC.sqrt ρ)))
  rw [hi, ← kmsInner_eq_hs, hn, hn] at h
  exact h

theorem traceNorm_kms_sandwich_le {D : ℕ} {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (X : Operator D) :
    Matrix.traceNorm (CFC.sqrt ρ * X * CFC.sqrt ρ) ≤ kmsNorm ρ X := by
  classical
  by_cases hD : D = 0
  · subst D
    have hx : X = 0 := Subsingleton.elim _ _
    simp [hx, kmsNorm, kmsInner, Matrix.traceNorm_zero]
  letI : NeZero D := ⟨hD⟩
  obtain ⟨U,hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (CFC.sqrt ρ * X * CFC.sqrt ρ)).1
  have hu : ‖(U.val)ᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    have hiso : U.valᴴ * U.val = 1 := by
      ext a b
      by_cases hab : a = b <;>
        simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, hab] using!
          congrFun (congrFun U.property.1 a) b
    have hsq := Matrix.l2_opNorm_conjTranspose_mul_self U.val
    rw [hiso, norm_one] at hsq
    nlinarith [norm_nonneg U.val]
  have hn : kmsNorm ρ U.valᴴ ≤ 1 := (kmsNorm_le_opNorm hρ _).trans_eq hu
  have hk := kmsInner_norm_le ρ U.valᴴ X
  have heq : kmsInner ρ U.valᴴ X = Matrix.trace (U.val * (CFC.sqrt ρ * X * CFC.sqrt ρ)) := by
    simp only [kmsInner, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  calc
    _ = (kmsInner ρ U.valᴴ X).re := by rw [heq,hU]
    _ ≤ ‖kmsInner ρ U.valᴴ X‖ := Complex.re_le_norm _
    _ ≤ kmsNorm ρ U.valᴴ * kmsNorm ρ X := hk
    _ ≤ kmsNorm ρ X := by
      have hx : 0 ≤ kmsNorm ρ X := Real.sqrt_nonneg _
      nlinarith

noncomputable def kmsDensityRatio {D : ℕ} (ρ X : Operator D) : Operator D :=
  (CFC.sqrt ρ)⁻¹ * X * (CFC.sqrt ρ)⁻¹

private theorem sqrt_inverse_pair {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef) :
    (CFC.sqrt ρ)⁻¹ * CFC.sqrt ρ = 1 ∧ CFC.sqrt ρ * (CFC.sqrt ρ)⁻¹ = 1 := by
  have hSS := CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  have hdet : (CFC.sqrt ρ).det ≠ 0 := by
    intro h
    apply (Matrix.PosDef.det_pos hρ).ne'
    rw [← hSS, Matrix.det_mul, h, zero_mul]
  have hunit := IsUnit.mk0 _ hdet
  exact ⟨Matrix.nonsing_inv_mul _ hunit, Matrix.mul_nonsing_inv _ hunit⟩

theorem kmsDensityRatio_sandwich {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (X : Operator D) : CFC.sqrt ρ * kmsDensityRatio ρ X * CFC.sqrt ρ = X := by
  obtain ⟨hl,hr⟩ := sqrt_inverse_pair hρ
  simp only [kmsDensityRatio, Matrix.mul_assoc, hl, Matrix.mul_one]
  rw [← Matrix.mul_assoc (CFC.sqrt ρ) (CFC.sqrt ρ)⁻¹ X, hr, Matrix.one_mul]

theorem kmsDensityRatio_reference {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef) :
    kmsDensityRatio ρ ρ = 1 := by
  obtain ⟨hl,hr⟩ := sqrt_inverse_pair hρ
  have hSS := CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  change (CFC.sqrt ρ)⁻¹ * ρ * (CFC.sqrt ρ)⁻¹ = 1
  calc
    _ = (CFC.sqrt ρ)⁻¹ * (CFC.sqrt ρ * CFC.sqrt ρ) * (CFC.sqrt ρ)⁻¹ := by rw [hSS]
    _ = 1 := by simp only [← Matrix.mul_assoc, hl, Matrix.one_mul, hr]

theorem kmsDensityRatio_center {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    {σ : Operator D} (hσ : IsDensityOperator σ) :
    kmsCenter ρ (kmsDensityRatio ρ σ) = kmsDensityRatio ρ (σ - ρ) := by
  have htrace : Matrix.trace (ρ * kmsDensityRatio ρ σ) = 1 := by
    calc
      _ = Matrix.trace (CFC.sqrt ρ * kmsDensityRatio ρ σ * CFC.sqrt ρ) := by
        rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]
      _ = Matrix.trace σ := congrArg Matrix.trace (kmsDensityRatio_sandwich hρ σ)
      _ = 1 := hσ.2
  rw [kmsCenter, htrace, one_smul]
  conv_lhs => rw [← kmsDensityRatio_reference hρ]
  simp only [kmsDensityRatio, Matrix.mul_sub, Matrix.sub_mul]

theorem traceDistance_le_kmsDensityRatio {D : ℕ} {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (σ : Operator D) :
    traceDistance σ ρ ≤ kmsNorm ρ (kmsDensityRatio ρ (σ - ρ)) / 2 := by
  have h := traceNorm_kms_sandwich_le hρ (kmsDensityRatio ρ (σ - ρ))
  rw [kmsDensityRatio_sandwich hfull] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem hasDerivAt_kmsEnergy {D : ℕ} (ρ : Operator D) {f : ℝ → Operator D}
    {v : Operator D} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun u => (kmsInner ρ (f u) (f u)).re)
      (2 * (kmsInner ρ (f t) v).re) t := by
  let J : Operator D →ₗ[ℝ] Operator D := {
    toFun := Matrix.conjTranspose
    map_add' := Matrix.conjTranspose_add
    map_smul' := fun r X => by simp }
  let T : Operator D →ₗ[ℝ] ℝ := {
    toFun := fun X => (Matrix.trace X).re
    map_add' := fun X Y => by simp
    map_smul' := fun r X => by simp }
  have hj := J.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf
  change HasDerivAt (fun u => (f u)ᴴ) vᴴ t at hj
  have hp := ((hj.mul_const (CFC.sqrt ρ)).mul hf).mul_const (CFC.sqrt ρ)
  have ht := T.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp
  change HasDerivAt (fun u => (kmsInner ρ (f u) (f u)).re)
    (Matrix.trace ((vᴴ * CFC.sqrt ρ * f t + (f t)ᴴ * CFC.sqrt ρ * v) * CFC.sqrt ρ)).re t at ht
  have hs : (kmsInner ρ v (f t)).re = (kmsInner ρ (f t) v).re := by
    rw [kmsInner_conjSym ρ v (f t)]
    exact Complex.conj_re _
  have he : (Matrix.trace ((vᴴ * CFC.sqrt ρ * f t + (f t)ᴴ * CFC.sqrt ρ * v) * CFC.sqrt ρ)).re =
      2 * (kmsInner ρ (f t) v).re := by
    simp only [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    change (kmsInner ρ v (f t)).re + (kmsInner ρ (f t) v).re = _
    rw [hs]
    ring
  rw [he] at ht
  exact ht

theorem kmsNorm_decay_of_gap {D : ℕ} (ρ : Operator D) (N : Operator D →ₗ[ℂ] Operator D)
    (γ : ℝ) (hgap : KmsGapAtLeast ρ N γ) (f : ℝ → Operator D)
    (hflow : ∀ u, HasDerivAt f (N (f u)) u)
    (hmean : ∀ u, Matrix.trace (ρ * f u) = 0) (t : ℝ) (ht : 0 ≤ t) :
    kmsNorm ρ (f t) ≤ Real.exp (-γ * t) * kmsNorm ρ (f 0) := by
  let E (u : ℝ) := (kmsInner ρ (f u) (f u)).re
  let E' (u : ℝ) := 2 * (kmsInner ρ (f u) (N (f u))).re
  have hd (u : ℝ) : HasDerivAt E (E' u) u := hasDerivAt_kmsEnergy ρ (hflow u)
  have hb (u : ℝ) : E' u ≤ (-2 * γ) * E u + 0 := by
    have h := hgap (f u)
    have hc : kmsCenter ρ (f u) = f u := by simp only [kmsCenter, hmean, zero_smul, sub_zero]
    have hn : (kmsNorm ρ (f u)) ^ 2 = E u := Real.sq_sqrt (kmsInner_re_self_nonneg ρ (f u))
    simp only [kmsVariance, hc, hn, kmsDirichlet, kmsInner_neg_right, Complex.neg_re] at h
    change 2 * (kmsInner ρ (f u) (N (f u))).re ≤ (-2 * γ) * E u + 0
    linarith
  have hG := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := E') (δ := E 0) (K := -2 * γ) (ε := 0) (a := 0) (b := t)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ r hr => (hd u).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun u _ => hb u) t ⟨ht, le_rfl⟩
  simp only [gronwallBound_ε0, sub_zero] at hG
  have hn (u : ℝ) : (kmsNorm ρ (f u)) ^ 2 = E u := Real.sq_sqrt (kmsInner_re_self_nonneg ρ (f u))
  have he : Real.exp ((-2 * γ) * t) = (Real.exp (-γ * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, ← hn 0, ← hn t] at hG
  have hp : 0 ≤ Real.exp (-γ * t) * kmsNorm ρ (f 0) :=
    mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sqrt_nonneg (kmsInner ρ (f t) (f t)).re]

theorem gkslHeisenbergMap_conjTranspose {D : ℕ} (G : GKSL D) (X : Operator D) :
    gkslHeisenbergMap G Xᴴ = (gkslHeisenbergMap G X)ᴴ := by
  simp only [gkslHeisenbergMap_apply, Matrix.conjTranspose_add, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, G.hamHermitian.eq, Complex.star_def,
    Complex.conj_I, map_div₀, map_one, map_ofNat]
  congr 1
  · simp only [smul_sub]
    module
  · apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mul_assoc]
    congr 1
    rw [add_comm]

theorem lindbladApply_kms_sandwich {D : ℕ} (G : GKSL D) (ρ : Operator D)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (X : Operator D) :
    lindbladApply G (CFC.sqrt ρ * X * CFC.sqrt ρ) =
      CFC.sqrt ρ * gkslHeisenbergMap G X * CFC.sqrt ρ := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Y
  have h := hself Yᴴ X
  simp only [kmsInner, Matrix.conjTranspose_conjTranspose,
    gkslHeisenbergMap_conjTranspose] at h
  rw [Matrix.trace_mul_comm Y, lindblad_heisenberg_trace_dual,
    Matrix.trace_mul_comm (CFC.sqrt ρ * X * CFC.sqrt ρ)]
  simpa only [Matrix.mul_assoc] using! h.symm

noncomputable def kmsDensityRatioMap {D : ℕ} (ρ : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  (LinearMap.mulRight ℂ (CFC.sqrt ρ)⁻¹).comp (LinearMap.mulLeft ℂ (CFC.sqrt ρ)⁻¹)

theorem kmsDensityRatioMap_apply {D : ℕ} (ρ X : Operator D) :
    kmsDensityRatioMap ρ X = kmsDensityRatio ρ X := rfl

theorem kmsDensityRatio_of_sandwich {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (X : Operator D) : kmsDensityRatio ρ (CFC.sqrt ρ * X * CFC.sqrt ρ) = X := by
  obtain ⟨hl,hr⟩ := sqrt_inverse_pair hρ
  simp only [kmsDensityRatio, ← Matrix.mul_assoc, hl, Matrix.one_mul]
  rw [Matrix.mul_assoc X, hr, Matrix.mul_one]

theorem trace_kmsDensityRatio {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef) (X : Operator D) :
    Matrix.trace (ρ * kmsDensityRatio ρ X) = Matrix.trace X := by
  calc
    _ = Matrix.trace (CFC.sqrt ρ * kmsDensityRatio ρ X * CFC.sqrt ρ) := by
      rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]
    _ = Matrix.trace X := congrArg Matrix.trace (kmsDensityRatio_sandwich hρ X)

theorem kmsDensityRatio_lindbladApply {D : ℕ} (G : GKSL D) {ρ : Operator D}
    (hρ : ρ.PosDef) (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (X : Operator D) :
    kmsDensityRatio ρ (lindbladApply G X) = gkslHeisenbergMap G (kmsDensityRatio ρ X) := by
  calc
    _ = kmsDensityRatio ρ (lindbladApply G (CFC.sqrt ρ * kmsDensityRatio ρ X * CFC.sqrt ρ)) := by
      rw [kmsDensityRatio_sandwich hρ]
    _ = kmsDensityRatio ρ (CFC.sqrt ρ * gkslHeisenbergMap G (kmsDensityRatio ρ X) * CFC.sqrt ρ) := by
      rw [lindbladApply_kms_sandwich G ρ hself]
    _ = _ := kmsDensityRatio_of_sandwich hρ _

theorem lindblad_traceDistance_le_of_heisenberg_kmsGap {D : ℕ} (G : GKSL D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ) {σ : Operator D}
    (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    traceDistance (lindbladSemigroup G t σ) ρ ≤
      Real.exp (-γ * t) * kmsNorm ρ (kmsDensityRatio ρ (σ - ρ)) / 2 := by
  let f (u : ℝ) := kmsDensityRatio ρ (lindbladSemigroup G u σ - ρ)
  have hzero := lindbladApply_eq_zero_of_heisenberg_kmsSelfAdjoint G ρ hρ.1 hself
  have hL (u : ℝ) : lindbladApply G (lindbladSemigroup G u σ - ρ) =
      lindbladApply G (lindbladSemigroup G u σ) := by
    change (lindbladMap G) (_ - _) = (lindbladMap G) _
    rw [map_sub]
    change _ - lindbladApply G ρ = _
    rw [hzero, sub_zero]
  have hf (u : ℝ) : HasDerivAt f (gkslHeisenbergMap G (f u)) u := by
    have hd := hasDerivAt_lindbladSemigroup G σ u
    have h := ((kmsDensityRatioMap ρ).restrictScalars ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u
      (hd.sub_const ρ)
    change HasDerivAt f (kmsDensityRatio ρ (lindbladApply G (lindbladSemigroup G u σ))) u at h
    rw [← hL u, kmsDensityRatio_lindbladApply G hfull hself] at h
    exact h
  have hm (u : ℝ) : Matrix.trace (ρ * f u) = 0 := by
    dsimp only [f]
    rw [trace_kmsDensityRatio hfull, Matrix.trace_sub, trace_lindbladSemigroup, hσ.2, hρ.2,
        sub_self]
  have hn := kmsNorm_decay_of_gap ρ (gkslHeisenbergMap G) γ hgap f hf hm t ht
  have hinit : f 0 = kmsDensityRatio ρ (σ - ρ) := by
    simp only [f, lindbladSemigroup_zero_apply]
  rw [hinit] at hn
  exact (traceDistance_le_kmsDensityRatio hρ hfull (lindbladSemigroup G t σ)).trans
    (div_le_div_of_nonneg_right hn (by norm_num))

theorem kmsNorm_densityRatio_le_inverse_sqrt {D : ℕ} {ρ σ : Operator D}
    (hρ : ρ.PosDef) (hσ : IsDensityOperator σ) :
    kmsNorm ρ (kmsDensityRatio ρ σ) ≤ ‖(CFC.sqrt ρ)⁻¹‖ := by
  let B := (CFC.sqrt ρ)⁻¹
  let R := CFC.sqrt σ
  let A := R * B * R
  have hB : B.PosSemidef := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).inv
  have hR : Rᴴ = R := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).1
  have hRR : R * R = σ := CFC.sqrt_mul_sqrt_self σ hσ.1.nonneg
  have hA : A.PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same R
    simpa only [hR] using! h
  have hinner (X : Operator D) : kmsInner ρ X (kmsDensityRatio ρ σ) = Matrix.trace (Xᴴ * σ) := by
    change Matrix.trace (Xᴴ * CFC.sqrt ρ * kmsDensityRatio ρ σ * CFC.sqrt ρ) = _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt ρ) (kmsDensityRatio ρ σ) (CFC.sqrt ρ),
        kmsDensityRatio_sandwich hρ]
  have he : kmsInner ρ (kmsDensityRatio ρ σ) (kmsDensityRatio ρ σ) = Matrix.trace (A * A) := by
    rw [hinner]
    have hn : (kmsDensityRatio ρ σ)ᴴ = B * σ * B := by
      change (B * σ * B)ᴴ = B * σ * B
      simp only [Matrix.conjTranspose_mul, hσ.1.isHermitian.eq, hB.isHermitian.eq, Matrix.mul_assoc]
    rw [hn]
    calc
      _ = Matrix.trace (R * (B * σ * B) * R) := by
        rw [Matrix.trace_mul_cycle R (B * σ * B) R, hRR, Matrix.trace_mul_comm σ (B * σ * B)]
      _ = Matrix.trace (A * A) := by
        congr 1
        dsimp only [A]
        simp only [Matrix.mul_assoc, ← hRR]
  let a : HermitianMat (Fin D) ℂ := ⟨A, hA.isHermitian⟩
  have ha : (0 : HermitianMat (Fin D) ℂ) ≤ a := HermitianMat.zero_le_iff.mpr hA
  have hp := HermitianMat.inner_le_mul_trace ha ha
  have hpur : (Matrix.trace (A * A)).re ≤ (Matrix.trace A).re ^ 2 := by
    simpa only [HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace, pow_two] using! hp
  have hta : Matrix.trace A = Matrix.trace (σ * B) := by
    dsimp only [A]
    rw [Matrix.trace_mul_cycle, hRR]
  have hsn : Matrix.traceNorm σ = 1 := by
    simpa only [hσ.2, Complex.one_re] using! congrArg Complex.re hσ.1.traceNorm_eq_trace
  have hb : (Matrix.trace A).re ≤ ‖B‖ := by
    calc
      _ = (Matrix.trace (σ * B)).re := congrArg Complex.re hta
      _ ≤ ‖Matrix.trace (σ * B)‖ := Complex.re_le_norm _
      _ ≤ Matrix.traceNorm (σ * B) := Matrix.abs_trace_le_traceNorm _
      _ ≤ Matrix.traceNorm σ * ‖B‖ := Matrix.traceNorm_mul_le_traceNorm_opNorm _ _
      _ = ‖B‖ := by rw [hsn, one_mul]
  have hta0 : 0 ≤ (Matrix.trace A).re := (Complex.le_def.mp hA.trace_nonneg).1
  have hn : (kmsNorm ρ (kmsDensityRatio ρ σ)) ^ 2 = (Matrix.trace (A * A)).re := by
    rw [kmsNorm, Real.sq_sqrt (kmsInner_re_self_nonneg _ _), he]
  have hnn : 0 ≤ kmsNorm ρ (kmsDensityRatio ρ σ) := Real.sqrt_nonneg _
  change kmsNorm ρ (kmsDensityRatio ρ σ) ≤ ‖B‖
  nlinarith [norm_nonneg B]

theorem kmsNorm_densityRatio_error_sq {D : ℕ} {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (hσ : IsDensityOperator σ) :
    (kmsNorm ρ (kmsDensityRatio ρ (σ - ρ))) ^ 2 + 1 =
      (kmsNorm ρ (kmsDensityRatio ρ σ)) ^ 2 := by
  let X := kmsDensityRatio ρ σ
  have hi : kmsInner ρ 1 X = 1 := by
    rw [kmsInner_one_left ρ X hρ.1.nonneg, Matrix.trace_mul_comm,
      trace_kmsDensityRatio hfull, hσ.2]
  have hj : kmsInner ρ X 1 = 1 := by rw [kmsInner_conjSym ρ X 1, hi, star_one]
  have hk : kmsInner ρ 1 1 = 1 := by
    rw [kmsInner_one_left ρ 1 hρ.1.nonneg, Matrix.one_mul, hρ.2]
  have hs (A B C : Operator D) : kmsInner ρ (A - B) C = kmsInner ρ A C - kmsInner ρ B C := by
    rw [kmsInner_conjSym ρ (A - B) C, kmsInner_sub_right, star_sub,
      ← kmsInner_conjSym ρ A C, ← kmsInner_conjSym ρ B C]
  have he : kmsDensityRatio ρ (σ - ρ) = X - 1 := by
    rw [← kmsDensityRatio_center hfull hσ, kmsCenter, trace_kmsDensityRatio hfull, hσ.2, one_smul]
  have hN (Y : Operator D) : (kmsNorm ρ Y) ^ 2 = (kmsInner ρ Y Y).re :=
    Real.sq_sqrt (kmsInner_re_self_nonneg ρ Y)
  rw [he, hN, hN, hs, kmsInner_sub_right, kmsInner_sub_right, hi, hj, hk]
  simp only [Complex.sub_re, Complex.one_re]
  ring

theorem kmsNorm_densityRatio_error_le_inverse_sqrt {D : ℕ} {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (hσ : IsDensityOperator σ) :
    kmsNorm ρ (kmsDensityRatio ρ (σ - ρ)) ≤ ‖(CFC.sqrt ρ)⁻¹‖ := by
  have hn := kmsNorm_densityRatio_le_inverse_sqrt hfull hσ
  have he := kmsNorm_densityRatio_error_sq hρ hfull hσ
  have h0 : 0 ≤ kmsNorm ρ (kmsDensityRatio ρ σ) := Real.sqrt_nonneg _
  have h1 : 0 ≤ kmsNorm ρ (kmsDensityRatio ρ (σ - ρ)) := Real.sqrt_nonneg _
  nlinarith [norm_nonneg ((CFC.sqrt ρ)⁻¹)]

theorem lindblad_traceDistance_le_inverse_sqrt {D : ℕ} (G : GKSL D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ) {σ : Operator D}
    (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    traceDistance (lindbladSemigroup G t σ) ρ ≤ Real.exp (-γ * t) * ‖(CFC.sqrt ρ)⁻¹‖ / 2 := by
  have h := lindblad_traceDistance_le_of_heisenberg_kmsGap G hρ hfull hself γ hgap hσ t ht
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (kmsNorm_densityRatio_error_le_inverse_sqrt hρ hfull hσ)
      (Real.exp_nonneg _)) (by norm_num))

theorem mixingTime_le_inverse_sqrt {D : ℕ} (G : GKSL D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ) (hγ : 0 < γ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    mixingTime G ρ η ≠ ⊤ ∧ (mixingTime G ρ η).toReal ≤
      Real.log ((‖(CFC.sqrt ρ)⁻¹‖ + 1) / η) / γ := by
  let b := ‖(CFC.sqrt ρ)⁻¹‖ + 1
  let T := Real.log (b / η) / γ
  have hb : 0 < b := by dsimp only [b]; positivity
  have harg : 0 < b / η := div_pos hb hη
  have hl : 0 ≤ Real.log (b / η) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hη).mpr
    dsimp only [b]
    nlinarith [norm_nonneg ((CFC.sqrt ρ)⁻¹)]
  have hT : 0 ≤ T := div_nonneg hl hγ.le
  have he : Real.exp (-γ * T) = η / b := by
    have hc : -γ * T = -Real.log (b / η) := by dsimp only [T]; field_simp
    rw [hc, Real.exp_neg, Real.exp_log harg, inv_div]
  have hq : (η / b) * ‖(CFC.sqrt ρ)⁻¹‖ / 2 ≤ η := by
    apply (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hb).mpr
    dsimp only [b]
    nlinarith [mul_nonneg hη.le (norm_nonneg ((CFC.sqrt ρ)⁻¹))]
  have hle : mixingTime G ρ η ≤ ENNReal.ofReal T := by
    apply sInf_le
    intro σ hσ
    rw [ENNReal.toReal_ofReal hT]
    have h := lindblad_traceDistance_le_inverse_sqrt G hρ hfull hself γ hgap hσ T hT
    rw [he] at h
    exact h.trans hq
  have hn : mixingTime G ρ η ≠ ⊤ := ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hn, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal hT] at h
end Qatlib.Concepts.LindbladFlow.GkslSemigroup
