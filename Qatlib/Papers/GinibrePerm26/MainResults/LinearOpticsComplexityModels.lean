/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GinibrePerm26.MainResults.LinearOpticsComplexityModelsDefs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BosonFock.PermAnalysis

namespace Qatlib.Papers.GinibrePerm26.MainResults

set_option autoImplicit false

open Qatlib.Papers.GinibrePerm26.MainResults
open scoped BigOperators Quaternion RealInnerProductSpace InnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

theorem dimR_real : dimR ℝ = 1 :=
  Module.finrank_self ℝ

theorem dimR_complex : dimR ℂ = 2 :=
  Complex.finrank_real_complex

theorem dimR_quaternion : dimR ℍ = 4 :=
  Quaternion.finrank_eq_four (R := ℝ)

theorem rowOrderedPermanent_fin_zero (S : Type*) [AddCommMonoid S] [Monoid S] :
    rowOrderedPermanent S (0 : Matrix (Fin 0) (Fin 0) S) = 1 := by
  have hterm : ∀ σ : Equiv.Perm (Fin 0),
      (List.ofFn fun i : Fin 0 => (0 : Matrix (Fin 0) (Fin 0) S) i (σ i)).prod = 1 := by
    intro σ
    simp
  calc
    rowOrderedPermanent S (0 : Matrix (Fin 0) (Fin 0) S)
        = ∑ σ : Equiv.Perm (Fin 0), (1 : S) :=
      Finset.sum_congr rfl fun σ _ => hterm σ
    _ = Finset.univ.card • (1 : S) := Finset.sum_const _
    _ = (1 : S) := by
      rw [Finset.card_univ, Fintype.card_perm]
      simp

theorem perCofactor_one (S : Type*) [AddCommMonoid S] [Monoid S]
    (B : Matrix (Fin 0) (Fin 1) S) (j : Fin 1) :
    @perCofactor S _ _ 1 B j = 1 := by
  have hsub : (fun i k => B i (deleteColumn j k)) = (0 : Matrix (Fin 0) (Fin 0) S) :=
    Subsingleton.elim _ _
  rw [perCofactor, hsub]
  exact rowOrderedPermanent_fin_zero S

theorem perCofactorColumn_one (S : Type*) [AddCommMonoid S] [Monoid S]
    (B : Matrix (Fin 0) (Fin 1) S) :
    @perCofactorColumn S _ _ 1 B = fun _ => 1 := by
  funext j
  exact perCofactor_one S B j

theorem deleteColumn_val (n : ℕ) (j : Fin n) (i : Fin (n - 1)) :
    (deleteColumn j i).val = if i.val < j.val then i.val else i.val + 1 := by
  unfold deleteColumn
  split_ifs <;> rfl

theorem deleteColumn_ne (n : ℕ) (j : Fin n) (i : Fin (n - 1)) :
    deleteColumn j i ≠ j := by
  intro h
  have hval : (deleteColumn j i).val = j.val := congrArg Fin.val h
  rw [deleteColumn_val] at hval
  split_ifs at hval with hi <;> omega

theorem deleteColumn_injective (n : ℕ) (j : Fin n) :
    Function.Injective (deleteColumn j) := by
  intro i₁ i₂ h
  have hval : (deleteColumn j i₁).val = (deleteColumn j i₂).val := congrArg Fin.val h
  rw [deleteColumn_val, deleteColumn_val] at hval
  split_ifs at hval <;> exact Fin.ext (by omega)

theorem deleteColumn_lt {n : ℕ} {j : Fin n} {i : Fin (n - 1)} (h : i.val < j.val) :
    (deleteColumn j i).val = i.val := by
  rw [deleteColumn_val, if_pos h]

theorem deleteColumn_ge {n : ℕ} {j : Fin n} {i : Fin (n - 1)} (h : j.val ≤ i.val) :
    (deleteColumn j i).val = i.val + 1 := by
  rw [deleteColumn_val, if_neg (not_lt.mpr h)]

theorem deleteColumn_strictMono (n : ℕ) (j : Fin n) :
    StrictMono (deleteColumn j) := by
  intro i₁ i₂ h
  rw [Fin.lt_def]
  have h1 : (deleteColumn j i₁).val = if i₁.val < j.val then i₁.val else i₁.val + 1 :=
    deleteColumn_val n j i₁
  have h2 : (deleteColumn j i₂).val = if i₂.val < j.val then i₂.val else i₂.val + 1 :=
    deleteColumn_val n j i₂
  rw [h1, h2]
  split_ifs <;> omega

theorem unitFirst_apply_of_ne_zero {S : Type*} [Semiring S] [Algebra ℝ S] {n : ℕ}
    (r : ℝ) (j : Fin n) (hj : j.val ≠ 0) :
    unitFirst S n r j = 0 := by
  simp [unitFirst, hj]

theorem unitFirst_apply_zero {S : Type*} [Semiring S] [Algebra ℝ S] {n : ℕ}
    (hn : 0 < n) (r : ℝ) :
    unitFirst S n r ⟨0, hn⟩ = algebraMap ℝ S r := by
  simp [unitFirst]

theorem vecInner_zero_left {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (y : Fin n → S) :
    vecInner S (fun _ => 0) y = 0 := by
  simp [vecInner]

theorem vecInner_zero_right {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (x : Fin n → S) :
    vecInner S x (fun _ => 0) = 0 := by
  simp [vecInner]

theorem gammaProductLaw_of_le_one {m β : ℕ} (hm : m ≤ 1) :
    gammaProductLaw m β = Measure.dirac (1 : ℝ) := by
  rw [gammaProductLaw, if_pos hm]

theorem isRealNonneg_ofReal {r : ℝ} (hr : 0 ≤ r) :
    IsRealNonneg (r : ℂ) := by
  constructor
  · simp
  · simpa using hr

theorem isRealNonneg_one : IsRealNonneg (1 : ℂ) :=
  isRealNonneg_ofReal zero_le_one

theorem vecCF_zero {S : Type*} [NormedDivisionRing S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ : Measure (Fin n → S)) [IsProbabilityMeasure μ] :
    vecCF S μ (fun _ => 0) = 1 := by
  have hzero : ∀ x : Fin n → S,
      Complex.exp (Complex.I * ((vecInner S (fun _ => 0) x : ℝ) : ℂ)) = 1 := by
    intro x
    simp [vecInner]
  calc
    vecCF S μ (fun _ => 0) = ∫ _x : Fin n → S, (1 : ℂ) ∂μ :=
      integral_congr_ae (ae_of_all _ hzero)
    _ = 1 := by
      rw [MeasureTheory.integral_const]
      simp

theorem vecCF_zero_isRealNonneg {S : Type*} [NormedDivisionRing S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ : Measure (Fin n → S)) [IsProbabilityMeasure μ] :
    IsRealNonneg (vecCF S μ (fun _ => 0)) := by
  rw [vecCF_zero]
  exact isRealNonneg_one

theorem thm11SmallBall_complex {C : ℝ} :
    Thm11SmallBall ℂ C ↔ ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → ∀ z : ℂ,
      ((normalizedPermanentLaw ℂ n) (Metric.closedBall z t)).toReal ≤
        C * (n : ℝ) * t ^ 2 := by
  constructor
  · intro h n hn t ht z
    have hle := h n hn t ht z
    have hexp : (((Module.finrank ℝ ℂ : ℝ) + 2) / 4) = 1 := by
      rw [Complex.finrank_real_complex]
      norm_num
    have hpow : t ^ Module.finrank ℝ ℂ = t ^ 2 := by
      rw [Complex.finrank_real_complex]
    rw [hexp, hpow, Real.rpow_one] at hle
    exact hle
  · intro h n hn ε hε z
    have hle := h n hn ε hε z
    have hexp : (((Module.finrank ℝ ℂ : ℝ) + 2) / 4) = 1 := by
      rw [Complex.finrank_real_complex]
      norm_num
    have hpow : ε ^ Module.finrank ℝ ℂ = ε ^ 2 := by
      rw [Complex.finrank_real_complex]
    rw [hexp, hpow, Real.rpow_one]
    exact hle

theorem complexSmallBallCnT2_iff_thm11SmallBall :
    ComplexSmallBallCnT2 ↔ ∃ C : ℝ, 0 < C ∧ Thm11SmallBall ℂ C := by
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, thm11SmallBall_complex.mpr h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, thm11SmallBall_complex.mp h⟩

theorem complexSmallBallCnT2_of_gaussianPermanentAnticoncentration
    (h : GaussianPermanentAnticoncentration ℂ) : ComplexSmallBallCnT2 := by
  obtain ⟨_, C, hC, hs⟩ := h
  exact complexSmallBallCnT2_iff_thm11SmallBall.mpr ⟨C, hC, hs⟩

theorem gaussianPermanentAnticoncentration_complex_of_parts
    (hd : ∃ C : ℝ, 0 < C ∧ Thm11Density ℂ C) (hs : ComplexSmallBallCnT2) :
    GaussianPermanentAnticoncentration ℂ := by
  obtain ⟨C, hC, h⟩ := complexSmallBallCnT2_iff_thm11SmallBall.mp hs
  exact ⟨hd, C, hC, h⟩

theorem laplaceLE_refl (μ : Measure ℝ) :
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE μ μ :=
  fun _ _ => le_refl _

theorem laplaceLE_trans {μ ν ρ : Measure ℝ}
    (hμν : Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE μ ν) (hνρ : Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE ν ρ) :
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE μ ρ :=
  fun s hs => le_trans (hνρ s hs) (hμν s hs)

theorem laplaceLE_dirac_iff {u v : ℝ} :
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE (Measure.dirac u) (Measure.dirac v) ↔ u ≤ v := by
  constructor
  · intro h
    have h1 : Real.exp (-(1 : ℝ) * u) ≥ Real.exp (-(1 : ℝ) * v) := by
      simpa only [MeasureTheory.integral_dirac] using h 1 zero_le_one
    have h2 : Real.exp (-(1 : ℝ) * v) ≤ Real.exp (-(1 : ℝ) * u) := h1
    rw [Real.exp_le_exp] at h2
    linarith
  · intro h s hs
    simp only [MeasureTheory.integral_dirac]
    have huv : s * u ≤ s * v := mul_le_mul_of_nonneg_left h hs
    apply Real.exp_le_exp.mpr
    linarith

theorem matrixLaplaceLEVec_refl {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ : Measure (Fin n → S)) :
    matrixLaplaceLEVec S μ μ :=
  fun _ _ => le_refl _

theorem matrixLaplaceLEVec_trans {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} {μ ν ρ : Measure (Fin n → S)}
    (hμν : matrixLaplaceLEVec S μ ν) (hνρ : matrixLaplaceLEVec S ν ρ) :
    matrixLaplaceLEVec S μ ρ :=
  fun Q hQ => le_trans (hνρ Q hQ) (hμν Q hQ)

theorem gaussianCofactorInduction_laplaceLE
    {S : Type*} [NormedDivisionRing S] [NormedAlgebra ℝ S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    {n : ℕ} (hn : 1 ≤ n) (h : GaussianCofactorInduction S) :
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE (gammaProductLaw n (dimR S))
      (Measure.map (fun x : Fin n → S => vecNormSq S x) (cofactorColumnLaw S n)) :=
  h.2.1 n hn

abbrev CofactorL2 (S : Type*) (n : ℕ) := WithLp 2 (Fin n → S)

theorem vecInner_eq_piLp_inner {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (x y : Fin n → S) :
    vecInner S x y =
      ⟪(WithLp.toLp 2 x : CofactorL2 S n), WithLp.toLp 2 y⟫_ℝ :=
  PiLp.inner_apply (𝕜 := ℝ) (f := fun _ : Fin n => S) (WithLp.toLp 2 x) (WithLp.toLp 2 y)

def toL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] (n : ℕ)
    (Q : (Fin n → S) →ₗ[ℝ] (Fin n → S)) : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n :=
  (WithLp.linearEquiv 2 ℝ (Fin n → S)).symm.toLinearMap ∘ₗ Q ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → S)).toLinearMap

def ofL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] (n : ℕ)
    (Q' : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n) : (Fin n → S) →ₗ[ℝ] (Fin n → S) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → S)).toLinearMap ∘ₗ Q' ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → S)).symm.toLinearMap

theorem toL2_apply {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q : (Fin n → S) →ₗ[ℝ] (Fin n → S)) (x : Fin n → S) :
    toL2 n Q (WithLp.toLp 2 x) = WithLp.toLp 2 (Q x) := by
  simp [toL2]

theorem ofL2_apply {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q' : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n) (x : Fin n → S) :
    ofL2 n Q' x = WithLp.ofLp (Q' (WithLp.toLp 2 x)) := by
  simp [ofL2]

theorem inner_toL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q : (Fin n → S) →ₗ[ℝ] (Fin n → S)) (x : Fin n → S) :
    ⟪(WithLp.toLp 2 x : CofactorL2 S n), toL2 n Q (WithLp.toLp 2 x)⟫_ℝ
      = vecInner S x (Q x) := by
  rw [toL2_apply, vecInner_eq_piLp_inner]

theorem inner_ofL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q' : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n) (x : Fin n → S) :
    ⟪(WithLp.toLp 2 x : CofactorL2 S n), Q' (WithLp.toLp 2 x)⟫_ℝ
      = vecInner S x (ofL2 n Q' x) := by
  rw [ofL2_apply, vecInner_eq_piLp_inner]

def withLpMeasurableEquiv {S : Type*} [NormedAddCommGroup S] [MeasurableSpace S]
    (n : ℕ) : (Fin n → S) ≃ᵐ CofactorL2 S n :=
  { toEquiv := (WithLp.equiv 2 (Fin n → S)).symm
    measurable_toFun := WithLp.measurable_toLp 2 (Fin n → S)
    measurable_invFun := WithLp.measurable_ofLp 2 (Fin n → S) }

theorem integral_toLp {S : Type*} [NormedAddCommGroup S] [MeasurableSpace S]
    {n : ℕ} (μ : Measure (Fin n → S)) (f : CofactorL2 S n → ℝ) :
    ∫ y, f y ∂(Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) μ)
      = ∫ x, f (WithLp.toLp 2 x) ∂μ :=
  MeasureTheory.integral_map_equiv (withLpMeasurableEquiv n) f

theorem matrixLaplaceLEVec_iff_matrixLaplaceLE
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ ν : Measure (Fin n → S)) :
    matrixLaplaceLEVec S μ ν ↔
      Qatlib.Concepts.BosonFock.PermAnalysis.matrixLaplaceLE
        (Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) μ)
        (Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) ν) := by
  constructor
  · intro h Q' hQ'
    have hQpsd : ∀ x : Fin n → S, 0 ≤ vecInner S x (ofL2 n Q'.toLinearMap x) := by
      intro x
      rw [← inner_ofL2]
      exact hQ' _
    have hge := h (ofL2 n Q'.toLinearMap) hQpsd
    have hμ : ∫ y, Real.exp (-⟪y, Q' y⟫_ℝ)
        ∂(Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) μ)
        = ∫ x, Real.exp (-vecInner S x (ofL2 n Q'.toLinearMap x)) ∂μ := by
      rw [integral_toLp]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show Real.exp (-⟪(WithLp.toLp 2 x : CofactorL2 S n), Q' (WithLp.toLp 2 x)⟫_ℝ)
        = Real.exp (-vecInner S x (ofL2 n Q'.toLinearMap x))
      rw [← inner_ofL2]
      rfl
    have hν : ∫ y, Real.exp (-⟪y, Q' y⟫_ℝ)
        ∂(Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) ν)
        = ∫ x, Real.exp (-vecInner S x (ofL2 n Q'.toLinearMap x)) ∂ν := by
      rw [integral_toLp]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show Real.exp (-⟪(WithLp.toLp 2 x : CofactorL2 S n), Q' (WithLp.toLp 2 x)⟫_ℝ)
        = Real.exp (-vecInner S x (ofL2 n Q'.toLinearMap x))
      rw [← inner_ofL2]
      rfl
    rw [hμ, hν]
    exact hge
  · intro h Q hQ
    have hQ'psd : ∀ y : CofactorL2 S n,
        0 ≤ ⟪y, (LinearMap.toContinuousLinearMap (toL2 n Q)) y⟫_ℝ := by
      intro y
      rw [← WithLp.toLp_ofLp 2 y]
      show 0 ≤ ⟪(WithLp.toLp 2 y.ofLp : CofactorL2 S n),
        toL2 n Q (WithLp.toLp 2 y.ofLp)⟫_ℝ
      rw [inner_toL2]
      exact hQ _
    have hge := h (LinearMap.toContinuousLinearMap (toL2 n Q)) hQ'psd
    have hμ : ∫ y, Real.exp (-⟪y, (LinearMap.toContinuousLinearMap (toL2 n Q)) y⟫_ℝ)
        ∂(Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) μ)
        = ∫ x, Real.exp (-vecInner S x (Q x)) ∂μ := by
      rw [integral_toLp]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show Real.exp (-⟪(WithLp.toLp 2 x : CofactorL2 S n),
        toL2 n Q (WithLp.toLp 2 x)⟫_ℝ)
        = Real.exp (-vecInner S x (Q x))
      rw [inner_toL2]
    have hν : ∫ y, Real.exp (-⟪y, (LinearMap.toContinuousLinearMap (toL2 n Q)) y⟫_ℝ)
        ∂(Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) ν)
        = ∫ x, Real.exp (-vecInner S x (Q x)) ∂ν := by
      rw [integral_toLp]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show Real.exp (-⟪(WithLp.toLp 2 x : CofactorL2 S n),
        toL2 n Q (WithLp.toLp 2 x)⟫_ℝ)
        = Real.exp (-vecInner S x (Q x))
      rw [inner_toL2]
    rw [hμ, hν] at hge
    exact hge

theorem gaussianCofactorInduction_matrixLaplaceLEVec
    {S : Type*} [NormedDivisionRing S] [NormedAlgebra ℝ S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    {n : ℕ} (hn : 1 ≤ n) (h : GaussianCofactorInduction S) :
    matrixLaplaceLEVec S (gammaScaledGaussianColumnLaw S n) (cofactorColumnLaw S n) :=
  h.1 n hn

theorem gaussianCofactorInduction_fourier
    {S : Type*} [NormedDivisionRing S] [NormedAlgebra ℝ S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    {n : ℕ} (hn : 1 ≤ n) (h : GaussianCofactorInduction S) :
    ∀ z : Fin (n + 1) → S,
      IsRealNonneg (vecCF S (cofactorColumnLaw S (n + 1)) z) ∧
      IsRealNonneg (vecCF S (gammaScaledGaussianColumnLaw S (n + 1)) z) ∧
      (vecCF S (cofactorColumnLaw S (n + 1)) z).re ≤
        (vecCF S (gammaScaledGaussianColumnLaw S (n + 1)) z).re :=
  h.2.2 n hn

end

end Qatlib.Papers.GinibrePerm26.MainResults
