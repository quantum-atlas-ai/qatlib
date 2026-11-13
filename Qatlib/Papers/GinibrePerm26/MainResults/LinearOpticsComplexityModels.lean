/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GinibrePerm26.MainResults.LinearOpticsComplexityModelsDefs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Comparison tools for Gaussian permanent models

This module proves elementary identities for the permanent and cofactor models, specializes the
small-ball predicate to complex scalars, and relates vector quadratic-form comparisons to the
Hilbert-space formulation. The final comparison theorems extract the scalar, matrix, and Fourier
conclusions supplied by `GaussianCofactorInduction`. See [KoehlerLeung2026].

## Main statements

* `thm11SmallBall_complex`: Over `ℂ`, `Thm11SmallBall` is equivalent to the uniform closed-ball
  bound `C * n * t²` for positive `n` and `t`.
* `matrixLaplaceLEVec_iff_matrixLaplaceLE`: The coordinate quadratic-form Laplace comparison is
  equivalent to the Hilbert-space matrix Laplace comparison after pushing both measures to
  `CofactorL2`.
* `gaussianCofactorInduction_fourier`: For `n ≥ 1`, `GaussianCofactorInduction` supplies real
  nonnegative characteristic functions in dimension `n + 1` and bounds the cofactor
  characteristic function above by the gamma-scaled Gaussian characteristic function.

## References

* [Koehler and Leung, 2026][KoehlerLeung2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BosonFock.PermAnalysis

namespace Qatlib.Papers.GinibrePerm26.MainResults

set_option autoImplicit false

open Qatlib.Papers.GinibrePerm26.MainResults
open scoped BigOperators Quaternion RealInnerProductSpace InnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

/-- The real dimension of `ℝ` is one. -/
theorem dimR_real : dimR ℝ = 1 :=
  Module.finrank_self ℝ

/-- The real dimension of `ℂ` is two. -/
theorem dimR_complex : dimR ℂ = 2 :=
  Complex.finrank_real_complex

/-- The real dimension of the quaternions is four. -/
theorem dimR_quaternion : dimR ℍ = 4 :=
  Quaternion.finrank_eq_four (R := ℝ)

/-- The row-ordered permanent of the empty square matrix is one. -/
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

/-- Every permanent cofactor of a matrix with zero rows and one column is one. -/
theorem perCofactor_one (S : Type*) [AddCommMonoid S] [Monoid S]
    (B : Matrix (Fin 0) (Fin 1) S) (j : Fin 1) :
    @perCofactor S _ _ 1 B j = 1 := by
  have hsub : (fun i k => B i (deleteColumn j k)) = (0 : Matrix (Fin 0) (Fin 0) S) :=
    Subsingleton.elim _ _
  rw [perCofactor, hsub]
  exact rowOrderedPermanent_fin_zero S

/-- The permanent cofactor column of a matrix with zero rows and one column is the constant-one
vector. -/
theorem perCofactorColumn_one (S : Type*) [AddCommMonoid S] [Monoid S]
    (B : Matrix (Fin 0) (Fin 1) S) :
    @perCofactorColumn S _ _ 1 B = fun _ => 1 := by
  funext j
  exact perCofactor_one S B j

/-- Deleting column `j` leaves an index below `j` unchanged and increases every other index by
one. -/
theorem deleteColumn_val (n : ℕ) (j : Fin n) (i : Fin (n - 1)) :
    (deleteColumn j i).val = if i.val < j.val then i.val else i.val + 1 := by
  unfold deleteColumn
  split_ifs <;> rfl

/-- An index produced by `deleteColumn j` is never `j`. -/
theorem deleteColumn_ne (n : ℕ) (j : Fin n) (i : Fin (n - 1)) :
    deleteColumn j i ≠ j := by
  intro h
  have hval : (deleteColumn j i).val = j.val := congrArg Fin.val h
  rw [deleteColumn_val] at hval
  split_ifs at hval with hi <;> omega

/-- The index map that skips a fixed column is injective. -/
theorem deleteColumn_injective (n : ℕ) (j : Fin n) :
    Function.Injective (deleteColumn j) := by
  intro i₁ i₂ h
  have hval : (deleteColumn j i₁).val = (deleteColumn j i₂).val := congrArg Fin.val h
  rw [deleteColumn_val, deleteColumn_val] at hval
  split_ifs at hval <;> exact Fin.ext (by omega)

/-- The column-deletion map leaves an index strictly below the deleted column unchanged. -/
theorem deleteColumn_lt {n : ℕ} {j : Fin n} {i : Fin (n - 1)} (h : i.val < j.val) :
    (deleteColumn j i).val = i.val := by
  rw [deleteColumn_val, if_pos h]

/-- The column-deletion map increases an index at or above the deleted column by one. -/
theorem deleteColumn_ge {n : ℕ} {j : Fin n} {i : Fin (n - 1)} (h : j.val ≤ i.val) :
    (deleteColumn j i).val = i.val + 1 := by
  rw [deleteColumn_val, if_neg (not_lt.mpr h)]

/-- The index map that skips a fixed column is strictly increasing. -/
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

/-- The vector `unitFirst` vanishes at every coordinate whose index is nonzero. -/
theorem unitFirst_apply_of_ne_zero {S : Type*} [Semiring S] [Algebra ℝ S] {n : ℕ}
    (r : ℝ) (j : Fin n) (hj : j.val ≠ 0) :
    unitFirst S n r j = 0 := by
  simp [unitFirst, hj]

/-- For positive dimension, the zeroth coordinate of `unitFirst S n r` is the algebra image of
`r`. -/
theorem unitFirst_apply_zero {S : Type*} [Semiring S] [Algebra ℝ S] {n : ℕ}
    (hn : 0 < n) (r : ℝ) :
    unitFirst S n r ⟨0, hn⟩ = algebraMap ℝ S r := by
  simp [unitFirst]

/-- The vector inner product with a zero left argument is zero. -/
theorem vecInner_zero_left {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (y : Fin n → S) :
    vecInner S (fun _ => 0) y = 0 := by
  simp [vecInner]

/-- The vector inner product with a zero right argument is zero. -/
theorem vecInner_zero_right {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (x : Fin n → S) :
    vecInner S x (fun _ => 0) = 0 := by
  simp [vecInner]

/-- For `m ≤ 1`, the gamma product measure is the Dirac measure at one. -/
theorem gammaProductLaw_of_le_one {m β : ℕ} (hm : m ≤ 1) :
    gammaProductLaw m β = Measure.dirac (1 : ℝ) := by
  rw [gammaProductLaw, if_pos hm]

/-- A nonnegative real number cast to `ℂ` satisfies `IsRealNonneg`. -/
theorem isRealNonneg_ofReal {r : ℝ} (hr : 0 ≤ r) :
    IsRealNonneg (r : ℂ) := by
  constructor
  · simp
  · simpa using hr

/-- The complex number one satisfies `IsRealNonneg`. -/
theorem isRealNonneg_one : IsRealNonneg (1 : ℂ) :=
  isRealNonneg_ofReal zero_le_one

/-- The characteristic function of a probability measure on vectors is one at the zero vector. -/
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

/-- At the zero vector, the characteristic function of a probability measure is real and
nonnegative. -/
theorem vecCF_zero_isRealNonneg {S : Type*} [NormedDivisionRing S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ : Measure (Fin n → S)) [IsProbabilityMeasure μ] :
    IsRealNonneg (vecCF S μ (fun _ => 0)) := by
  rw [vecCF_zero]
  exact isRealNonneg_one

/-- Over `ℂ`, `Thm11SmallBall` is equivalent to the uniform closed-ball bound `C * n * t²` for
positive `n` and `t`. -/
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

/-- The complex `C*n*t²` small-ball predicate is equivalent to the existence of a positive
constant satisfying `Thm11SmallBall ℂ`. -/
theorem complexSmallBallCnT2_iff_thm11SmallBall :
    ComplexSmallBallCnT2 ↔ ∃ C : ℝ, 0 < C ∧ Thm11SmallBall ℂ C := by
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, thm11SmallBall_complex.mpr h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, thm11SmallBall_complex.mp h⟩

/-- The complex Gaussian permanent anticoncentration predicate implies the `C*n*t²` small-ball
predicate. -/
theorem complexSmallBallCnT2_of_gaussianPermanentAnticoncentration
    (h : GaussianPermanentAnticoncentration ℂ) : ComplexSmallBallCnT2 := by
  obtain ⟨_, C, hC, hs⟩ := h
  exact complexSmallBallCnT2_iff_thm11SmallBall.mpr ⟨C, hC, hs⟩

/-- A positive-constant density bound together with the complex `C*n*t²` small-ball bound yields
`GaussianPermanentAnticoncentration ℂ`. -/
theorem gaussianPermanentAnticoncentration_complex_of_parts
    (hd : ∃ C : ℝ, 0 < C ∧ Thm11Density ℂ C) (hs : ComplexSmallBallCnT2) :
    GaussianPermanentAnticoncentration ℂ := by
  obtain ⟨C, hC, h⟩ := complexSmallBallCnT2_iff_thm11SmallBall.mp hs
  exact ⟨hd, C, hC, h⟩

/-- The scalar Laplace comparison relation is reflexive. -/
theorem laplaceLE_refl (μ : Measure ℝ) :
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE μ μ :=
  fun _ _ => le_refl _

/-- The scalar Laplace comparison relation is transitive. -/
theorem laplaceLE_trans {μ ν ρ : Measure ℝ}
    (hμν : Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE μ ν) (hνρ : Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE ν ρ) :
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE μ ρ :=
  fun s hs => le_trans (hνρ s hs) (hμν s hs)

/-- Scalar Laplace comparison between Dirac measures at `u` and `v` is equivalent to `u ≤ v`. -/
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

/-- The quadratic-form Laplace comparison relation on vector measures is reflexive. -/
theorem matrixLaplaceLEVec_refl {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ : Measure (Fin n → S)) :
    matrixLaplaceLEVec S μ μ :=
  fun _ _ => le_refl _

/-- The quadratic-form Laplace comparison relation on vector measures is transitive. -/
theorem matrixLaplaceLEVec_trans {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} {μ ν ρ : Measure (Fin n → S)}
    (hμν : matrixLaplaceLEVec S μ ν) (hνρ : matrixLaplaceLEVec S ν ρ) :
    matrixLaplaceLEVec S μ ρ :=
  fun Q hQ => le_trans (hνρ Q hQ) (hμν Q hQ)

/-- For positive dimension, `GaussianCofactorInduction` supplies the scalar Laplace comparison
from the gamma product measure to the squared-norm distribution of the permanent cofactor
column. -/
theorem gaussianCofactorInduction_laplaceLE
    {S : Type*} [NormedDivisionRing S] [NormedAlgebra ℝ S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    {n : ℕ} (hn : 1 ≤ n) (h : GaussianCofactorInduction S) :
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE (gammaProductLaw n (dimR S))
      (Measure.map (fun x : Fin n → S => vecNormSq S x) (cofactorColumnLaw S n)) :=
  h.2.1 n hn

/-- The type `WithLp 2 (Fin n → S)` of finite vectors in the `L²` representation. -/
abbrev CofactorL2 (S : Type*) (n : ℕ) := WithLp 2 (Fin n → S)

/-- The coordinatewise sum `vecInner` equals the real inner product of the corresponding
`CofactorL2` vectors. -/
theorem vecInner_eq_piLp_inner {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (x y : Fin n → S) :
    vecInner S x y =
      ⟪(WithLp.toLp 2 x : CofactorL2 S n), WithLp.toLp 2 y⟫_ℝ :=
  PiLp.inner_apply (𝕜 := ℝ) (f := fun _ : Fin n => S) (WithLp.toLp 2 x) (WithLp.toLp 2 y)

/-- A real linear endomorphism of coordinate vectors transported to `CofactorL2` using the
canonical linear equivalence. -/
def toL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] (n : ℕ)
    (Q : (Fin n → S) →ₗ[ℝ] (Fin n → S)) : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n :=
  (WithLp.linearEquiv 2 ℝ (Fin n → S)).symm.toLinearMap ∘ₗ Q ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → S)).toLinearMap

/-- A real linear endomorphism of `CofactorL2` transported back to coordinate vectors. -/
def ofL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] (n : ℕ)
    (Q' : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n) : (Fin n → S) →ₗ[ℝ] (Fin n → S) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → S)).toLinearMap ∘ₗ Q' ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → S)).symm.toLinearMap

/-- Applying the transported map to an `L²` vector agrees with transporting the result of the
original coordinate map. -/
theorem toL2_apply {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q : (Fin n → S) →ₗ[ℝ] (Fin n → S)) (x : Fin n → S) :
    toL2 n Q (WithLp.toLp 2 x) = WithLp.toLp 2 (Q x) := by
  simp [toL2]

/-- The map transported from `CofactorL2` is evaluated by converting the input, applying the
map, and converting back. -/
theorem ofL2_apply {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q' : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n) (x : Fin n → S) :
    ofL2 n Q' x = WithLp.ofLp (Q' (WithLp.toLp 2 x)) := by
  simp [ofL2]

/-- The quadratic expression for a map transported to `CofactorL2` equals its coordinate
expression using `vecInner`. -/
theorem inner_toL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q : (Fin n → S) →ₗ[ℝ] (Fin n → S)) (x : Fin n → S) :
    ⟪(WithLp.toLp 2 x : CofactorL2 S n), toL2 n Q (WithLp.toLp 2 x)⟫_ℝ
      = vecInner S x (Q x) := by
  rw [toL2_apply, vecInner_eq_piLp_inner]

/-- The quadratic expression of a map on `CofactorL2` equals the coordinate expression for its
transported map. -/
theorem inner_ofL2 {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (Q' : CofactorL2 S n →ₗ[ℝ] CofactorL2 S n) (x : Fin n → S) :
    ⟪(WithLp.toLp 2 x : CofactorL2 S n), Q' (WithLp.toLp 2 x)⟫_ℝ
      = vecInner S x (ofL2 n Q' x) := by
  rw [ofL2_apply, vecInner_eq_piLp_inner]

/-- The measurable equivalence between coordinate vectors and their `CofactorL2` representation. -/
def withLpMeasurableEquiv {S : Type*} [NormedAddCommGroup S] [MeasurableSpace S]
    (n : ℕ) : (Fin n → S) ≃ᵐ CofactorL2 S n :=
  { toEquiv := (WithLp.equiv 2 (Fin n → S)).symm
    measurable_toFun := WithLp.measurable_toLp 2 (Fin n → S)
    measurable_invFun := WithLp.measurable_ofLp 2 (Fin n → S) }

/-- Integration against the pushforward under `WithLp.toLp 2` equals integration of the composed
function against the original measure. -/
theorem integral_toLp {S : Type*} [NormedAddCommGroup S] [MeasurableSpace S]
    {n : ℕ} (μ : Measure (Fin n → S)) (f : CofactorL2 S n → ℝ) :
    ∫ y, f y ∂(Measure.map (WithLp.toLp 2 : (Fin n → S) → CofactorL2 S n) μ)
      = ∫ x, f (WithLp.toLp 2 x) ∂μ :=
  MeasureTheory.integral_map_equiv (withLpMeasurableEquiv n) f

/-- The coordinate quadratic-form Laplace comparison is equivalent to the Hilbert-space matrix
Laplace comparison after pushing both measures to `CofactorL2`. -/
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

/-- For positive dimension, `GaussianCofactorInduction` supplies the vector Laplace comparison
from the gamma-scaled Gaussian column measure to the permanent cofactor column measure. -/
theorem gaussianCofactorInduction_matrixLaplaceLEVec
    {S : Type*} [NormedDivisionRing S] [NormedAlgebra ℝ S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    {n : ℕ} (hn : 1 ≤ n) (h : GaussianCofactorInduction S) :
    matrixLaplaceLEVec S (gammaScaledGaussianColumnLaw S n) (cofactorColumnLaw S n) :=
  h.1 n hn

/-- For `n ≥ 1`, `GaussianCofactorInduction` supplies real nonnegative characteristic functions
in dimension `n + 1` and bounds the cofactor characteristic function above by the
gamma-scaled Gaussian characteristic function. -/
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
