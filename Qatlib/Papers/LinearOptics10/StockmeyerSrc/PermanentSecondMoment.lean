/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.EmptyBoundary
public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexMixed
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.ColoredCycleCount
import Qatlib.Papers.LinearOptics10.StockmeyerSrc.MomentModel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.FinCases

@[expose] public section


/-! # The actual second moment of the normalized Gaussian permanent

Fixed source: Aaronson--Arkhipov, arXiv:1011.3245v1, Lemma 56 (p. 73):
`E[P_n^2] = n + 1` for the normalized permanent random variable
`P_n = |Per(X)|^2 / n!` of a complex Ginibre matrix `X`.  The exact source
integral is evaluated here at the concrete dimensions `n = 1` and `n = 2`
against the actual product Gaussian density: balanced complex Gaussian moments
are factorial and unbalanced ones vanish by the rotational symmetry of the
plane density.  The arbitrary-`n` fourth permanent moment remains a separate
open obligation and is not asserted.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder
open MeasureTheory
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.PermanentSecondMoment
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib.Foundations.ProbabilityCore.Concentration
open Qatlib.Papers.LinearOptics10.StockmeyerSrc.EmptyBoundary
open Qatlib.Papers.LinearOptics10.StockmeyerSrc.ColoredCycleCount

/-- The actual second moment of the normalized permanent random variable `P_n`. -/
noncomputable def permSqMoment (n : ℕ) : ℝ :=
  ∫ X : Fin n → Fin n → ℂ, (permMomentVar X) ^ 2 * loGaussianMatDensity n X ∂volume

/-! ## Rotational invariance of the plane density -/

/-- Multiplication by a unit complex number as a real-linear isometry. -/
noncomputable def mulUnitLi (u : ℂ) (hu : ‖u‖ = 1) : ℂ →ₗᵢ[ℝ] ℂ where
  toLinearMap :=
    { toFun := fun z => u * z
      map_add' := fun a b => mul_add u a b
      map_smul' := fun r z => by
        rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, RingHom.id_apply,
          mul_left_comm] }
  norm_map' := fun z => by simp [hu]

/-- Multiplication by a unit complex number as a real-linear isometric equivalence. -/
noncomputable def mulUnitLie (u : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  LinearIsometryEquiv.ofSurjective (mulUnitLi u hu) (fun z => ⟨u⁻¹ * z, by
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    show u * (u⁻¹ * z) = z
    rw [mul_inv_cancel_left₀ hu0]⟩)

/-- Rotating the plane by a unit complex number preserves volume. -/
theorem mulUnit_measurePreserving (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving ((mulUnitLie u hu).toHomeomorph.toMeasurableEquiv : ℂ → ℂ) :=
  LinearIsometryEquiv.measurePreserving _

/-- The plane integral of any function equals its rotated integral. -/
theorem integral_conjRotation (u : ℂ) (hu : ‖u‖ = 1) (g : ℂ → ℂ) :
    ∫ z, g z ∂volume = ∫ z, g (u * z) ∂volume := by
  have h := (mulUnit_measurePreserving u hu).integral_comp' g
  have e : (fun z => g ((mulUnitLie u hu).toHomeomorph.toMeasurableEquiv z)) = fun z => g (u * z) := by
    funext z
    congr 1
  rw [e] at h
  exact h.symm

/-- The actual plane density is invariant under rotation by a unit complex number. -/
theorem loGaussianDensity_conjRotation (u : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    loGaussianDensity (u * z) = loGaussianDensity z := by
  unfold loGaussianDensity
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, hu, one_pow, one_mul]

/-- The cast of the actual complex Gaussian density is nonnegative. -/
theorem density_cast_nonneg (z : ℂ) : 0 ≤ (loGaussianDensity z : ℂ) := by
  exact_mod_cast (ComplexShift.nonneg z)

/-- The zeroth moment of the actual complex Gaussian density is one. -/
theorem moment_00 : (∫ z : ℂ, (loGaussianDensity z : ℂ) ∂volume) = 1 := by
  change (∫ z : ℂ, (ComplexShift.density z : ℂ) ∂volume) = 1
  rw [integral_complex_ofReal, ComplexShift.mass]
  norm_num

/-- The balanced first moment of the actual complex Gaussian is `1!`. -/
theorem moment_11 : (∫ z : ℂ, z * conj z * (loGaussianDensity z : ℂ) ∂volume) = 1 := by
  have h := ComplexMixed.balanced 1
  have e : (fun z => z * conj z * (loGaussianDensity z : ℂ)) =
      fun z => conj (z ^ 1) * z ^ 1 * (ComplexShift.density z : ℂ) := by
    funext z
    simp only [pow_one]
    unfold loGaussianDensity ComplexShift.density
    ring
  rw [e]
  simpa using h

/-- The balanced second moment of the actual complex Gaussian is `2!`. -/
theorem moment_22 : (∫ z : ℂ, z ^ 2 * conj z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 2 := by
  have h := ComplexMixed.balanced 2
  have e : (fun z => z ^ 2 * conj z ^ 2 * (loGaussianDensity z : ℂ)) =
      fun z => conj (z ^ 2) * z ^ 2 * (ComplexShift.density z : ℂ) := by
    funext z
    simp only [map_pow]
    unfold loGaussianDensity ComplexShift.density
    ring
  rw [e, h]
  norm_num

/-- The plane density kills the first unbalanced monomial moment by rotation. -/
theorem moment_10 : (∫ z : ℂ, z * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  have h := integral_conjRotation Complex.I (by simp) (g := fun z => z * (loGaussianDensity z : ℂ))
  have hg : (fun z => Complex.I * z * (loGaussianDensity (Complex.I * z) : ℂ)) =
      fun z => Complex.I * (z * (loGaussianDensity z : ℂ)) := by
    funext z
    rw [loGaussianDensity_conjRotation Complex.I (by simp) z, mul_assoc]
  rw [hg, integral_const_mul] at h
  have h1 : (1 - Complex.I) * (∫ z : ℂ, z * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
    linear_combination h
  have hu : (1 : ℂ) - Complex.I ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [Complex.I_re] at hre
  exact (mul_eq_zero.mp h1).resolve_left hu

/-- The plane density kills the second unbalanced monomial moment by rotation. -/
theorem moment_20 : (∫ z : ℂ, z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  have h := integral_conjRotation Complex.I (by simp)
    (g := fun z => z ^ 2 * (loGaussianDensity z : ℂ))
  have hg : (fun z => (Complex.I * z) ^ 2 * (loGaussianDensity (Complex.I * z) : ℂ)) =
      fun z => -(z ^ 2 * (loGaussianDensity z : ℂ)) := by
    funext z
    rw [loGaussianDensity_conjRotation Complex.I (by simp) z, mul_pow, Complex.I_sq]
    ring
  rw [hg, integral_neg] at h
  have h2 : (∫ z : ℂ, z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) +
      (∫ z : ℂ, z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
    linear_combination h
  have h3 : (2 : ℂ) * (∫ z : ℂ, z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
    linear_combination h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- The plane density kills the unbalanced `(2, 1)` monomial moment by rotation. -/
theorem moment_21 : (∫ z : ℂ, z ^ 2 * conj z * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  have h := integral_conjRotation Complex.I (by simp)
    (g := fun z => z ^ 2 * conj z * (loGaussianDensity z : ℂ))
  have hg : (fun z => (Complex.I * z) ^ 2 * conj (Complex.I * z) * (loGaussianDensity (Complex.I * z) : ℂ)) =
      fun z => Complex.I * (z ^ 2 * conj z * (loGaussianDensity z : ℂ)) := by
    funext z
    rw [loGaussianDensity_conjRotation Complex.I (by simp) z, mul_pow, Complex.I_sq, map_mul,
      Complex.conj_I]
    ring
  rw [hg, integral_const_mul] at h
  have h1 : (1 - Complex.I) * (∫ z : ℂ, z ^ 2 * conj z * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
    linear_combination h
  have hu : (1 : ℂ) - Complex.I ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [Complex.I_re] at hre
  exact (mul_eq_zero.mp h1).resolve_left hu

/-- The conjugate unbalanced moment `(0, 1)` vanishes as well. -/
theorem moment_01 : (∫ z : ℂ, conj z * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  have e : (fun z => conj z * (loGaussianDensity z : ℂ)) =
      fun z => conj (z * (loGaussianDensity z : ℂ)) := by
    funext z
    rw [map_mul, Complex.conj_ofReal]
  rw [e, integral_conj, moment_10, map_zero]

/-- The conjugate unbalanced moment `(0, 2)` vanishes as well. -/
theorem moment_02 : (∫ z : ℂ, conj z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  have e : (fun z => conj z ^ 2 * (loGaussianDensity z : ℂ)) =
      fun z => conj (z ^ 2 * (loGaussianDensity z : ℂ)) := by
    funext z
    rw [map_mul, map_pow, Complex.conj_ofReal]
  rw [e, integral_conj, moment_20, map_zero]

/-- The conjugate unbalanced moment `(1, 2)` vanishes as well. -/
theorem moment_12 : (∫ z : ℂ, z * conj z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  have e : (fun z => z * conj z ^ 2 * (loGaussianDensity z : ℂ)) =
      fun z => conj (z ^ 2 * conj z * (loGaussianDensity z : ℂ)) := by
    funext z
    rw [map_mul, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [e, integral_conj, moment_21, map_zero]

/-! ## An integrable dominating product for the fourth moment -/

/-- `‖z‖^8` times the actual plane density is integrable (pulled back to the real plane). -/
theorem integrable_norm_pow_eight_mul_density : Integrable
    (fun z : ℂ => (((‖z‖ ^ 8 : ℝ) : ℂ)) * (loGaussianDensity z : ℂ)) := by
  have hpp := Complex.volume_preserving_equiv_real_prod
  have key : (fun z : ℂ => (((‖z‖ ^ 8 : ℝ) : ℂ)) * (loGaussianDensity z : ℂ)) =
      (fun p : ℝ × ℝ => (((p.1 ^ 2 + p.2 ^ 2) ^ 4 *
        (Real.pi⁻¹ * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))) : ℝ) : ℂ)) ∘
        (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ) := by
    funext z
    simp only [Function.comp_def, Complex.measurableEquivRealProd_apply]
    have hnR : ‖z‖ ^ 8 = (z.re ^ 2 + z.im ^ 2) ^ 4 := by
      rw [show ‖z‖ ^ 8 = (‖z‖ ^ 2) ^ 4 by ring, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      ring
    rw [hnR]
    unfold loGaussianDensity
    rw [Complex.normSq_apply]
    push_cast
    rw [← Complex.exp_add, ← pow_two, ← pow_two]
    ring
  rw [key]
  have h1 : Integrable (fun x : ℝ => x ^ (((4 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h2 : Integrable (fun x : ℝ => x ^ (((2 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h3 : Integrable (fun x : ℝ => x ^ (((0 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h4 : Integrable (fun x : ℝ => x ^ (((6 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h5 : Integrable (fun x : ℝ => x ^ (((8 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have hg : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 + p.2 ^ 2) ^ 4 *
      (Real.pi⁻¹ * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))) : ℝ)) := by
    have hg1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 8 * Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) :=
      (h5.mul_prod h3).congr (Filter.EventuallyEq.of_eq (by funext p; simp only [Real.rpow_natCast]; ring))
    have hg2 : Integrable
        (fun p : ℝ × ℝ => p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 2 * Real.exp (-p.2 ^ 2)) :=
      (h4.mul_prod h2).congr (Filter.EventuallyEq.of_eq (by funext p; simp only [Real.rpow_natCast]; ring))
    have hg3 : Integrable
        (fun p : ℝ × ℝ => p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 4 * Real.exp (-p.2 ^ 2)) :=
      (h1.mul_prod h1).congr (Filter.EventuallyEq.of_eq (by funext p; simp only [Real.rpow_natCast]; ring))
    have hg4 : Integrable
        (fun p : ℝ × ℝ => p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 * Real.exp (-p.2 ^ 2)) :=
      (h2.mul_prod h4).congr (Filter.EventuallyEq.of_eq (by funext p; simp only [Real.rpow_natCast]; ring))
    have hg5 : Integrable (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * p.2 ^ 8 * Real.exp (-p.2 ^ 2)) :=
      (h3.mul_prod h5).congr (Filter.EventuallyEq.of_eq (by funext p; simp only [Real.rpow_natCast]; ring))
    have hsum0 : Integrable (fun p : ℝ × ℝ => Real.pi⁻¹ * (p.1 ^ 8 * Real.exp (-p.1 ^ 2) *
          Real.exp (-p.2 ^ 2)) + Real.pi⁻¹ * (p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 2 *
          Real.exp (-p.2 ^ 2)) * 4 + Real.pi⁻¹ * (p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 4 *
          Real.exp (-p.2 ^ 2)) * 6 + Real.pi⁻¹ * (p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 *
          Real.exp (-p.2 ^ 2)) * 4 + Real.pi⁻¹ * (Real.exp (-p.1 ^ 2) * p.2 ^ 8 *
          Real.exp (-p.2 ^ 2))) := by
      refine ((((hg1.const_mul (Real.pi⁻¹ : ℝ)).add ((hg2.const_mul (4 : ℝ)).const_mul
        (Real.pi⁻¹ : ℝ))).add (((hg3.const_mul (6 : ℝ)).const_mul (Real.pi⁻¹ : ℝ)))).add
        (((hg4.const_mul (4 : ℝ)).const_mul (Real.pi⁻¹ : ℝ)).add
        (hg5.const_mul (Real.pi⁻¹ : ℝ)))).congr ?_
      exact Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring)
    have hsum : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 + p.2 ^ 2) ^ 4 *
        (Real.pi⁻¹ * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))) : ℝ)) :=
      hsum0.congr (Filter.EventuallyEq.of_eq (by funext p; ring))
    exact hsum
  exact (MeasurePreserving.integrable_comp_emb hpp
    Complex.measurableEquivRealProd.measurableEmbedding).mpr
    (Complex.ofRealCLM.integrable_comp hg)

/-- The plane density is integrable as a real function with unit integral. -/
theorem integrable_density_real : Integrable (fun z : ℂ => loGaussianDensity z) := by
  refine Integrable.of_integral_ne_zero ?_
  change (∫ z : ℂ, ComplexShift.density z) ≠ 0
  rw [ComplexShift.mass]
  norm_num

/-- The plane density itself is integrable on the actual complex plane. -/
theorem integrable_density : Integrable (fun z : ℂ => (loGaussianDensity z : ℂ)) := by
  exact Complex.ofRealCLM.integrable_comp integrable_density_real

/-- `‖z‖^16` times the actual plane density is integrable (pulled back to the real plane). -/
theorem integrable_norm_pow_sixteen_mul_density : Integrable
    (fun z : ℂ => (((‖z‖ ^ 16 : ℝ) : ℂ)) * (loGaussianDensity z : ℂ)) := by
  have hpp := Complex.volume_preserving_equiv_real_prod
  have key : (fun z : ℂ => (((‖z‖ ^ 16 : ℝ) : ℂ)) * (loGaussianDensity z : ℂ)) =
      (fun p : ℝ × ℝ => (((p.1 ^ 2 + p.2 ^ 2) ^ 8 *
        (Real.pi⁻¹ * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))) : ℝ) : ℂ)) ∘
        (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ) := by
    funext z
    simp only [Function.comp_def, Complex.measurableEquivRealProd_apply]
    have hnR : ‖z‖ ^ 16 = (z.re ^ 2 + z.im ^ 2) ^ 8 := by
      rw [show ‖z‖ ^ 16 = (‖z‖ ^ 2) ^ 8 by ring, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      ring
    rw [hnR]
    unfold loGaussianDensity
    rw [Complex.normSq_apply]
    push_cast
    rw [← Complex.exp_add, ← pow_two, ← pow_two]
    ring
  rw [key]
  have h0 : Integrable (fun x : ℝ => x ^ (((0 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h2 : Integrable (fun x : ℝ => x ^ (((2 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h4 : Integrable (fun x : ℝ => x ^ (((4 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h6 : Integrable (fun x : ℝ => x ^ (((6 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h8 : Integrable (fun x : ℝ => x ^ (((8 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h10 : Integrable (fun x : ℝ => x ^ (((10 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h12 : Integrable (fun x : ℝ => x ^ (((12 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h14 : Integrable (fun x : ℝ => x ^ (((14 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have h16 : Integrable (fun x : ℝ => x ^ (((16 : ℕ)) : ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num)
  have hg1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 16 * Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) :=
    (h16.mul_prod h0).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg2 : Integrable
      (fun p : ℝ × ℝ => p.1 ^ 14 * Real.exp (-p.1 ^ 2) * p.2 ^ 2 * Real.exp (-p.2 ^ 2)) :=
    (h14.mul_prod h2).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg3 : Integrable
      (fun p : ℝ × ℝ => p.1 ^ 12 * Real.exp (-p.1 ^ 2) * p.2 ^ 4 * Real.exp (-p.2 ^ 2)) :=
    (h12.mul_prod h4).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg4 : Integrable
      (fun p : ℝ × ℝ => p.1 ^ 10 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 * Real.exp (-p.2 ^ 2)) :=
    (h10.mul_prod h6).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg5 : Integrable
      (fun p : ℝ × ℝ => p.1 ^ 8 * Real.exp (-p.1 ^ 2) * p.2 ^ 8 * Real.exp (-p.2 ^ 2)) :=
    (h8.mul_prod h8).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg6 : Integrable
      (fun p : ℝ × ℝ => p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 * Real.exp (-p.2 ^ 2)) :=
    (h6.mul_prod h10).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg7 : Integrable
      (fun p : ℝ × ℝ => p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2)) :=
    (h4.mul_prod h12).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg8 : Integrable
      (fun p : ℝ × ℝ => p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2)) :=
    (h2.mul_prod h14).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hg9 : Integrable (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
    (h0.mul_prod h16).congr (Filter.EventuallyEq.of_eq
      (by funext p; simp only [Real.rpow_natCast]; ring))
  have hsum0 : Integrable (fun p : ℝ × ℝ => Real.pi⁻¹ * ((p.1 ^ 16 * Real.exp (-p.1 ^ 2) *
        Real.exp (-p.2 ^ 2)) + (p.1 ^ 14 * Real.exp (-p.1 ^ 2) * p.2 ^ 2 *
        Real.exp (-p.2 ^ 2)) * 8 + (p.1 ^ 12 * Real.exp (-p.1 ^ 2) * p.2 ^ 4 *
        Real.exp (-p.2 ^ 2)) * 28 + (p.1 ^ 10 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 *
        Real.exp (-p.2 ^ 2)) * 56 + (p.1 ^ 8 * Real.exp (-p.1 ^ 2) * p.2 ^ 8 *
        Real.exp (-p.2 ^ 2)) * 70 + (p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 *
        Real.exp (-p.2 ^ 2)) * 56 + (p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 *
        Real.exp (-p.2 ^ 2)) * 28 + (p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 *
        Real.exp (-p.2 ^ 2)) * 8 + (Real.exp (-p.1 ^ 2) * p.2 ^ 16 *
        Real.exp (-p.2 ^ 2)))) := by
    have r1 : Integrable (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * p.2 ^ 16 *
        Real.exp (-p.2 ^ 2)) := hg9
    have r2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      ((hg8.const_mul (8 : ℝ)).add r1).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    have r3 : Integrable (fun p : ℝ × ℝ => p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      ((hg7.const_mul (28 : ℝ)).add r2).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    have r4 : Integrable (fun p : ℝ × ℝ => p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      ((hg6.const_mul (56 : ℝ)).add r3).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    have r5 : Integrable (fun p : ℝ × ℝ => p.1 ^ 8 * Real.exp (-p.1 ^ 2) * p.2 ^ 8 * Real.exp (-p.2 ^ 2) * 70 + p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      ((hg5.const_mul (70 : ℝ)).add r4).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    have r6 : Integrable (fun p : ℝ × ℝ => p.1 ^ 10 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 8 * Real.exp (-p.1 ^ 2) * p.2 ^ 8 * Real.exp (-p.2 ^ 2) * 70 + p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      ((hg4.const_mul (56 : ℝ)).add r5).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    have r7 : Integrable (fun p : ℝ × ℝ => p.1 ^ 12 * Real.exp (-p.1 ^ 2) * p.2 ^ 4 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 10 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 8 * Real.exp (-p.1 ^ 2) * p.2 ^ 8 * Real.exp (-p.2 ^ 2) * 70 + p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      ((hg3.const_mul (28 : ℝ)).add r6).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    have r8 : Integrable (fun p : ℝ × ℝ => p.1 ^ 14 * Real.exp (-p.1 ^ 2) * p.2 ^ 2 * Real.exp (-p.2 ^ 2) * 8 + p.1 ^ 12 * Real.exp (-p.1 ^ 2) * p.2 ^ 4 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 10 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 8 * Real.exp (-p.1 ^ 2) * p.2 ^ 8 * Real.exp (-p.2 ^ 2) * 70 + p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      ((hg2.const_mul (8 : ℝ)).add r7).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    have r9 : Integrable (fun p : ℝ × ℝ => p.1 ^ 16 * Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) + p.1 ^ 14 * Real.exp (-p.1 ^ 2) * p.2 ^ 2 * Real.exp (-p.2 ^ 2) * 8 + p.1 ^ 12 * Real.exp (-p.1 ^ 2) * p.2 ^ 4 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 10 * Real.exp (-p.1 ^ 2) * p.2 ^ 6 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 8 * Real.exp (-p.1 ^ 2) * p.2 ^ 8 * Real.exp (-p.2 ^ 2) * 70 + p.1 ^ 6 * Real.exp (-p.1 ^ 2) * p.2 ^ 10 * Real.exp (-p.2 ^ 2) * 56 + p.1 ^ 4 * Real.exp (-p.1 ^ 2) * p.2 ^ 12 * Real.exp (-p.2 ^ 2) * 28 + p.1 ^ 2 * Real.exp (-p.1 ^ 2) * p.2 ^ 14 * Real.exp (-p.2 ^ 2) * 8 + Real.exp (-p.1 ^ 2) * p.2 ^ 16 * Real.exp (-p.2 ^ 2)) :=
      (hg1.add r8).congr
        (Filter.EventuallyEq.of_eq (by funext p; simp only [Pi.add_apply]; ring))
    exact (r9.const_mul (Real.pi⁻¹ : ℝ)).congr (Filter.EventuallyEq.of_eq (by funext p; ring))
  have hsum : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 + p.2 ^ 2) ^ 8 *
      (Real.pi⁻¹ * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))) : ℝ)) :=
    hsum0.congr (Filter.EventuallyEq.of_eq (by funext p; ring))
  exact (MeasurePreserving.integrable_comp_emb hpp
    Complex.measurableEquivRealProd.measurableEmbedding).mpr
    (Complex.ofRealCLM.integrable_comp hsum)

/-- The squared eighth-degree dominating entry factor is integrable. -/
theorem integrable_gDom :
    Integrable (fun z : ℂ => (((1 + ‖z‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity z : ℂ)) := by
  have e : (fun z : ℂ => (((1 + ‖z‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity z : ℂ)) =
      (fun z => (loGaussianDensity z : ℂ)) +
        (fun z => (2 : ℂ) * (((‖z‖ ^ 8 : ℝ) : ℂ) * (loGaussianDensity z : ℂ))) +
        (fun z => ((‖z‖ ^ 16 : ℝ) : ℂ) * (loGaussianDensity z : ℂ)) := by
    funext z
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e]
  exact (integrable_density.add
    (integrable_norm_pow_eight_mul_density.const_mul (2 : ℂ))).add
    integrable_norm_pow_sixteen_mul_density

/-- The product dominating factor over the actual four matrix entries is integrable. -/
theorem dom_integrable :
    Integrable (fun X : Fin 2 → Fin 2 → ℂ =>
      ∏ i : Fin 2, ∏ j : Fin 2,
        (((1 + ‖X i j‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity (X i j) : ℂ)) := by
  have hrow : ∀ y : Fin 2 → ℂ, Integrable
      (fun z : ℂ => (((1 + ‖z‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity z : ℂ)) := fun y =>
    integrable_gDom
  have hrow2 : ∀ i : Fin 2, Integrable (fun y : Fin 2 → ℂ =>
      ∏ j : Fin 2, (((1 + ‖y j‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity (y j) : ℂ)) :=
    fun i => Integrable.fintype_prod fun j => hrow i
  have hX : Integrable (fun X : Fin 2 → Fin 2 → ℂ =>
      ∏ i : Fin 2, (fun y : Fin 2 → ℂ =>
        ∏ j : Fin 2, (((1 + ‖y j‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity (y j) : ℂ)) (X i)) :=
    Integrable.fintype_prod hrow2
  exact hX.congr (Filter.EventuallyEq.of_eq (by funext X; rfl))

/-! ## Row factorization and the two-by-two fourth permanent moment -/

/-- The actual product Gaussian density of a `2 × 2` matrix splits into row factors. -/
theorem densCast (X : Fin 2 → Fin 2 → ℂ) :
    (loGaussianMatDensity 2 X : ℂ) =
      (∏ j : Fin 2, (loGaussianDensity (X 0 j) : ℂ)) *
        (∏ j : Fin 2, (loGaussianDensity (X 1 j) : ℂ)) := by
  unfold loGaussianMatDensity
  push_cast
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]

/-- The actual row product density of a `Fin 2 → ℂ` row. -/
noncomputable def rowDens (y : Fin 2 → ℂ) : ℂ := ∏ j : Fin 2, (loGaussianDensity (y j) : ℂ)

/-- The actual product Gaussian density of a `2 × 2` matrix in row-density form. -/
theorem densCast' (X : Fin 2 → Fin 2 → ℂ) :
    (loGaussianMatDensity 2 X : ℂ) = rowDens (X 0) * rowDens (X 1) :=
  densCast X

/-- The outer Fubini step: a two-row product integral factorizes. -/
theorem matrix_eval (F0 F1 : (Fin 2 → ℂ) → ℂ) (v0 v1 : ℂ)
    (h0 : ∫ y : Fin 2 → ℂ, F0 y * rowDens y = v0)
    (h1 : ∫ y : Fin 2 → ℂ, F1 y * rowDens y = v1) :
    ∫ X : Fin 2 → Fin 2 → ℂ, (F0 (X 0) * rowDens (X 0)) * (F1 (X 1) * rowDens (X 1)) =
      v0 * v1 := by
  have e : (fun X : Fin 2 → Fin 2 → ℂ =>
      (F0 (X 0) * rowDens (X 0)) * (F1 (X 1) * rowDens (X 1))) =
      fun X => ∏ i : Fin 2, ![fun y : Fin 2 → ℂ => F0 y * rowDens y,
        fun y : Fin 2 → ℂ => F1 y * rowDens y] i (X i) := by
    funext X
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val]
  rw [e, integral_fintype_prod_volume_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val, h0, h1]

/-- The inner Fubini step: a two-entry row integral factorizes into entry moments. -/
theorem row_eval (α0 β0 α1 β1 : ℕ) (m0 m1 : ℂ)
    (h0 : ∫ z : ℂ, z ^ α0 * conj z ^ β0 * (loGaussianDensity z : ℂ) = m0)
    (h1 : ∫ z : ℂ, z ^ α1 * conj z ^ β1 * (loGaussianDensity z : ℂ) = m1) :
    ∫ y : Fin 2 → ℂ, ((y 0) ^ α0 * conj (y 0) ^ β0) * ((y 1) ^ α1 * conj (y 1) ^ β1) *
        rowDens y = m0 * m1 := by
  have e : (fun y : Fin 2 → ℂ => ((y 0) ^ α0 * conj (y 0) ^ β0) * ((y 1) ^ α1 * conj (y 1) ^ β1) *
        rowDens y) =
      fun y => ∏ j : Fin 2, ![fun z : ℂ => z ^ α0 * conj z ^ β0 * (loGaussianDensity z : ℂ),
        fun z : ℂ => z ^ α1 * conj z ^ β1 * (loGaussianDensity z : ℂ)] j (y j) := by
    funext y
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val, rowDens, Fin.prod_univ_two]
    ring
  rw [e, integral_fintype_prod_volume_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val, h0, h1]

/-! ## The actual two-by-two permanent and its fourth moment -/

/-- The four row factors in the expansion of `Per X * conj (Per X)`. -/
def pairMono (x y : ℂ) (u : Fin 4) : ℂ :=
  if (u : ℕ) = 0 then x * conj x
  else if (u : ℕ) = 1 then x * conj y
  else if (u : ℕ) = 2 then y * conj x
  else y * conj y

/-- Every real eighth power is nonnegative. -/
theorem pow8_nonneg (b : ℝ) : 0 ≤ b ^ 8 := by
  have h := sq_nonneg (b ^ 4)
  rwa [show (b ^ 4) ^ 2 = b ^ 8 by ring] at h

/-- The sixteenth-power norm bound used for the dominating product. -/
theorem norm_le_one_add_pow8 (t : ℝ) (ht : 0 ≤ t) : t ≤ 1 + t ^ 8 := by
  by_cases h : t ≤ 1
  · nlinarith [pow_nonneg ht 8]
  · calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ 1 + t ^ 8 := le_add_of_nonneg_left zero_le_one

/-- The squared norm is bounded by one plus the eighth power. -/
theorem sq_le_one_add_pow8 (t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ 1 + t ^ 8 := by
  by_cases h : t ≤ 1
  · have h2 := pow_le_one₀ ht h (n := 2)
    nlinarith [h2, pow_nonneg ht 8]
  · calc t ^ 2 ≤ t ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ 1 + t ^ 8 := le_add_of_nonneg_left zero_le_one


/-- Every actual pair monomial is dominated by the single-eighth-power product. -/
theorem norm_pairMono_le (x y : ℂ) (u : Fin 4) :
    ‖pairMono x y u‖ ≤ (1 + ‖x‖ ^ 8) * (1 + ‖y‖ ^ 8) := by
  have key_mul : ∀ a b : ℝ, 0 ≤ b → a ≤ 1 + a ^ 8 → b ≤ 1 + b ^ 8 →
      a * b ≤ (1 + a ^ 8) * (1 + b ^ 8) := fun a b hb0 ha hb =>
    mul_le_mul ha hb (by linarith) (add_nonneg zero_le_one (pow8_nonneg a))
  fin_cases u <;> simp [pairMono, ↓reduceIte]
  · rw [← pow_two]
    calc ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 8 := sq_le_one_add_pow8 ‖x‖ (norm_nonneg _)
      _ ≤ (1 + ‖x‖ ^ 8) * (1 + ‖y‖ ^ 8) :=
        le_mul_of_one_le_right (add_nonneg zero_le_one (pow8_nonneg ‖x‖))
          (le_add_of_nonneg_right (pow8_nonneg ‖y‖))
  · exact key_mul ‖x‖ ‖y‖ (norm_nonneg _) (norm_le_one_add_pow8 ‖x‖ (norm_nonneg _))
      (norm_le_one_add_pow8 ‖y‖ (norm_nonneg _))
  · calc ‖y‖ * ‖x‖ = ‖x‖ * ‖y‖ := mul_comm _ _
      _ ≤ (1 + ‖x‖ ^ 8) * (1 + ‖y‖ ^ 8) :=
        key_mul ‖x‖ ‖y‖ (norm_nonneg _) (norm_le_one_add_pow8 ‖x‖ (norm_nonneg _))
          (norm_le_one_add_pow8 ‖y‖ (norm_nonneg _))
  · rw [← pow_two]
    calc ‖y‖ ^ 2 ≤ 1 + ‖y‖ ^ 8 := sq_le_one_add_pow8 ‖y‖ (norm_nonneg _)
      _ ≤ (1 + ‖x‖ ^ 8) * (1 + ‖y‖ ^ 8) := by
        rw [mul_comm]
        exact le_mul_of_one_le_right (add_nonneg zero_le_one (pow8_nonneg ‖y‖))
          (le_add_of_nonneg_right (pow8_nonneg ‖x‖))

/-- The integrand terms of the actual fourth permanent moment. -/
def termFun (u v : Fin 4) (X : Fin 2 → Fin 2 → ℂ) : ℂ :=
  (pairMono (X 0 0) (X 0 1) u * pairMono (X 1 1) (X 1 0) u) *
    (pairMono (X 0 0) (X 0 1) v * pairMono (X 1 1) (X 1 0) v) *
    (loGaussianMatDensity 2 X : ℂ)

/-- The norm of each actual fourth-moment term is dominated by the product bound. -/
theorem term_norm_le (u v : Fin 4) (X : Fin 2 → Fin 2 → ℂ) :
    ‖termFun u v X‖ ≤
      ‖∏ i : Fin 2, ∏ j : Fin 2,
        (((1 + ‖X i j‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity (X i j) : ℂ)‖ := by
  have hpu := norm_pairMono_le (X 0 0) (X 0 1) u
  have hqu := norm_pairMono_le (X 1 1) (X 1 0) u
  have hpv := norm_pairMono_le (X 0 0) (X 0 1) v
  have hqv := norm_pairMono_le (X 1 1) (X 1 0) v
  have hd : ‖(loGaussianMatDensity 2 X : ℂ)‖ =
      ∏ i : Fin 2, ∏ j : Fin 2, loGaussianDensity (X i j) := by
    rw [show (loGaussianMatDensity 2 X : ℂ) =
        (((∏ i : Fin 2, ∏ j : Fin 2, loGaussianDensity (X i j) : ℝ) : ℂ)) by
      rw [show loGaussianMatDensity 2 X =
        ∏ i : Fin 2, ∏ j : Fin 2, loGaussianDensity (X i j) from rfl]]
    rw [Complex.norm_real]
    exact abs_of_nonneg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
      show (0:ℝ) ≤ ComplexShift.density (X i j)
      exact ComplexShift.nonneg _)
  have hg : ‖∏ i : Fin 2, ∏ j : Fin 2,
        (((1 + ‖X i j‖ ^ 8) ^ 2 : ℝ) : ℂ) * (loGaussianDensity (X i j) : ℂ)‖ =
      (∏ i : Fin 2, ∏ j : Fin 2, ((1 + ‖X i j‖ ^ 8) ^ 2 : ℝ) * loGaussianDensity (X i j)) := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ) ≤ (1 + ‖X i j‖ ^ 8) ^ 2 by positivity),
      abs_of_nonneg (show (0:ℝ) ≤ loGaussianDensity (X i j) by
        show (0:ℝ) ≤ ComplexShift.density (X i j)
        exact ComplexShift.nonneg _)]
  rw [termFun, norm_mul, norm_mul, norm_mul, norm_mul, ← mul_assoc, hd, hg]
  have step1 : (((‖pairMono (X 0 0) (X 0 1) u‖ * ‖pairMono (X 1 1) (X 1 0) u‖) *
        ‖pairMono (X 0 0) (X 0 1) v‖) * ‖pairMono (X 1 1) (X 1 0) v‖) *
        (∏ i : Fin 2, ∏ j : Fin 2, loGaussianDensity (X i j)) ≤
      ((((1 + ‖X 0 0‖ ^ 8) * (1 + ‖X 0 1‖ ^ 8)) *
        ((1 + ‖X 1 1‖ ^ 8) * (1 + ‖X 1 0‖ ^ 8))) *
        ((1 + ‖X 0 0‖ ^ 8) * (1 + ‖X 0 1‖ ^ 8))) *
        ((1 + ‖X 1 1‖ ^ 8) * (1 + ‖X 1 0‖ ^ 8)) *
        (∏ i : Fin 2, ∏ j : Fin 2, loGaussianDensity (X i j)) := by
    refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul hpu hqu (by positivity)
      (by positivity)) hpv (by positivity) (by positivity)) hqv (by positivity)
      (by positivity)) (le_refl _) ?_ ?_
    · exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
        ComplexShift.nonneg _
    · positivity
  have eD : (∏ i : Fin 2, ∏ j : Fin 2, loGaussianDensity (X i j)) =
      (loGaussianDensity (X 0 0) * loGaussianDensity (X 0 1)) *
        (loGaussianDensity (X 1 0) * loGaussianDensity (X 1 1)) := by
    rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  have eG : (∏ i : Fin 2, ∏ j : Fin 2,
        ((1 + ‖X i j‖ ^ 8) ^ 2 : ℝ) * loGaussianDensity (X i j)) =
      ((((1 + ‖X 0 0‖ ^ 8) ^ 2 : ℝ) * loGaussianDensity (X 0 0)) *
          (((1 + ‖X 0 1‖ ^ 8) ^ 2 : ℝ) * loGaussianDensity (X 0 1))) *
        ((((1 + ‖X 1 0‖ ^ 8) ^ 2 : ℝ) * loGaussianDensity (X 1 0)) *
          (((1 + ‖X 1 1‖ ^ 8) ^ 2 : ℝ) * loGaussianDensity (X 1 1))) := by
    rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  have my_eq : ((((1 + ‖X 0 0‖ ^ 8) * (1 + ‖X 0 1‖ ^ 8)) *
        ((1 + ‖X 1 1‖ ^ 8) * (1 + ‖X 1 0‖ ^ 8))) *
        ((1 + ‖X 0 0‖ ^ 8) * (1 + ‖X 0 1‖ ^ 8))) *
      ((1 + ‖X 1 1‖ ^ 8) * (1 + ‖X 1 0‖ ^ 8)) *
      (∏ i : Fin 2, ∏ j : Fin 2, loGaussianDensity (X i j)) =
      (∏ i : Fin 2, ∏ j : Fin 2,
        ((1 + ‖X i j‖ ^ 8) ^ 2 : ℝ) * loGaussianDensity (X i j)) := by
    rw [eD, eG]
    generalize hb00 : loGaussianDensity (X 0 0) = b00
    generalize hb01 : loGaussianDensity (X 0 1) = b01
    generalize hb10 : loGaussianDensity (X 1 0) = b10
    generalize hb11 : loGaussianDensity (X 1 1) = b11
    generalize ha00 : ((1 + ‖X 0 0‖ ^ 8) : ℝ) = a00
    generalize ha01 : ((1 + ‖X 0 1‖ ^ 8) : ℝ) = a01
    generalize ha10 : ((1 + ‖X 1 0‖ ^ 8) : ℝ) = a10
    generalize ha11 : ((1 + ‖X 1 1‖ ^ 8) : ℝ) = a11
    ring
  exact le_trans step1 (le_of_eq my_eq)

/-- The actual single-entry Gaussian density is continuous. -/
theorem continuous_loGaussianDensity : Continuous loGaussianDensity := by
  have h1 : Continuous (fun z : ℂ => Complex.normSq z) := by
    have hr : Continuous (fun z : ℂ => z.re) := Complex.continuous_re
    have hi : Continuous (fun z : ℂ => z.im) := Complex.continuous_im
    refine ((hr.pow 2).add (hi.pow 2)).congr
      (by intro z; rw [Pi.add_apply, Pi.pow_apply, Pi.pow_apply, Complex.normSq_apply]; ring)
  unfold loGaussianDensity
  exact (Real.continuous_exp.comp h1.neg).const_mul (Real.pi⁻¹ : ℝ)

/-- The actual two-by-two product Gaussian density is continuous. -/
theorem continuous_loGaussianMatDensity_two :
    Continuous (fun X : Fin 2 → Fin 2 → ℂ => loGaussianMatDensity 2 X) := by
  unfold loGaussianMatDensity
  exact continuous_finsetProd _ fun i _ =>
    continuous_finsetProd _ fun j _ =>
      continuous_loGaussianDensity.comp ((continuous_apply j).comp (continuous_apply i))

/-- The actual left-mode pair monomial is continuous in the matrix entries. -/
theorem continuous_pairMono_left (u : Fin 4) :
    Continuous (fun X : Fin 2 → Fin 2 → ℂ => pairMono (X 0 0) (X 0 1) u) := by
  have c00 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 0 0) :=
    (continuous_apply (0 : Fin 2)).comp (continuous_apply (0 : Fin 2))
  have c01 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 0 1) :=
    (continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2))
  have cc0 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => conj (X 0 0)) :=
    Complex.continuous_conj.comp c00
  have cc1 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => conj (X 0 1)) :=
    Complex.continuous_conj.comp c01
  fin_cases u
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 0 0 * conj (X 0 0)) :=
      (c00.mul cc0).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 0 0 * conj (X 0 1)) :=
      (c00.mul cc1).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 0 1 * conj (X 0 0)) :=
      (c01.mul cc0).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 0 1 * conj (X 0 1)) :=
      (c01.mul cc1).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h

/-- The actual right-mode pair monomial is continuous in the matrix entries. -/
theorem continuous_pairMono_right (u : Fin 4) :
    Continuous (fun X : Fin 2 → Fin 2 → ℂ => pairMono (X 1 1) (X 1 0) u) := by
  have c11 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 1 1) :=
    (continuous_apply (1 : Fin 2)).comp (continuous_apply (1 : Fin 2))
  have c10 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 1 0) :=
    (continuous_apply (0 : Fin 2)).comp (continuous_apply (1 : Fin 2))
  have cc1 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => conj (X 1 1)) :=
    Complex.continuous_conj.comp c11
  have cc0 : Continuous (fun X : Fin 2 → Fin 2 → ℂ => conj (X 1 0)) :=
    Complex.continuous_conj.comp c10
  fin_cases u
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 1 1 * conj (X 1 1)) :=
      (c11.mul cc1).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 1 1 * conj (X 1 0)) :=
      (c11.mul cc0).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 1 0 * conj (X 1 1)) :=
      (c10.mul cc1).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h
  · have h : Continuous (fun X : Fin 2 → Fin 2 → ℂ => X 1 0 * conj (X 1 0)) :=
      (c10.mul cc0).congr (by intro X; rfl)
    simpa [pairMono, ↓reduceIte] using h

/-- The actual fourth-moment term is continuous in the matrix entries. -/
theorem term_continuous (u v : Fin 4) : Continuous (termFun u v) := by
  show Continuous (fun X : Fin 2 → Fin 2 → ℂ =>
    (pairMono (X 0 0) (X 0 1) u * pairMono (X 1 1) (X 1 0) u) *
      (pairMono (X 0 0) (X 0 1) v * pairMono (X 1 1) (X 1 0) v) *
      (loGaussianMatDensity 2 X : ℂ))
  exact ((((continuous_pairMono_left u).mul (continuous_pairMono_right u)).mul
    ((continuous_pairMono_left v).mul (continuous_pairMono_right v)))).mul
    (Complex.ofRealCLM.continuous.comp continuous_loGaussianMatDensity_two)

/-- Every actual fourth-moment term is integrable. -/
theorem term_integrable (u v : Fin 4) : Integrable (termFun u v) := by
  refine dom_integrable.mono (term_continuous u v).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun X => term_norm_le u v X

/-- The explicit permanent of the actual `2 × 2` Ginibre matrix model. -/
theorem permanent_fin_two (X : Fin 2 → Fin 2 → ℂ) :
    Matrix.permanent (Matrix.of X) = X 0 0 * X 1 1 + X 0 1 * X 1 0 := by
  rw [Matrix.permanent, sum_perm_fin_two]
  simp [Matrix.of_apply, Fin.prod_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- The squared absolute value of the `2 × 2` permanent is a sum over the four
pairs of permutations. -/
theorem per_conj_eq_sum (X : Fin 2 → Fin 2 → ℂ) :
    Matrix.permanent (Matrix.of X) * conj (Matrix.permanent (Matrix.of X)) =
      ∑ u : Fin 4, pairMono (X 0 0) (X 0 1) u * pairMono (X 1 1) (X 1 0) u := by
  rw [permanent_fin_two, map_add]
  rw [Fin.sum_univ_four]
  simp [pairMono]
  ring

/-- The actual balanced zeroth Gaussian moment in exponent form is one. -/
theorem moment_00' : (∫ z : ℂ, z ^ 0 * conj z ^ 0 * (loGaussianDensity z : ℂ) ∂volume) = 1 := by
  simp only [pow_zero, one_mul]
  exact moment_00

/-- The actual balanced first Gaussian moment in exponent form is one. -/
theorem moment_11' : (∫ z : ℂ, z ^ 1 * conj z ^ 1 * (loGaussianDensity z : ℂ) ∂volume) = 1 := by
  simp only [pow_one]
  exact moment_11

/-- The actual unbalanced `(1, 0)` Gaussian moment vanishes by rotation. -/
theorem moment_10' : (∫ z : ℂ, z ^ 1 * conj z ^ 0 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  simp only [pow_one, pow_zero, mul_one]
  exact moment_10

/-- The actual unbalanced `(0, 1)` Gaussian moment vanishes by conjugation. -/
theorem moment_01' : (∫ z : ℂ, z ^ 0 * conj z ^ 1 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  simp only [pow_one, pow_zero, one_mul]
  exact moment_01

/-- The actual unbalanced `(2, 0)` Gaussian moment vanishes by rotation. -/
theorem moment_20' : (∫ z : ℂ, z ^ 2 * conj z ^ 0 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  simp only [pow_zero, mul_one]
  exact moment_20

/-- The actual unbalanced `(0, 2)` Gaussian moment vanishes by conjugation. -/
theorem moment_02' : (∫ z : ℂ, z ^ 0 * conj z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  simp only [pow_zero, one_mul]
  exact moment_02

/-- The actual unbalanced `(2, 1)` Gaussian moment vanishes by rotation. -/
theorem moment_21' : (∫ z : ℂ, z ^ 2 * conj z ^ 1 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  simp only [pow_one]
  exact moment_21

/-- The actual unbalanced `(1, 2)` Gaussian moment vanishes by conjugation. -/
theorem moment_12' : (∫ z : ℂ, z ^ 1 * conj z ^ 2 * (loGaussianDensity z : ℂ) ∂volume) = 0 := by
  simp only [pow_one]
  exact moment_12

/-- The exact values of the sixteen actual fourth-moment term integrals. -/
theorem term_integral (u v : Fin 4) :
    (∫ X : Fin 2 → Fin 2 → ℂ, termFun u v X) =
      ![![(4:ℂ), 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 4]] u v := by
  fin_cases u <;> fin_cases v
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 2 * ((y 1) ^ 0 * conj (y 1) ^ 0)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 0 * ((y 1) ^ 2 * conj (y 1) ^ 2)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 2 2 0 0 2 1 moment_22 moment_00')
      (row_eval 0 0 2 2 1 2 moment_00' moment_22)]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 1 * ((y 1) ^ 0 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 1 * ((y 1) ^ 2 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 2 1 0 1 0 0 moment_21' moment_01')
      (row_eval 0 1 2 1 0 0 moment_01' moment_21')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 2 * ((y 1) ^ 1 * conj (y 1) ^ 0)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 0 * ((y 1) ^ 1 * conj (y 1) ^ 2)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 2 1 0 0 0 moment_12' moment_10')
      (row_eval 1 0 1 2 0 0 moment_10' moment_12')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 1 1 1 1 1 moment_11' moment_11')
      (row_eval 1 1 1 1 1 1 moment_11' moment_11')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 1 * ((y 1) ^ 0 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 1 * ((y 1) ^ 2 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 2 1 0 1 0 0 moment_21' moment_01')
      (row_eval 0 1 2 1 0 0 moment_01' moment_21')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 0 * ((y 1) ^ 0 * conj (y 1) ^ 2)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 2 * ((y 1) ^ 2 * conj (y 1) ^ 0)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 2 0 0 2 0 0 moment_20' moment_02')
      (row_eval 0 2 2 0 0 0 moment_02' moment_20')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 1 1 1 1 1 moment_11' moment_11')
      (row_eval 1 1 1 1 1 1 moment_11' moment_11')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 0 * ((y 1) ^ 1 * conj (y 1) ^ 2)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 2 * ((y 1) ^ 1 * conj (y 1) ^ 0)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 0 1 2 0 0 moment_10' moment_12')
      (row_eval 1 2 1 0 0 0 moment_12' moment_10')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 2 * ((y 1) ^ 1 * conj (y 1) ^ 0)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 0 * ((y 1) ^ 1 * conj (y 1) ^ 2)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 2 1 0 0 0 moment_12' moment_10')
      (row_eval 1 0 1 2 0 0 moment_10' moment_12')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 1 1 1 1 1 moment_11' moment_11')
      (row_eval 1 1 1 1 1 1 moment_11' moment_11')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 2 * ((y 1) ^ 2 * conj (y 1) ^ 0)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 0 * ((y 1) ^ 0 * conj (y 1) ^ 2)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 0 2 2 0 0 0 moment_02' moment_20')
      (row_eval 2 0 0 2 0 0 moment_20' moment_02')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 1 * ((y 1) ^ 2 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 1 * ((y 1) ^ 0 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 0 1 2 1 0 0 moment_01' moment_21')
      (row_eval 2 1 0 1 0 0 moment_21' moment_01')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 1 * ((y 1) ^ 1 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 1 1 1 1 1 moment_11' moment_11')
      (row_eval 1 1 1 1 1 1 moment_11' moment_11')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 0 * ((y 1) ^ 1 * conj (y 1) ^ 2)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 1 * conj (y 0) ^ 2 * ((y 1) ^ 1 * conj (y 1) ^ 0)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 1 0 1 2 0 0 moment_10' moment_12')
      (row_eval 1 2 1 0 0 0 moment_12' moment_10')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 1 * ((y 1) ^ 2 * conj (y 1) ^ 1)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 1 * ((y 1) ^ 0 * conj (y 1) ^ 1)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, ↓reduceIte, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 0 1 2 1 0 0 moment_01' moment_21')
      (row_eval 2 1 0 1 0 0 moment_21' moment_01')]
    norm_num [Matrix.cons_val]
  · rw [show (fun X : Fin 2 → Fin 2 → ℂ => termFun _ _ X) = (fun X =>
        ((fun y : Fin 2 → ℂ => (y 0) ^ 0 * conj (y 0) ^ 0 * ((y 1) ^ 2 * conj (y 1) ^ 2)) (X 0) * rowDens (X 0)) *
          ((fun y : Fin 2 → ℂ => (y 0) ^ 2 * conj (y 0) ^ 2 * ((y 1) ^ 0 * conj (y 1) ^ 0)) (X 1) * rowDens (X 1))) from by
      funext X
      simp only [termFun, pairMono, densCast']
      simp only [rowDens, Fin.prod_univ_two]
      push_cast
      ring]
    rw [matrix_eval _ _ _ _ (row_eval 0 0 2 2 1 2 moment_00' moment_22)
      (row_eval 2 2 0 0 2 1 moment_22 moment_00')]
    norm_num [Matrix.cons_val]

/-- Lemma 56 at `n = 1`: the actual second moment of the normalized permanent
random variable equals `1 + 1 = 2`. -/
theorem permSqMoment_one : permSqMoment 1 = 2 := by
  simpa only [permSqMoment, one_add_one_eq_two] using
    Qatlib.Papers.LinearOptics10.StockmeyerSrc.MomentModel.oneFourth

/-- Lemma 56 at `n = 2`: the actual second moment of the normalized permanent
random variable equals `2 + 1 = 3`. -/
theorem permSqMoment_two : permSqMoment 2 = 3 := by
  have key : (∫ X : Fin 2 → Fin 2 → ℂ,
      ((Matrix.permanent (Matrix.of X) * conj (Matrix.permanent (Matrix.of X)) /
        ((Nat.factorial 2 : ℕ) : ℂ)) ^ 2) * (loGaussianMatDensity 2 X : ℂ) ∂volume) = 3 := by
    have hexp : (fun X : Fin 2 → Fin 2 → ℂ =>
        ((Matrix.permanent (Matrix.of X) * conj (Matrix.permanent (Matrix.of X)) /
          ((Nat.factorial 2 : ℕ) : ℂ)) ^ 2) * (loGaussianMatDensity 2 X : ℂ)) =
        fun X => (1 / 4) * ∑ p : Fin 4 × Fin 4, termFun p.1 p.2 X := by
      funext X
      have h1 := per_conj_eq_sum X
      rw [h1, div_pow, sq, Fintype.sum_mul_sum, ← Fintype.sum_prod_type',
        show ((Nat.factorial 2 : ℕ) : ℂ) ^ 2 = 4 by norm_num, div_mul_eq_mul_div,
        Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [show termFun p.1 p.2 X = (pairMono (X 0 0) (X 0 1) p.1 * pairMono (X 1 1) (X 1 0) p.1) *
          (pairMono (X 0 0) (X 0 1) p.2 * pairMono (X 1 1) (X 1 0) p.2) *
          (loGaussianMatDensity 2 X : ℂ) from rfl]
      ring
    rw [hexp, integral_const_mul, integral_finsetSum _ (fun p _ => term_integrable p.1 p.2)]
    have hsum : (∑ p : Fin 4 × Fin 4, (∫ X : Fin 2 → Fin 2 → ℂ, termFun p.1 p.2 X)) = 12 := by
      have e1 : (∑ p : Fin 4 × Fin 4, (∫ X : Fin 2 → Fin 2 → ℂ, termFun p.1 p.2 X)) =
          ∑ p : Fin 4 × Fin 4,
            ![![(4:ℂ), 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 4]] p.1 p.2 :=
        Finset.sum_congr rfl fun p _ => term_integral p.1 p.2
      rw [e1, Fintype.sum_prod_type']
      simp only [Fin.sum_univ_four, Matrix.cons_val]
      norm_num
    rw [hsum]
    norm_num
  apply Complex.ofReal_injective
  rw [permSqMoment, ← integral_complex_ofReal, show ((3 : ℝ) : ℂ) = 3 by norm_num, ← key]
  congr 1 with x
  rw [show ((permMomentVar x ^ 2 * loGaussianMatDensity 2 x : ℝ) : ℂ) =
      (permMomentVar x : ℂ) ^ 2 * (loGaussianMatDensity 2 x : ℂ) from by push_cast; ring]
  rw [show ((permMomentVar x : ℝ) : ℂ) =
      (Matrix.of x).permanent * conj (Matrix.of x).permanent / ((Nat.factorial 2 : ℕ) : ℂ) from by
    rw [permMomentVar]
    push_cast
    rw [← Complex.mul_conj]]

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.PermanentSecondMoment
