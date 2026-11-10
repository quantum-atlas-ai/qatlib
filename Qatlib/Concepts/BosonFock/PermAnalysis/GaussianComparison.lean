/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open MeasureTheory ProbabilityTheory Complex
open scoped InnerProductSpace MeasureTheory ENNReal ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def gaussianBilinearCF {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a b : F) : ℂ :=
  ∫ x : E, ∫ y : E,
    Complex.exp ((I : ℂ) * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ)))
      ∂(stdGaussian E) ∂(stdGaussian E)

def laplaceLE (μ ν : Measure ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∫ x, Real.exp (-s * x) ∂μ ≥ ∫ x, Real.exp (-s * x) ∂ν

def matrixLaplaceLE (μ ν : Measure E) : Prop :=
  ∀ Q : E →L[ℝ] E, (∀ x : E, 0 ≤ ⟪x, Q x⟫_ℝ) →
    ∫ y, Real.exp (-⟪y, Q y⟫_ℝ) ∂μ ≥ ∫ x, Real.exp (-⟪x, Q x⟫_ℝ) ∂ν

private theorem integral_cexp_gaussianReal_quadratic (μ h : ℝ) (hμ : 0 ≤ μ) :
    ∫ r, cexp (((-(μ * r ^ 2 / 2) : ℝ) : ℂ) + I * (((h * r) : ℝ) : ℂ)) ∂(gaussianReal 0 1)
      = (((1 + μ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((-(h ^ 2 / (2 * (1 + μ))) : ℝ) : ℂ)) := by
  have h1μ : (0:ℝ) < 1 + μ := by linarith
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have key : ∀ r : ℝ,
      gaussianPDFReal 0 1 r • cexp (((-(μ * r ^ 2 / 2) : ℝ) : ℂ) + I * (((h * r) : ℝ) : ℂ))
        = ((√(2 * Real.pi))⁻¹ : ℝ) * cexp (((-((1 + μ) * r ^ 2 / 2) : ℝ) : ℂ) + I * (((h * r) : ℝ) : ℂ)) := by
    intro r
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, smul_eq_mul, Algebra.smul_def,
      Complex.coe_algebraMap, Complex.ofReal_mul, sub_zero]
    rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [key, integral_const_mul]
  have e2 : ∀ r : ℝ, cexp (((-((1 + μ) * r ^ 2 / 2) : ℝ) : ℂ) + I * (((h * r) : ℝ) : ℂ))
      = cexp (((-(1 + μ) / 2 : ℝ) : ℂ) * ((r : ℝ) : ℂ) ^ 2 + (I * ((h : ℝ) : ℂ)) * ((r : ℝ) : ℂ) + 0) := by
    intro r
    congr 1
    push_cast
    ring
  rw [integral_congr_ae (ae_of_all _ e2)]
  rw [integral_cexp_quadratic (b := ((-(1 + μ) / 2 : ℝ) : ℂ)) (c := I * ((h : ℝ) : ℂ)) (d := 0)
    (by rw [Complex.ofReal_re]; linarith)]
  have h12 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by simp [Complex.ofReal_div]
  have hp : ((Real.pi : ℝ) : ℂ) / -((-(1 + μ) / 2 : ℝ) : ℂ) = ((Real.pi / ((1 + μ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_div]
    congr 1
    ring
  have hpow : (((Real.pi / ((1 + μ) / 2) : ℝ) : ℂ) ^ (1 / 2 : ℂ))
      = (((Real.pi / ((1 + μ) / 2)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← h12, Complex.ofReal_cpow (le_of_lt (by positivity))]
  have hexp : (0 - (I * ((h : ℝ) : ℂ)) ^ 2 / (4 * ((-(1 + μ) / 2 : ℝ) : ℂ)) : ℂ)
      = ((-(h ^ 2 / (2 * (1 + μ))) : ℝ) : ℂ) := by
    rw [Complex.ext_iff]
    simp only [Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im, Complex.neg_re,
      Complex.neg_im, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.I_mul_I,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, add_zero, sub_self, mul_one, one_mul,
      neg_zero, sub_zero, mul_neg, neg_mul, neg_neg, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat]
    constructor
    · field_simp
      ring
    · simp
  rw [hp, hpow, hexp, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, Complex.ofReal_inj]
  have hr : √(2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  rw [show Real.pi / ((1 + μ) / 2) = 2 * Real.pi / (1 + μ) by
      rw [div_eq_div_iff (ne_of_gt (by positivity)) h1μ.ne']
      ring,
    Real.div_rpow (by positivity) h1μ.le, ← Real.sqrt_eq_rpow, mul_div_assoc',
    inv_mul_cancel₀ hr, one_div, ← Real.rpow_neg h1μ.le]

private theorem gaussAdjointSymm (R : E →L[ℝ] E) :
    ((ContinuousLinearMap.id ℝ E + R.adjoint ∘L R).toLinearMap).IsSymmetric := by
  intro x y
  show ⟪x + R.adjoint (R x), y⟫_ℝ = ⟪x, y + R.adjoint (R y)⟫_ℝ
  rw [inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

private theorem gaussian_anisotropic_integral (R : E →L[ℝ] E) (h : E) :
    ∫ y, cexp (((-(‖R y‖ ^ 2 / 2) : ℝ) : ℂ) + I * ((⟪h, y⟫_ℝ : ℝ) : ℂ)) ∂(stdGaussian E)
      = ((∏ i : Fin (Module.finrank ℝ E),
          (gaussAdjointSymm R).eigenvalues rfl i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * cexp (((-(∑ i : Fin (Module.finrank ℝ E),
            (⟪(gaussAdjointSymm R).eigenvectorBasis rfl i, h⟫_ℝ) ^ 2
              / (2 * (gaussAdjointSymm R).eigenvalues rfl i)) : ℝ) : ℂ)) := by
  classical
  set n := Module.finrank ℝ E with hn
  set S : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + R.adjoint ∘L R with hS
  set e := (gaussAdjointSymm R).eigenvectorBasis rfl with he
  set ev := (gaussAdjointSymm R).eigenvalues rfl with hev
  have hon : ∀ i j : Fin n, ⟪e i, e j⟫_ℝ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have heig : ∀ i : Fin n, S (e i) = ↑(ev i) • e i := fun i ↦
    (gaussAdjointSymm R).apply_eigenvectorBasis rfl i
  have hpos : ∀ i : Fin n, 1 ≤ ev i := by
    intro i
    have h2 : ⟪e i, S (e i)⟫_ℝ = ev i := by
      rw [heig, real_inner_smul_right, hon i i, if_pos rfl, mul_one]
    have h3 : ⟪e i, S (e i)⟫_ℝ = 1 + ⟪R (e i), R (e i)⟫_ℝ := by
      show ⟪e i, e i + R.adjoint (R (e i))⟫_ℝ = _
      rw [inner_add_right, hon i i, if_pos rfl, ContinuousLinearMap.adjoint_inner_right]
    have h4 : 0 ≤ ⟪R (e i), R (e i)⟫_ℝ := real_inner_self_nonneg
    have h5 : ev i = 1 + ⟪R (e i), R (e i)⟫_ℝ := by rw [← h2, h3]
    rw [h5]
    linarith
  have hRReig : ∀ i : Fin n, R.adjoint (R (e i)) = ↑(ev i - 1) • e i := by
    intro i
    have h1 : R.adjoint (R (e i)) = S (e i) - e i := by
      show R.adjoint (R (e i)) = (e i + R.adjoint (R (e i))) - e i
      abel
    rw [h1, heig, sub_smul, one_smul]

  have hq : ∀ w : Fin n → ℝ,
      ‖R (∑ i, w i • e i)‖ ^ 2 = ∑ i, (ev i - 1) * (w i) ^ 2 := by
    intro w
    rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right]
    rw [map_sum, map_sum]
    simp only [map_smul, hRReig, smul_smul]
    rw [sum_inner]
    simp_rw [real_inner_smul_left]
    have hZ : ∀ i : Fin n, ⟪e i, ∑ x, (w x * (ev x - 1)) • e x⟫_ℝ = w i * (ev i - 1) :=
      fun i ↦ e.orthonormal.inner_right_fintype (fun x ↦ w x * (ev x - 1)) i
    simp_rw [hZ]
    apply Finset.sum_congr rfl
    intro i _
    ring

  have hl : ∀ w : Fin n → ℝ, ⟪h, ∑ i, w i • e i⟫_ℝ = ∑ i, w i * ⟪h, e i⟫_ℝ := by
    intro w
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_right]

  rw [stdGaussian_eq_map_pi_orthonormalBasis e, integral_map]
  · have hf : ∀ w : Fin n → ℝ,
        cexp (((-(‖R (∑ i, w i • e i)‖ ^ 2 / 2) : ℝ) : ℂ)
            + I * ((⟪h, ∑ i, w i • e i⟫_ℝ : ℝ) : ℂ))
          = ∏ i, cexp (((-((ev i - 1) * (w i) ^ 2 / 2) : ℝ) : ℂ)
            + I * ((⟪h, e i⟫_ℝ * w i : ℝ) : ℂ)) := by
      intro w
      have h1 : (((-((∑ i, (ev i - 1) * (w i) ^ 2) / 2)) : ℝ) : ℂ)
          = ∑ i, (((-((ev i - 1) * (w i) ^ 2 / 2) : ℝ) : ℂ)) := by
        have h : ((-((∑ i, (ev i - 1) * (w i) ^ 2) / 2)) : ℝ)
            = ∑ i, -((ev i - 1) * (w i) ^ 2 / 2) := by
          calc ((-((∑ i, (ev i - 1) * (w i) ^ 2) / 2)) : ℝ)
              = ((-(∑ i, (ev i - 1) * (w i) ^ 2)) / 2 : ℝ) := by rw [← neg_div]
            _ = ((∑ i, -((ev i - 1) * (w i) ^ 2)) / 2 : ℝ) := by rw [Finset.sum_neg_distrib]
            _ = ∑ i, -((ev i - 1) * (w i) ^ 2 / 2) := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro i _
                ring
        rw [h, Complex.ofReal_sum]
      have h2 : ((∑ i, w i * ⟪h, e i⟫_ℝ : ℝ) : ℂ)
          = ∑ i, ((⟪h, e i⟫_ℝ * w i : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        ring
      rw [hq, hl, h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib, ← Complex.exp_sum]
    rw [integral_congr_ae (ae_of_all _ hf)]
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin n ↦ gaussianReal 0 1)
      (f := fun i r ↦ cexp (((-((ev i - 1) * r ^ 2 / 2) : ℝ) : ℂ)
        + I * ((⟪h, e i⟫_ℝ * r : ℝ) : ℂ)))]
    rw [Complex.ofReal_prod]
    have hsum : ((-(∑ i : Fin n, (⟪e i, h⟫_ℝ) ^ 2 / (2 * ev i))) : ℝ)
        = ∑ i : Fin n, -((⟪e i, h⟫_ℝ) ^ 2 / (2 * ev i)) := by
      rw [← Finset.sum_neg_distrib]
    rw [hsum, Complex.ofReal_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [integral_cexp_gaussianReal_quadratic (ev i - 1) (⟪h, e i⟫_ℝ) (by linarith [hpos i])]
    congr 1
    · rw [show (1 + (ev i - 1)) = ev i from by ring]
    · congr 1
      rw [Complex.ofReal_inj, real_inner_comm, show (1 + (ev i - 1)) = ev i from by ring]
  · exact (Continuous.aemeasurable (by fun_prop))
  · exact (Continuous.aestronglyMeasurable (by fun_prop))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem gaussianBilinearCF_a_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a : F) :
    gaussianBilinearCF T L a 0
      = ∫ y, cexp (((-(‖T y‖ ^ 2 / 2) : ℝ) : ℂ) + I * ((⟪L a, y⟫_ℝ : ℝ) : ℂ)) ∂(stdGaussian E) := by
  unfold gaussianBilinearCF
  rw [integral_integral_swap]
  · apply integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    have e1 : ∀ x : E,
        cexp (I * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L (0 : F)⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ)))
          = cexp (I * ((⟪x, T y⟫_ℝ : ℂ))) * cexp (I * ((⟪y, L a⟫_ℝ : ℂ))) := by
      intro x
      rw [map_zero L, inner_zero_right, Complex.ofReal_zero, add_zero, mul_add, Complex.exp_add]
    rw [integral_congr_ae (ae_of_all _ e1), integral_mul_const]
    have e2 : ∫ x, cexp (I * ((⟪x, T y⟫_ℝ : ℂ))) ∂(stdGaussian E)
        = cexp (((-(‖T y‖ ^ 2 / 2) : ℝ) : ℂ)) := by
      have h : ∫ x, cexp (I * ((⟪x, T y⟫_ℝ : ℂ))) ∂(stdGaussian E)
          = charFun (stdGaussian E) (T y) := by
        rw [charFun_apply]
        exact integral_congr_ae (ae_of_all _ fun x ↦ by
          show cexp (I * ((⟪x, T y⟫_ℝ : ℝ) : ℂ)) = cexp (((⟪x, T y⟫_ℝ : ℝ) : ℂ) * I)
          rw [mul_comm])
      rw [h, charFun_stdGaussian]
      congr 1
      push_cast
      ring
    rw [e2, ← Complex.exp_add]
    congr 1
    rw [real_inner_comm]
  · have hI : Integrable (fun _ : E × E ↦ (1 : ℝ)) ((stdGaussian E).prod (stdGaussian E)) :=
      integrable_const 1
    refine hI.mono' ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact ae_of_all _ fun p ↦ by
        show ‖cexp (I * ((⟪p.1, T p.2⟫_ℝ : ℂ) + (⟪p.1, L (0 : F)⟫_ℝ : ℂ)
            + (⟪p.2, L a⟫_ℝ : ℂ)))‖ ≤ 1
        rw [Complex.norm_exp]
        have hre : (I * ((⟪p.1, T p.2⟫_ℝ : ℂ) + (⟪p.1, L (0 : F)⟫_ℝ : ℂ)
            + (⟪p.2, L a⟫_ℝ : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im]
        rw [hre, Real.exp_zero]

private theorem gaussEigenvalue_ge_one (R : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    1 ≤ (gaussAdjointSymm R).eigenvalues rfl i := by
  set S : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + R.adjoint ∘L R with hS
  set e := (gaussAdjointSymm R).eigenvectorBasis rfl with he
  set ev := (gaussAdjointSymm R).eigenvalues rfl with hev
  have hon : ∀ j k : Fin (Module.finrank ℝ E), ⟪e j, e k⟫_ℝ = if j = k then 1 else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have heig : ∀ j : Fin (Module.finrank ℝ E), S (e j) = ↑(ev j) • e j := fun j ↦
    (gaussAdjointSymm R).apply_eigenvectorBasis rfl j
  have h2 : ⟪e i, S (e i)⟫_ℝ = ev i := by
    rw [heig, real_inner_smul_right, hon i i, if_pos rfl, mul_one]
  have h3 : ⟪e i, S (e i)⟫_ℝ = 1 + ⟪R (e i), R (e i)⟫_ℝ := by
    show ⟪e i, e i + R.adjoint (R (e i))⟫_ℝ = _
    rw [inner_add_right, hon i i, if_pos rfl, ContinuousLinearMap.adjoint_inner_right]
  have h4 : 0 ≤ ⟪R (e i), R (e i)⟫_ℝ := real_inner_self_nonneg
  rw [← h2, h3]
  linarith

private theorem gaussianBilinearCF_b_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] E) (L : F →L[ℝ] E) (b : F) :
    gaussianBilinearCF T L 0 b
      = ∫ x, cexp (((-(‖T.adjoint x‖ ^ 2 / 2) : ℝ) : ℂ) + I * ((⟪L b, x⟫_ℝ : ℝ) : ℂ))
        ∂(stdGaussian E) := by
  unfold gaussianBilinearCF
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have e1 : ∀ y : E,
      cexp (I * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L (0 : F)⟫_ℝ : ℂ)))
        = cexp (I * ((⟪x, T y⟫_ℝ : ℂ))) * cexp (I * ((⟪x, L b⟫_ℝ : ℂ))) := by
    intro y
    rw [map_zero L, inner_zero_right, Complex.ofReal_zero, add_zero, mul_add, Complex.exp_add]
  rw [integral_congr_ae (ae_of_all _ e1), integral_mul_const]
  have e2 : ∫ y, cexp (I * ((⟪x, T y⟫_ℝ : ℂ))) ∂(stdGaussian E)
      = cexp (((-(‖T.adjoint x‖ ^ 2 / 2) : ℝ) : ℂ)) := by
    have h : ∫ y, cexp (I * ((⟪x, T y⟫_ℝ : ℂ))) ∂(stdGaussian E)
        = charFun (stdGaussian E) (T.adjoint x) := by
      rw [charFun_apply]
      apply integral_congr_ae (ae_of_all _ fun y ↦ by
        show cexp (I * ((⟪x, T y⟫_ℝ : ℝ) : ℂ)) = cexp (((⟪y, T.adjoint x⟫_ℝ : ℝ) : ℂ) * I)
        rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_right, mul_comm])
    rw [h, charFun_stdGaussian]
    congr 1
    push_cast
    ring
  rw [e2, ← Complex.exp_add]
  congr 1
  rw [real_inner_comm]

theorem gaussianCF_oneSidedQuadraticScaling (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a b : F) :
    0 < (gaussianBilinearCF T L a 0).re ∧
      0 < (gaussianBilinearCF T L 0 b).re ∧
        0 < (gaussianBilinearCF T L 0 0).re ∧
          ∀ t : ℝ, gaussianBilinearCF T L (t • a) 0 =
            gaussianBilinearCF T L 0 0 *
              (gaussianBilinearCF T L a 0 / gaussianBilinearCF T L 0 0) ^ ((t ^ 2 : ℝ) : ℂ) ∧
            ∀ t : ℝ, gaussianBilinearCF T L 0 (t • b) =
              gaussianBilinearCF T L 0 0 *
                (gaussianBilinearCF T L 0 b / gaussianBilinearCF T L 0 0) ^ ((t ^ 2 : ℝ) : ℂ) := by
  classical
  set n := Module.finrank ℝ E with hn
  set ebT := (gaussAdjointSymm T).eigenvectorBasis rfl with hebT
  set evT := (gaussAdjointSymm T).eigenvalues rfl with hevT
  set ebTs := (gaussAdjointSymm T.adjoint).eigenvectorBasis rfl with hebTs
  set evTs := (gaussAdjointSymm T.adjoint).eigenvalues rfl with hevTs
  have key_a : ∀ a' : F, gaussianBilinearCF T L a' 0
      = ((∏ i : Fin n, evT i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * cexp (((-(∑ i : Fin n, (⟪ebT i, L a'⟫_ℝ) ^ 2 / (2 * evT i))) : ℝ) : ℂ) :=
    fun a' ↦ by
      rw [gaussianBilinearCF_a_zero]
      exact gaussian_anisotropic_integral T (L a')
  have key_b : ∀ b' : F, gaussianBilinearCF T L 0 b'
      = ((∏ i : Fin n, evTs i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * cexp (((-(∑ i : Fin n, (⟪ebTs i, L b'⟫_ℝ) ^ 2 / (2 * evTs i))) : ℝ) : ℂ) :=
    fun b' ↦ by
      rw [gaussianBilinearCF_b_zero]
      exact gaussian_anisotropic_integral T.adjoint (L b')
  have hCr : ∀ R : E →L[ℝ] E, 0 < (∏ i : Fin n, (gaussAdjointSymm R).eigenvalues rfl i ^ (-(1 / 2 : ℝ)) : ℝ) := by
    intro R
    apply Finset.prod_pos
    intro i _
    apply Real.rpow_pos_of_pos
    have := gaussEigenvalue_ge_one R i
    linarith
  have hCc : ∀ R : E →L[ℝ] E, ((∏ i : Fin n, (gaussAdjointSymm R).eigenvalues rfl i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    fun R ↦ Complex.ofReal_ne_zero.mpr (ne_of_gt (hCr R))
  refine ⟨?_, ?_, ?_, fun t ↦ ⟨?_, fun t' ↦ ?_⟩⟩
  · rw [key_a a, Complex.mul_re, Complex.ofReal_re, ← Complex.ofReal_exp, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos (hCr T) (Real.exp_pos _)
  · rw [key_b b, Complex.mul_re, Complex.ofReal_re, ← Complex.ofReal_exp, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos (hCr T.adjoint) (Real.exp_pos _)
  · rw [key_a (0 : F), Complex.mul_re, Complex.ofReal_re, ← Complex.ofReal_exp, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos (hCr T) (Real.exp_pos _)
  · rw [key_a (t • a), key_a a, key_a (0 : F)]
    have hq : (∑ i : Fin n, (⟪ebT i, L (t • a)⟫_ℝ) ^ 2 / (2 * evT i))
        = t ^ 2 * (∑ i : Fin n, (⟪ebT i, L a⟫_ℝ) ^ 2 / (2 * evT i)) := by
      calc (∑ i : Fin n, (⟪ebT i, L (t • a)⟫_ℝ) ^ 2 / (2 * evT i))
          = ∑ i : Fin n, t ^ 2 * ((⟪ebT i, L a⟫_ℝ) ^ 2 / (2 * evT i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [map_smul, real_inner_smul_right]
            ring
        _ = t ^ 2 * (∑ i : Fin n, (⟪ebT i, L a⟫_ℝ) ^ 2 / (2 * evT i)) :=
          (Finset.mul_sum _ _ _).symm
    have h00 : ((∏ i : Fin n, evT i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * cexp (((-(∑ i : Fin n, (⟪ebT i, L (0 : F)⟫_ℝ) ^ 2 / (2 * evT i))) : ℝ) : ℂ)
        = ((∏ i : Fin n, evT i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [map_zero L]
      simp
    rw [hq, h00, mul_div_cancel_left₀ _ (hCc T)]
    have hexp : (cexp (((-(∑ i : Fin n, (⟪ebT i, L a⟫_ℝ) ^ 2 / (2 * evT i))) : ℝ) : ℂ))
        ^ ((t ^ 2 : ℝ) : ℂ)
        = cexp (((t ^ 2 * -(∑ i : Fin n, (⟪ebT i, L a⟫_ℝ) ^ 2 / (2 * evT i))) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, ← Complex.ofReal_cpow (le_of_lt (Real.exp_pos _)), ← Real.exp_mul,
        Complex.ofReal_exp]
      congr 1
      rw [Complex.ofReal_inj]
      ring
    rw [hexp]
    have harg : (-(t ^ 2 * (∑ i : Fin n, (⟪ebT i, L a⟫_ℝ) ^ 2 / (2 * evT i))) : ℝ)
        = (t ^ 2 * -(∑ i : Fin n, (⟪ebT i, L a⟫_ℝ) ^ 2 / (2 * evT i)) : ℝ) := by ring
    rw [harg]
  · rw [key_b (t' • b), key_b b, key_b (0 : F)]
    have hq : (∑ i : Fin n, (⟪ebTs i, L (t' • b)⟫_ℝ) ^ 2 / (2 * evTs i))
        = t' ^ 2 * (∑ i : Fin n, (⟪ebTs i, L b⟫_ℝ) ^ 2 / (2 * evTs i)) := by
      calc (∑ i : Fin n, (⟪ebTs i, L (t' • b)⟫_ℝ) ^ 2 / (2 * evTs i))
          = ∑ i : Fin n, t' ^ 2 * ((⟪ebTs i, L b⟫_ℝ) ^ 2 / (2 * evTs i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [map_smul, real_inner_smul_right]
            ring
        _ = t' ^ 2 * (∑ i : Fin n, (⟪ebTs i, L b⟫_ℝ) ^ 2 / (2 * evTs i)) :=
          (Finset.mul_sum _ _ _).symm
    have h00 : ((∏ i : Fin n, evTs i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * cexp (((-(∑ i : Fin n, (⟪ebTs i, L (0 : F)⟫_ℝ) ^ 2 / (2 * evTs i))) : ℝ) : ℂ)
        = ((∏ i : Fin n, evTs i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [map_zero L]
      simp
    rw [hq, h00, mul_div_cancel_left₀ _ (hCc T.adjoint)]
    have hexp : (cexp (((-(∑ i : Fin n, (⟪ebTs i, L b⟫_ℝ) ^ 2 / (2 * evTs i))) : ℝ) : ℂ))
        ^ ((t' ^ 2 : ℝ) : ℂ)
        = cexp (((t' ^ 2 * -(∑ i : Fin n, (⟪ebTs i, L b⟫_ℝ) ^ 2 / (2 * evTs i))) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, ← Complex.ofReal_cpow (le_of_lt (Real.exp_pos _)), ← Real.exp_mul,
        Complex.ofReal_exp]
      congr 1
      rw [Complex.ofReal_inj]
      ring
    rw [hexp]
    have harg : (-(t' ^ 2 * (∑ i : Fin n, (⟪ebTs i, L b⟫_ℝ) ^ 2 / (2 * evTs i))) : ℝ)
        = (t' ^ 2 * -(∑ i : Fin n, (⟪ebTs i, L b⟫_ℝ) ^ 2 / (2 * evTs i)) : ℝ) := by ring
    rw [harg]

private theorem stdGaussian_prod_lp :
    ((stdGaussian E).prod (stdGaussian E)).map
        (WithLp.toLp 2 : E × E → WithLp 2 (E × E)) = stdGaussian (WithLp 2 (E × E)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  rw [integral_map (WithLp.measurable_toLp (p := 2) (X := E × E)).aemeasurable]
  · simp_rw [charFun_apply]
    have h1 : ∀ p : E × E,
        cexp (((⟪WithLp.toLp 2 p, t⟫_ℝ : ℝ) : ℂ) * I)
          = cexp (((⟪p.1, ((WithLp.ofLp t).1 : E)⟫_ℝ : ℝ) : ℂ) * I)
            * cexp (((⟪p.2, ((WithLp.ofLp t).2 : E)⟫_ℝ : ℝ) : ℂ) * I) := by
      intro p
      rw [WithLp.prod_inner_apply, WithLp.ofLp_toLp, Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [integral_congr_ae (ae_of_all _ h1),
      integral_prod_mul (f := fun x : E ↦ cexp (((⟪x, ((WithLp.ofLp t).1 : E)⟫_ℝ : ℝ) : ℂ) * I))
      (g := fun y : E ↦ cexp (((⟪y, ((WithLp.ofLp t).2 : E)⟫_ℝ : ℝ) : ℂ) * I))]
    rw [← charFun_apply, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian]
    have hn : ‖t‖ ^ 2 = ‖(WithLp.ofLp t).1‖ ^ 2 + ‖(WithLp.ofLp t).2‖ ^ 2 := by
      rw [WithLp.prod_norm_eq_of_nat 2 (by norm_num : (2 : ℝ≥0∞) = (2 : ℕ)) t,
        show ((1 / ((2 : ℕ) : ℝ)) : ℝ) = 1 / 2 from by norm_num, ← Real.sqrt_eq_rpow,
        Real.sq_sqrt (by positivity)]
      rfl
    have hnc : ((↑‖t‖ : ℂ) ^ 2)
        = (↑‖(WithLp.ofLp t).1‖ : ℂ) ^ 2 + (↑‖(WithLp.ofLp t).2‖ : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
          hn]
    rw [← charFun_apply, charFun_stdGaussian, ← Complex.exp_add]
    congr 1
    rw [hnc]
    ring
  · exact (Continuous.aestronglyMeasurable (by fun_prop))

private noncomputable def rotLp : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E) where
  toFun := fun w ↦ WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • (w.fst + w.snd),
    (Real.sqrt 2)⁻¹ • (w.fst - w.snd))
  invFun := fun z ↦ WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • (z.fst + z.snd),
    (Real.sqrt 2)⁻¹ • (z.fst - z.snd))
  left_inv := by
    intro w
    have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
      have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      field_simp
      ring_nf
      norm_num
    have key : ∀ x y : E, (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (x + y)
        + (Real.sqrt 2)⁻¹ • (x - y)) = x := by
      intro x y
      rw [smul_add, smul_smul, smul_smul, hsq]
      have e1 : (x + y) + (x - y) = x + x := by abel
      rw [← smul_add, e1, ← two_smul ℝ, smul_smul]
      norm_num
    have key2 : ∀ x y : E, (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (x + y)
        - (Real.sqrt 2)⁻¹ • (x - y)) = y := by
      intro x y
      rw [smul_sub, smul_smul, smul_smul, hsq, ← smul_sub]
      have e1 : (x + y) - (x - y) = y + y := by abel
      rw [e1, ← two_smul ℝ, smul_smul]
      norm_num
    have h1 : ((Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (w.fst + w.snd)
          + (Real.sqrt 2)⁻¹ • (w.fst - w.snd)),
        (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (w.fst + w.snd)
          - (Real.sqrt 2)⁻¹ • (w.fst - w.snd))) = WithLp.ofLp w := by
      show ((Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (w.fst + w.snd)
          + (Real.sqrt 2)⁻¹ • (w.fst - w.snd)),
        (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (w.fst + w.snd)
          - (Real.sqrt 2)⁻¹ • (w.fst - w.snd))) = (w.fst, w.snd)
      rw [Prod.ext_iff]
      exact ⟨key w.fst w.snd, key2 w.fst w.snd⟩
    calc WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (w.fst + w.snd)
          + (Real.sqrt 2)⁻¹ • (w.fst - w.snd)),
        (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (w.fst + w.snd)
          - (Real.sqrt 2)⁻¹ • (w.fst - w.snd)))
        = WithLp.toLp 2 (WithLp.ofLp w) := congrArg _ h1
      _ = w := rfl
  right_inv := by
    intro z
    have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
      have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      field_simp
      ring_nf
      norm_num
    have key : ∀ x y : E, (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (x + y)
        + (Real.sqrt 2)⁻¹ • (x - y)) = x := by
      intro x y
      rw [smul_add, smul_smul, smul_smul, hsq]
      have e1 : (x + y) + (x - y) = x + x := by abel
      rw [← smul_add, e1, ← two_smul ℝ, smul_smul]
      norm_num
    have key2 : ∀ x y : E, (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (x + y)
        - (Real.sqrt 2)⁻¹ • (x - y)) = y := by
      intro x y
      rw [smul_sub, smul_smul, smul_smul, hsq, ← smul_sub]
      have e1 : (x + y) - (x - y) = y + y := by abel
      rw [e1, ← two_smul ℝ, smul_smul]
      norm_num
    have h1 : ((Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (z.fst + z.snd)
          + (Real.sqrt 2)⁻¹ • (z.fst - z.snd)),
        (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (z.fst + z.snd)
          - (Real.sqrt 2)⁻¹ • (z.fst - z.snd))) = WithLp.ofLp z := by
      show ((Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (z.fst + z.snd)
          + (Real.sqrt 2)⁻¹ • (z.fst - z.snd)),
        (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (z.fst + z.snd)
          - (Real.sqrt 2)⁻¹ • (z.fst - z.snd))) = (z.fst, z.snd)
      rw [Prod.ext_iff]
      exact ⟨key z.fst z.snd, key2 z.fst z.snd⟩
    calc WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (z.fst + z.snd)
          + (Real.sqrt 2)⁻¹ • (z.fst - z.snd)),
        (Real.sqrt 2)⁻¹ • ((Real.sqrt 2)⁻¹ • (z.fst + z.snd)
          - (Real.sqrt 2)⁻¹ • (z.fst - z.snd)))
        = WithLp.toLp 2 (WithLp.ofLp z) := congrArg _ h1
      _ = z := rfl
  map_add' := by
    intro w z
    have h1 : ((Real.sqrt 2)⁻¹ • ((w.fst + z.fst) + (w.snd + z.snd)),
        (Real.sqrt 2)⁻¹ • ((w.fst + z.fst) - (w.snd + z.snd)))
        = ((Real.sqrt 2)⁻¹ • (w.fst + w.snd) + (Real.sqrt 2)⁻¹ • (z.fst + z.snd),
          (Real.sqrt 2)⁻¹ • (w.fst - w.snd) + (Real.sqrt 2)⁻¹ • (z.fst - z.snd)) := by
      have hfst : (Real.sqrt 2)⁻¹ • ((w.fst + z.fst) + (w.snd + z.snd))
          = (Real.sqrt 2)⁻¹ • (w.fst + w.snd) + (Real.sqrt 2)⁻¹ • (z.fst + z.snd) := by
        rw [← smul_add]
        congr 1
        abel
      have hsnd : (Real.sqrt 2)⁻¹ • ((w.fst + z.fst) - (w.snd + z.snd))
          = (Real.sqrt 2)⁻¹ • (w.fst - w.snd) + (Real.sqrt 2)⁻¹ • (z.fst - z.snd) := by
        rw [← smul_add]
        congr 1
        abel
      exact Prod.ext hfst hsnd
    calc WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • ((w.fst + z.fst) + (w.snd + z.snd)),
        (Real.sqrt 2)⁻¹ • ((w.fst + z.fst) - (w.snd + z.snd)))
        = WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • (w.fst + w.snd) + (Real.sqrt 2)⁻¹ • (z.fst + z.snd),
            (Real.sqrt 2)⁻¹ • (w.fst - w.snd) + (Real.sqrt 2)⁻¹ • (z.fst - z.snd)) :=
          congrArg _ h1
      _ = WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • (w.fst + w.snd),
            (Real.sqrt 2)⁻¹ • (w.fst - w.snd))
          + WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • (z.fst + z.snd),
            (Real.sqrt 2)⁻¹ • (z.fst - z.snd)) := rfl
  map_smul' := by
    intro t w
    have h1 : ((Real.sqrt 2)⁻¹ • (t • w.fst + t • w.snd),
        (Real.sqrt 2)⁻¹ • (t • w.fst - t • w.snd))
        = (t • (Real.sqrt 2)⁻¹ • (w.fst + w.snd), t • (Real.sqrt 2)⁻¹ • (w.fst - w.snd)) := by
      have hfst : (Real.sqrt 2)⁻¹ • (t • w.fst + t • w.snd)
          = t • (Real.sqrt 2)⁻¹ • (w.fst + w.snd) := by
        rw [← smul_add, smul_smul, mul_comm, smul_smul]
      have hsnd : (Real.sqrt 2)⁻¹ • (t • w.fst - t • w.snd)
          = t • (Real.sqrt 2)⁻¹ • (w.fst - w.snd) := by
        rw [← smul_sub, smul_smul, mul_comm, smul_smul]
      exact Prod.ext hfst hsnd
    calc WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • (t • w.fst + t • w.snd),
        (Real.sqrt 2)⁻¹ • (t • w.fst - t • w.snd))
        = WithLp.toLp 2 (t • (Real.sqrt 2)⁻¹ • (w.fst + w.snd),
            t • (Real.sqrt 2)⁻¹ • (w.fst - w.snd)) := congrArg _ h1
      _ = t • WithLp.toLp 2 ((Real.sqrt 2)⁻¹ • (w.fst + w.snd),
            (Real.sqrt 2)⁻¹ • (w.fst - w.snd)) := rfl
  norm_map' := by
    intro w
    have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
      have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      field_simp
      ring_nf
      norm_num
    rw [WithLp.prod_norm_eq_of_nat 2 (by norm_num : (2 : ℝ≥0∞) = (2 : ℕ)) _,
      WithLp.prod_norm_eq_of_nat 2 (by norm_num : (2 : ℝ≥0∞) = (2 : ℕ)) _,
      show ((1 / ((2 : ℕ) : ℝ)) : ℝ) = 1 / 2 from by norm_num, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
    congr 1
    have hpar : ‖w.fst + w.snd‖ ^ 2 + ‖w.fst - w.snd‖ ^ 2 = 2 * (‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2) := by
      rw [parallelogram_law_with_norm ℝ]
    calc ‖(Real.sqrt 2)⁻¹ • (w.fst + w.snd)‖ ^ 2 + ‖(Real.sqrt 2)⁻¹ • (w.fst - w.snd)‖ ^ 2
        = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * (‖w.fst + w.snd‖ ^ 2 + ‖w.fst - w.snd‖ ^ 2) := by
          rw [norm_smul, norm_smul, mul_pow, mul_pow, ← mul_add,
            Real.norm_of_nonneg (by positivity), sq]
      _ = (1 / 2) * (‖w.fst + w.snd‖ ^ 2 + ‖w.fst - w.snd‖ ^ 2) := by rw [hsq]
      _ = ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2 := by rw [hpar]; ring

private theorem stdGaussian_prod_lp_rotate :
    ((stdGaussian (WithLp 2 (E × E))).prod (stdGaussian (WithLp 2 (E × E)))).map
      (Prod.map rotLp rotLp)
    = (stdGaussian (WithLp 2 (E × E))).prod (stdGaussian (WithLp 2 (E × E))) := by
  rw [← Measure.map_prod_map _ _ rotLp.continuous.measurable rotLp.continuous.measurable]
  have hr : (Measure.map (⇑(rotLp : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E)))
      (stdGaussian (WithLp 2 (E × E)))) = stdGaussian (WithLp 2 (E × E)) :=
    stdGaussian_map (rotLp : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E))
  rw [hr]

private theorem rotLp_exponent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] E) (L : F →L[ℝ] E) (u v : F) (r : (WithLp 2 (E × E)) × (WithLp 2 (E × E))) :
    ((⟪(r.1.fst : E), T (r.2.fst : E)⟫_ℝ : ℂ) + (⟪(r.1.fst : E), L v⟫_ℝ : ℂ)
        + (⟪(r.2.fst : E), L u⟫_ℝ : ℂ))
      - ((⟪(r.1.snd : E), T (r.2.snd : E)⟫_ℝ : ℂ) + (⟪(r.1.snd : E), L v⟫_ℝ : ℂ)
        + (⟪(r.2.snd : E), L u⟫_ℝ : ℂ))
    = ((⟪((rotLp r.1).fst : E), T ((rotLp r.2).snd : E)⟫_ℝ : ℂ)
        + (⟪((rotLp r.2).snd : E), L (Real.sqrt 2 • u)⟫_ℝ : ℂ))
      + ((⟪((rotLp r.1).snd : E), T ((rotLp r.2).fst : E)⟫_ℝ : ℂ)
        + (⟪((rotLp r.1).snd : E), L (Real.sqrt 2 • v)⟫_ℝ : ℂ)) := by
  have hrot1 : ∀ z : WithLp 2 (E × E), ((rotLp z).fst : E) = (Real.sqrt 2)⁻¹ • (z.fst + z.snd) :=
    fun z ↦ rfl
  have hrot2 : ∀ z : WithLp 2 (E × E), ((rotLp z).snd : E) = (Real.sqrt 2)⁻¹ • (z.fst - z.snd) :=
    fun z ↦ rfl
  have hc : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    have h2' : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
    ring_nf
    norm_num
  have hs2 : ((↑(Real.sqrt 2) : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [hrot1, hrot2, smul_eq_mul, map_add, map_sub, map_smul, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hc]
  push_cast
  ring_nf
  rw [hs2]
  ring

private theorem stdGaussian_prod_rotate_raw :
    ((stdGaussian E).prod (stdGaussian E)).map
        (fun p : E × E ↦ ((Real.sqrt 2)⁻¹ • (p.1 + p.2), (Real.sqrt 2)⁻¹ • (p.1 - p.2)))
    = (stdGaussian E).prod (stdGaussian E) := by
  have hcomp : (fun p : E × E ↦ ((Real.sqrt 2)⁻¹ • (p.1 + p.2), (Real.sqrt 2)⁻¹ • (p.1 - p.2)))
      = (fun z : WithLp 2 (E × E) ↦ WithLp.ofLp z) ∘ rotLp ∘
        (fun p : E × E ↦ WithLp.toLp 2 p) := by
    funext p
    show ((Real.sqrt 2)⁻¹ • (p.1 + p.2), (Real.sqrt 2)⁻¹ • (p.1 - p.2))
      = WithLp.ofLp (rotLp (WithLp.toLp 2 p))
    rw [show WithLp.ofLp (rotLp (WithLp.toLp 2 p))
        = ((Real.sqrt 2)⁻¹ • ((WithLp.toLp 2 p).fst + (WithLp.toLp 2 p).snd),
          (Real.sqrt 2)⁻¹ • ((WithLp.toLp 2 p).fst - (WithLp.toLp 2 p).snd)) from rfl]
    rfl
  rw [hcomp, ← Measure.map_map (WithLp.measurable_ofLp (p := 2) (X := E × E))
    (rotLp.continuous.measurable.comp (WithLp.measurable_toLp (p := 2) (X := E × E)))]
  rw [← Measure.map_map rotLp.continuous.measurable
    (WithLp.measurable_toLp (p := 2) (X := E × E))]
  rw [stdGaussian_prod_lp]
  have hr2 : (Measure.map (⇑(rotLp : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E)))
      (stdGaussian (WithLp 2 (E × E)))) = stdGaussian (WithLp 2 (E × E)) :=
    stdGaussian_map (rotLp : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E))
  rw [hr2]
  have hid : (fun z : WithLp 2 (E × E) ↦ WithLp.ofLp z) ∘
      (fun p : E × E ↦ WithLp.toLp 2 p) = id := by
    funext p
    rfl
  rw [← stdGaussian_prod_lp,
    Measure.map_map (WithLp.measurable_ofLp (p := 2) (X := E × E))
      (WithLp.measurable_toLp (p := 2) (X := E × E)), hid, Measure.map_id]

private theorem norm_sub_cexp_two_mul_le (s t : ℝ) :
    ‖cexp (((I : ℂ)) * ((s : ℂ))) - cexp (((I : ℂ)) * ((t : ℂ)))‖ ≤ 2 * |s - t| := by
  have h1 : cexp (((I : ℂ)) * ((s : ℂ)))
      = cexp (((I : ℂ)) * ((t : ℂ))) * cexp (((I : ℂ)) * (((s - t : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn1 : ‖cexp (((I : ℂ)) * ((t : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have h0 : (((I : ℂ)) * ((t : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [h0, Real.exp_zero]
  rw [h1, show cexp (((I : ℂ)) * ((t : ℝ) : ℂ)) * cexp (((I : ℂ)) * (((s - t : ℝ) : ℂ)))
      - cexp (((I : ℂ)) * ((t : ℝ) : ℂ))
      = cexp (((I : ℂ)) * ((t : ℝ) : ℂ))
        * (cexp (((I : ℂ)) * (((s - t : ℝ) : ℂ))) - 1) from by ring]
  by_cases hst : |s - t| ≤ 1
  · have hnorm2 : ‖((I : ℂ)) * (((s - t : ℝ) : ℂ))‖ = |s - t| := by
      calc ‖((I : ℂ)) * (((s - t : ℝ) : ℂ))‖ = ‖(I : ℂ)‖ * ‖((s - t : ℝ) : ℂ)‖ := norm_mul _ _
        _ = |s - t| := by
            rw [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have hle : ‖((I : ℂ)) * (((s - t : ℝ) : ℂ))‖ ≤ 1 := by rw [hnorm2]; exact hst
    calc ‖cexp (((I : ℂ)) * ((t : ℂ))) * (cexp (((I : ℂ)) * (((s - t : ℝ) : ℂ))) - 1)‖
        ≤ ‖cexp (((I : ℂ)) * ((t: ℂ)))‖ * ‖cexp (((I: ℂ)) * (((s - t : ℝ) : ℂ))) - 1‖ :=
          norm_mul_le _ _
      _ ≤ 1 * (2 * ‖((I : ℂ)) * (((s - t : ℝ) : ℂ))‖) := by
          rw [← hn1]
          exact mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le hle) (norm_nonneg _)
      _ = 2 * |s - t| := by rw [one_mul, hnorm2]
  · have hn2 : ‖cexp (((I : ℂ)) * (((s - t : ℝ) : ℂ))) - 1‖ ≤ 2 := by
      have hne : ‖cexp (((I: ℂ)) * (((s - t : ℝ) : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]
        have h0 : (((I: ℂ)) * (((s - t : ℝ) : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        rw [h0, Real.exp_zero]
      calc ‖cexp (((I: ℂ)) * (((s - t : ℝ) : ℂ))) - 1‖
          ≤ ‖cexp (((I: ℂ)) * (((s - t : ℝ) : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hne]; norm_num
    calc ‖cexp (((I: ℂ)) * ((t : ℂ))) * (cexp (((I: ℂ)) * (((s - t : ℝ) : ℂ))) - 1)‖
        ≤ ‖cexp (((I: ℂ)) * ((t : ℂ)))‖ * ‖cexp (((I: ℂ)) * (((s - t : ℝ) : ℂ))) - 1‖ :=
          norm_mul_le _ _
      _ ≤ 1 * 2 := by rw [hn1]; exact mul_le_mul_of_nonneg_left hn2 zero_le_one
      _ ≤ 2 * |s - t| := by
          have h1 : (1 : ℝ) < |s - t| := not_le.mp hst
          nlinarith [abs_nonneg (s - t), h1]

private theorem integrable_norm_le_one {G : Type*} [MeasurableSpace G] {μ : Measure G}
    [IsProbabilityMeasure μ] {f : G → ℂ} (hfm : AEStronglyMeasurable f μ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f μ := by
  have hI : Integrable (fun _ : G ↦ (1 : ℝ)) μ := integrable_const 1
  refine hI.mono' hfm ?_
  filter_upwards [] with x
  simpa using hf x

private theorem integral_norm_le_one {G : Type*} [MeasurableSpace G] {μ : Measure G}
    [IsProbabilityMeasure μ] {f : G → ℂ} (hfm : AEStronglyMeasurable f μ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, f x ∂μ‖ ≤ 1 := by
  calc ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : G, (1 : ℝ) ∂μ := by
        refine integral_mono ((integrable_norm_le_one hfm hf).norm) (integrable_const 1)
          (fun x ↦ hf x)
    _ = 1 := by simp

private theorem integrable_norm_stdGaussian : Integrable (fun x : E ↦ ‖x‖) (stdGaussian E) :=
  IsGaussian.integrable_id.norm

private theorem continuous_param_integral {X : Type*} [MetricSpace X] {Y : Type*}
    [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {G : X → Y → ℂ} {c : X → Y → ℝ}
    (hlip : ∀ x₀ x y, ‖G x y - G x₀ y‖ ≤ c x₀ y * (dist x x₀ + dist x x₀ ^ 2))
    (hc : ∀ x₀, Integrable (c x₀) μ) (hcn : ∀ x₀ y, 0 ≤ c x₀ y)
    (hGi : ∀ x, Integrable (G x) μ) :
    Continuous (fun x ↦ ∫ y, G x y ∂μ) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  have key : ∀ x : X, ‖(∫ y, G x y ∂μ) - (∫ y, G x₀ y ∂μ)‖
      ≤ (∫ y, c x₀ y ∂μ) * (dist x x₀ + dist x x₀ ^ 2) := by
    intro x
    have hint : Integrable (fun y ↦ G x y - G x₀ y) μ := (hGi x).sub (hGi x₀)
    rw [← integral_sub (hGi x) (hGi x₀)]
    calc ‖∫ y, (G x y - G x₀ y) ∂μ‖ ≤ ∫ y, ‖G x y - G x₀ y‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y, c x₀ y * (dist x x₀ + dist x x₀ ^ 2) ∂μ :=
          integral_mono hint.norm ((hc x₀).mul_const (dist x x₀ + dist x x₀ ^ 2))
            (fun y ↦ hlip x₀ x y)
      _ = (∫ y, c x₀ y ∂μ) * (dist x x₀ + dist x x₀ ^ 2) := integral_mul_const _ _
  have hM0 : 0 ≤ ∫ y, c x₀ y ∂μ := integral_nonneg (fun y ↦ hcn x₀ y)
  refine ⟨min 1 (ε / (2 * ((∫ y, c x₀ y ∂μ) + 1))), by positivity, ?_⟩
  intro x hx
  have hd1 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hd2 : dist x x₀ < ε / (2 * ((∫ y, c x₀ y ∂μ) + 1)) := lt_of_lt_of_le hx (min_le_right _ _)
  have hd0 : 0 ≤ dist x x₀ := dist_nonneg
  have hsq : dist x x₀ ^ 2 ≤ dist x x₀ := by nlinarith
  have hsum : dist x x₀ + dist x x₀ ^ 2 < 2 * (ε / (2 * ((∫ y, c x₀ y ∂μ) + 1))) := by nlinarith
  have h3 : (∫ y, c x₀ y ∂μ) * (dist x x₀ + dist x x₀ ^ 2)
      ≤ (∫ y, c x₀ y ∂μ) * (2 * (ε / (2 * ((∫ y, c x₀ y ∂μ) + 1)))) :=
    mul_le_mul_of_nonneg_left hsum.le hM0
  have h4 : (∫ y, c x₀ y ∂μ) * (2 * (ε / (2 * ((∫ y, c x₀ y ∂μ) + 1)))) < ε := by
    have hfrac : (∫ y, c x₀ y ∂μ) / ((∫ y, c x₀ y ∂μ) + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc (∫ y, c x₀ y ∂μ) * (2 * (ε / (2 * ((∫ y, c x₀ y ∂μ) + 1))))
        = ε * ((∫ y, c x₀ y ∂μ) / ((∫ y, c x₀ y ∂μ) + 1)) := by
          have hc1 : ((∫ y, c x₀ y ∂μ) + 1) ≠ 0 := by linarith
          field_simp [hc1]
      _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := by ring
  rw [dist_eq_norm]
  calc ‖(∫ y, G x y ∂μ) - (∫ y, G x₀ y ∂μ)‖ ≤ (∫ y, c x₀ y ∂μ) * (dist x x₀ + dist x x₀ ^ 2) :=
        key x
    _ ≤ (∫ y, c x₀ y ∂μ) * (2 * (ε / (2 * ((∫ y, c x₀ y ∂μ) + 1)))) := h3
    _ < ε := h4

set_option maxHeartbeats 1000000 in

private theorem gaussianBilinearCF_norm_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] E) (L : F →L[ℝ] E) (u v : F) :
    ‖gaussianBilinearCF T L u v‖ ^ 2
      = (gaussianBilinearCF T L (Real.sqrt 2 • u) 0
        * gaussianBilinearCF T L 0 (Real.sqrt 2 • v)).re := by
  classical
  set iv : F → F → E → E → ℂ := fun a b x y ↦
    cexp (I * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ)))
  set γ := stdGaussian E
  set ν := (γ).prod (γ)
  set ρ : E × E → E × E := fun p ↦ ((Real.sqrt 2)⁻¹ • (p.1 + p.2), (Real.sqrt 2)⁻¹ • (p.1 - p.2)) with hρ
  have hiv : ∀ a b : F, Integrable (Function.uncurry (iv a b)) ν := by
    intro a b
    have hI : Integrable (fun _ : E × E ↦ (1 : ℝ)) ν := integrable_const 1
    refine hI.mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun p ↦ by
        show ‖cexp (I * ((⟪p.1, T p.2⟫_ℝ : ℂ) + (⟪p.1, L b⟫_ℝ : ℂ) + (⟪p.2, L a⟫_ℝ : ℂ)))‖ ≤ 1
        rw [Complex.norm_exp]
        have hre : (I * ((⟪p.1, T p.2⟫_ℝ : ℂ) + (⟪p.1, L b⟫_ℝ : ℂ)
            + (⟪p.2, L a⟫_ℝ : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im]
        rw [hre, Real.exp_zero])
  have hF : ∀ a b : F, gaussianBilinearCF T L a b = ∫ p : E × E, iv a b p.1 p.2 ∂ν := by
    intro a b
    rw [gaussianBilinearCF, MeasureTheory.integral_integral (hiv a b)]
  have hconj : gaussianBilinearCF T L u v * conj (gaussianBilinearCF T L u v)
      = gaussianBilinearCF T L (Real.sqrt 2 • u) 0 * gaussianBilinearCF T L 0 (Real.sqrt 2 • v) := by
    rw [hF u v, hF (Real.sqrt 2 • u) 0, hF 0 (Real.sqrt 2 • v)]
    have hconjF : conj (∫ p : E × E, iv u v p.1 p.2 ∂ν)
        = ∫ p : E × E, conj (iv u v p.1 p.2) ∂ν := by
      rw [← integral_conj]
    rw [hconjF]
    rw [← integral_prod_mul (f := fun p : E × E ↦ iv u v p.1 p.2)
      (g := fun q : E × E ↦ conj (iv u v q.1 q.2))]

    have hiv1 : ∀ a b : F, ∀ x y : E, ‖iv a b x y‖ = 1 := by
      intro a b x y
      show ‖cexp (I * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ)))‖ = 1
      rw [Complex.norm_exp]
      have hre : (I * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im]
      rw [hre, Real.exp_zero]
    have hivC : ∀ (a b : F), Continuous (fun p : E × E ↦ iv a b p.1 p.2) := by
      intro a b
      show Continuous (fun p : E × E ↦ cexp ((I : ℂ) * ((⟪p.1, T p.2⟫_ℝ : ℂ)
        + (⟪p.1, L b⟫_ℝ : ℂ) + (⟪p.2, L a⟫_ℝ : ℂ))))
      fun_prop
    have hivmul : ∀ (a b c d : F) (x y x' y' : E),
        ‖iv a b x y * iv c d x' y'‖ ≤ 1 := by
      intro a b c d x y x' y'
      calc ‖iv a b x y * iv c d x' y'‖ ≤ ‖iv a b x y‖ * ‖iv c d x' y'‖ := norm_mul_le _ _
        _ = 1 := by rw [hiv1, hiv1, mul_one]
    have hivmulc : ∀ (a b c d : F) (x y x' y' : E),
        ‖iv a b x y * conj (iv c d x' y')‖ ≤ 1 := by
      intro a b c d x y x' y'
      calc ‖iv a b x y * conj (iv c d x' y')‖
          ≤ ‖iv a b x y‖ * ‖conj (iv c d x' y')‖ := norm_mul_le _ _
        _ = 1 := by rw [hiv1, Complex.norm_conj, hiv1, mul_one]
    have hsliceΨ : ∀ P : E × E, Integrable
        (fun q : E × E ↦ iv u v P.1 P.2 * conj (iv u v q.1 q.2)) ν := by
      intro P
      exact integrable_norm_le_one
        ((continuous_const.mul (continuous_conj.comp (hivC u v))).aestronglyMeasurable)
        (fun q ↦ hivmulc u v u v P.1 P.2 q.1 q.2)

    have hcomp : ∀ p p₀ : E × E, ‖p.1 - p₀.1‖ ≤ dist p p₀ ∧ ‖p.2 - p₀.2‖ ≤ dist p p₀ := by
      intro p p₀
      constructor
      · calc ‖p.1 - p₀.1‖ = dist p.1 p₀.1 := (dist_eq_norm _ _).symm
        _ ≤ max (dist p.1 p₀.1) (dist p.2 p₀.2) := le_max_left _ _
        _ = dist p p₀ := Prod.dist_eq.symm
      · calc ‖p.2 - p₀.2‖ = dist p.2 p₀.2 := (dist_eq_norm _ _).symm
        _ ≤ max (dist p.1 p₀.1) (dist p.2 p₀.2) := le_max_right _ _
        _ = dist p p₀ := Prod.dist_eq.symm
    have hncomp : ∀ p : E × E, ‖p.1‖ ≤ ‖p‖ ∧ ‖p.2‖ ≤ ‖p‖ := by
      intro p
      constructor
      · calc ‖p.1‖ ≤ max ‖p.1‖ ‖p.2‖ := le_max_left _ _
        _ = ‖p‖ := (Prod.norm_def p).symm
      · calc ‖p.2‖ ≤ max ‖p.1‖ ‖p.2‖ := le_max_right _ _
        _ = ‖p‖ := (Prod.norm_def p).symm
    have hnorm2le : ∀ p p₀ : E × E, ‖p.2‖ ≤ ‖p₀‖ + (dist p p₀ + dist p p₀ ^ 2) := by
      intro p p₀
      have h2 := (hcomp p p₀).2
      have h3 : ‖p.2‖ ≤ ‖p.2 - p₀.2‖ + ‖p₀.2‖ :=
        calc ‖p.2‖ = ‖(p.2 - p₀.2) + p₀.2‖ := by
              conv_lhs => rw [show p.2 = (p.2 - p₀.2) + p₀.2 from by abel]
            _ ≤ ‖p.2 - p₀.2‖ + ‖p₀.2‖ := norm_add_le _ _
      have h4 : ‖p₀.2‖ ≤ ‖p₀‖ := (hncomp p₀).2
      have hsq : 0 ≤ dist p p₀ ^ 2 := sq_nonneg _
      linarith

    have hivdiffx : ∀ (a b : F) (x x₀ y : E),
        ‖iv a b x y - iv a b x₀ y‖ ≤ 2 * (‖T‖ * ‖y‖ + ‖L b‖) * ‖x - x₀‖ := by
      intro a b x x₀ y
      have hpd : (⟪x, T y⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y, L a⟫_ℝ)
          - (⟪x₀, T y⟫_ℝ + ⟪x₀, L b⟫_ℝ + ⟪y, L a⟫_ℝ)
          = ⟪x - x₀, T y⟫_ℝ + ⟪x - x₀, L b⟫_ℝ := by
        simp only [inner_sub_left]
        ring
      have hb : |⟪x - x₀, T y⟫_ℝ + ⟪x - x₀, L b⟫_ℝ|
          ≤ ‖x - x₀‖ * (‖T‖ * ‖y‖) + ‖x - x₀‖ * ‖L b‖ := by
        have h1 : |⟪x - x₀, T y⟫_ℝ| ≤ ‖x - x₀‖ * (‖T‖ * ‖y‖) := by
          calc |⟪x - x₀, T y⟫_ℝ| = ‖⟪x - x₀, T y⟫_ℝ‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖x - x₀‖ * ‖T y‖ := norm_inner_le_norm _ _
            _ ≤ ‖x - x₀‖ * (‖T‖ * ‖y‖) := by
                exact mul_le_mul le_rfl (ContinuousLinearMap.le_opNorm T y)
                  (norm_nonneg _) (norm_nonneg _)
        have h2 : |⟪x - x₀, L b⟫_ℝ| ≤ ‖x - x₀‖ * ‖L b‖ := by
          calc |⟪x - x₀, L b⟫_ℝ| = ‖⟪x - x₀, L b⟫_ℝ‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖x - x₀‖ * ‖L b‖ := norm_inner_le_norm _ _
        calc |⟪x - x₀, T y⟫_ℝ + ⟪x - x₀, L b⟫_ℝ|
            ≤ |⟪x - x₀, T y⟫_ℝ| + |⟪x - x₀, L b⟫_ℝ| := abs_add_le _ _
          _ ≤ ‖x - x₀‖ * (‖T‖ * ‖y‖) + ‖x - x₀‖ * ‖L b‖ := add_le_add h1 h2
      show ‖cexp ((I : ℂ) * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ)))
          - cexp ((I : ℂ) * ((⟪x₀, T y⟫_ℝ : ℂ) + (⟪x₀, L b⟫_ℝ : ℂ)
            + (⟪y, L a⟫_ℝ : ℂ)))‖ ≤ _
      have e1 : ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ))
          = (((⟪x, T y⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y, L a⟫_ℝ : ℝ) : ℂ)) := by
        push_cast
        ring
      have e1₀ : ((⟪x₀, T y⟫_ℝ : ℂ) + (⟪x₀, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ))
          = (((⟪x₀, T y⟫_ℝ + ⟪x₀, L b⟫_ℝ + ⟪y, L a⟫_ℝ : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [e1, e1₀]
      refine le_trans (norm_sub_cexp_two_mul_le _ _) ?_
      have hre : ‖x - x₀‖ * (‖T‖ * ‖y‖) + ‖x - x₀‖ * ‖L b‖
          = (‖T‖ * ‖y‖ + ‖L b‖) * ‖x - x₀‖ := by ring
      calc 2 * |(⟪x, T y⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y, L a⟫_ℝ)
            - (⟪x₀, T y⟫_ℝ + ⟪x₀, L b⟫_ℝ + ⟪y, L a⟫_ℝ)|
          ≤ 2 * (‖x - x₀‖ * (‖T‖ * ‖y‖) + ‖x - x₀‖ * ‖L b‖) := by
              rw [hpd]
              exact mul_le_mul_of_nonneg_left hb two_pos.le
        _ = 2 * (‖T‖ * ‖y‖ + ‖L b‖) * ‖x - x₀‖ := by linear_combination hre
    have hivdiffy : ∀ (a b : F) (x y y₀ : E),
        ‖iv a b x y - iv a b x y₀‖ ≤ 2 * (‖T‖ * ‖x‖ + ‖L a‖) * ‖y - y₀‖ := by
      intro a b x y y₀
      have hpd : (⟪x, T y⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y, L a⟫_ℝ)
          - (⟪x, T y₀⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y₀, L a⟫_ℝ)
          = ⟪x, T (y - y₀)⟫_ℝ + ⟪y - y₀, L a⟫_ℝ := by
        simp only [inner_sub_left, inner_sub_right, map_sub]
        ring
      have hb : |⟪x, T (y - y₀)⟫_ℝ + ⟪y - y₀, L a⟫_ℝ|
          ≤ ‖x‖ * (‖T‖ * ‖y - y₀‖) + ‖y - y₀‖ * ‖L a‖ := by
        have h1 : |⟪x, T (y - y₀)⟫_ℝ| ≤ ‖x‖ * (‖T‖ * ‖y - y₀‖) := by
          calc |⟪x, T (y - y₀)⟫_ℝ| = ‖⟪x, T (y - y₀)⟫_ℝ‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖x‖ * ‖T (y - y₀)‖ := norm_inner_le_norm _ _
            _ ≤ ‖x‖ * (‖T‖ * ‖y - y₀‖) := by
                exact mul_le_mul le_rfl (ContinuousLinearMap.le_opNorm T _)
                  (norm_nonneg _) (norm_nonneg _)
        have h2 : |⟪y - y₀, L a⟫_ℝ| ≤ ‖y - y₀‖ * ‖L a‖ := by
          calc |⟪y - y₀, L a⟫_ℝ| = ‖⟪y - y₀, L a⟫_ℝ‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖y - y₀‖ * ‖L a‖ := norm_inner_le_norm _ _
        calc |⟪x, T (y - y₀)⟫_ℝ + ⟪y - y₀, L a⟫_ℝ|
            ≤ |⟪x, T (y - y₀)⟫_ℝ| + |⟪y - y₀, L a⟫_ℝ| := abs_add_le _ _
          _ ≤ ‖x‖ * (‖T‖ * ‖y - y₀‖) + ‖y - y₀‖ * ‖L a‖ := add_le_add h1 h2
      show ‖cexp ((I : ℂ) * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ)))
          - cexp ((I : ℂ) * ((⟪x, T y₀⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ)
            + (⟪y₀, L a⟫_ℝ : ℂ)))‖ ≤ _
      have e1 : ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ))
          = (((⟪x, T y⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y, L a⟫_ℝ : ℝ) : ℂ)) := by
        push_cast
        ring
      have e1₀ : ((⟪x, T y₀⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y₀, L a⟫_ℝ : ℂ))
          = (((⟪x, T y₀⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y₀, L a⟫_ℝ : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [e1, e1₀]
      refine le_trans (norm_sub_cexp_two_mul_le _ _) ?_
      have hre : ‖x‖ * (‖T‖ * ‖y - y₀‖) + ‖y - y₀‖ * ‖L a‖
          = (‖T‖ * ‖x‖ + ‖L a‖) * ‖y - y₀‖ := by ring
      calc 2 * |(⟪x, T y⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y, L a⟫_ℝ)
            - (⟪x, T y₀⟫_ℝ + ⟪x, L b⟫_ℝ + ⟪y₀, L a⟫_ℝ)|
          ≤ 2 * (‖x‖ * (‖T‖ * ‖y - y₀‖) + ‖y - y₀‖ * ‖L a‖) := by
              rw [hpd]
              exact mul_le_mul_of_nonneg_left hb two_pos.le
        _ = 2 * (‖T‖ * ‖x‖ + ‖L a‖) * ‖y - y₀‖ := by linear_combination hre

    have hintq1 : Integrable (fun q : E × E ↦ ‖q.1‖) ν :=
      integrable_norm_stdGaussian.comp_fst (stdGaussian E)
    have hintq2 : Integrable (fun q : E × E ↦ ‖q.2‖) ν :=
      integrable_norm_stdGaussian.comp_snd (stdGaussian E)

    have hcBC : ∀ a : E, Continuous (fun z : E × E ↦
        ∫ d : E, iv u v a z.1 * conj (iv u v z.2 d) ∂(stdGaussian E)) := by
      intro a
      apply continuous_param_integral (μ := stdGaussian E)
      · intro z₀ z d
        have h1 := (hcomp z z₀).1
        have h2 := (hcomp z z₀).2
        have hdy := hivdiffy u v a z.1 z₀.1
        have hdx := hivdiffx u v z.2 z₀.2 d
        have hb2 : ‖iv u v a z.1 * conj (iv u v z.2 d)
            - iv u v a z₀.1 * conj (iv u v z₀.2 d)‖
            ≤ 2 * (‖T‖ * ‖a‖ + ‖L u‖) * ‖z.1 - z₀.1‖
              + 2 * (‖T‖ * ‖d‖ + ‖L v‖) * ‖z.2 - z₀.2‖ := by
          have hd : iv u v a z.1 * conj (iv u v z.2 d) - iv u v a z₀.1 * conj (iv u v z₀.2 d)
              = (iv u v a z.1 - iv u v a z₀.1) * conj (iv u v z.2 d)
                + iv u v a z₀.1 * (conj (iv u v z.2 d) - conj (iv u v z₀.2 d)) := by ring
          have hn1 : ‖conj (iv u v z.2 d) - conj (iv u v z₀.2 d)‖
              = ‖iv u v z.2 d - iv u v z₀.2 d‖ := by
            conv_lhs => rw [← map_sub]
            rw [Complex.norm_conj]
          rw [hd]
          have e1 : ‖(iv u v a z.1 - iv u v a z₀.1) * conj (iv u v z.2 d)‖
              ≤ ‖iv u v a z.1 - iv u v a z₀.1‖ := by
            calc ‖(iv u v a z.1 - iv u v a z₀.1) * conj (iv u v z.2 d)‖
                ≤ ‖iv u v a z.1 - iv u v a z₀.1‖ * ‖conj (iv u v z.2 d)‖ :=
                  norm_mul_le _ _
              _ = ‖iv u v a z.1 - iv u v a z₀.1‖ * 1 := by
                  rw [Complex.norm_conj, hiv1]
              _ = ‖iv u v a z.1 - iv u v a z₀.1‖ := mul_one _
          have e2 : ‖iv u v a z₀.1 * (conj (iv u v z.2 d) - conj (iv u v z₀.2 d))‖
              ≤ ‖iv u v z.2 d - iv u v z₀.2 d‖ := by
            calc ‖iv u v a z₀.1 * (conj (iv u v z.2 d) - conj (iv u v z₀.2 d))‖
                ≤ ‖iv u v a z₀.1‖ * ‖conj (iv u v z.2 d) - conj (iv u v z₀.2 d)‖ :=
                  norm_mul_le _ _
              _ = 1 * ‖conj (iv u v z.2 d) - conj (iv u v z₀.2 d)‖ := by rw [hiv1]
              _ = 1 * ‖iv u v z.2 d - iv u v z₀.2 d‖ := by rw [hn1]
              _ = ‖iv u v z.2 d - iv u v z₀.2 d‖ := one_mul _
          exact le_trans (norm_add_le _ _)
            (le_trans (add_le_add e1 e2) (add_le_add hdy hdx))
        calc ‖iv u v a z.1 * conj (iv u v z.2 d) - iv u v a z₀.1 * conj (iv u v z₀.2 d)‖
            ≤ 2 * (‖T‖ * ‖a‖ + ‖L u‖) * ‖z.1 - z₀.1‖
              + 2 * (‖T‖ * ‖d‖ + ‖L v‖) * ‖z.2 - z₀.2‖ := hb2
          _ ≤ ((‖a‖ * (2 * ‖T‖) + 2 * ‖L u‖) + (‖d‖ * (2 * ‖T‖) + 2 * ‖L v‖))
              * (dist z z₀ + dist z z₀ ^ 2) := by
              have s1 : 2 * (‖T‖ * ‖a‖ + ‖L u‖) * ‖z.1 - z₀.1‖
                  ≤ 2 * (‖T‖ * ‖a‖ + ‖L u‖) * dist z z₀ :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
              have s2 : 2 * (‖T‖ * ‖d‖ + ‖L v‖) * ‖z.2 - z₀.2‖
                  ≤ 2 * (‖T‖ * ‖d‖ + ‖L v‖) * dist z z₀ :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              have hs : 0 ≤ dist z z₀ := dist_nonneg
              have hsq : 0 ≤ dist z z₀ ^ 2 := sq_nonneg _
              have p1 : 0 ≤ ‖T‖ * ‖a‖ * dist z z₀ ^ 2 :=
                mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsq
              have p2 : 0 ≤ ‖L u‖ * dist z z₀ ^ 2 := mul_nonneg (norm_nonneg _) hsq
              have p3 : 0 ≤ ‖T‖ * ‖d‖ * dist z z₀ ^ 2 :=
                mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsq
              have p4 : 0 ≤ ‖L v‖ * dist z z₀ ^ 2 := mul_nonneg (norm_nonneg _) hsq
              nlinarith [s1, s2, p1, p2, p3, p4]
      · intro z₀
        exact ((integrable_const _).add (integrable_const _)).add
          ((integrable_norm_stdGaussian.mul_const _).add (integrable_const _))
      · intro z₀ d; positivity
      · intro z
        have hc2' : Continuous fun d : E ↦ conj (iv u v z.2 d) :=
          continuous_conj.comp ((hivC u v).comp (continuous_const.prodMk continuous_id))
        exact integrable_norm_le_one
          ((continuous_const : Continuous fun _ : E ↦ iv u v a z.1).mul hc2').aestronglyMeasurable
          (fun d ↦ hivmulc u v u v a z.1 z.2 d)
    have hc2 : Continuous (fun p : E × E ↦
        ∫ q : E × E, iv u v p.1 q.1 * conj (iv u v p.2 q.2) ∂ν) := by
      apply continuous_param_integral (μ := ν)
      · intro p₀ p q
        have h1 := (hcomp p p₀).1
        have h2 := (hcomp p p₀).2
        have hbx := hivdiffx u v p.1 p₀.1 q.1
        have hby := hivdiffx u v p.2 p₀.2 q.2
        have hb : ‖iv u v p.1 q.1 * conj (iv u v p.2 q.2)
            - iv u v p₀.1 q.1 * conj (iv u v p₀.2 q.2)‖
            ≤ 2 * (‖T‖ * ‖q.1‖ + ‖L v‖) * ‖p.1 - p₀.1‖
              + 2 * (‖T‖ * ‖q.2‖ + ‖L v‖) * ‖p.2 - p₀.2‖ := by
          have hd : iv u v p.1 q.1 * conj (iv u v p.2 q.2)
                - iv u v p₀.1 q.1 * conj (iv u v p₀.2 q.2)
              = (iv u v p.1 q.1 - iv u v p₀.1 q.1) * conj (iv u v p.2 q.2)
                + iv u v p₀.1 q.1 * (conj (iv u v p.2 q.2) - conj (iv u v p₀.2 q.2)) := by ring
          have hn1 : ‖conj (iv u v p.2 q.2) - conj (iv u v p₀.2 q.2)‖
              = ‖iv u v p.2 q.2 - iv u v p₀.2 q.2‖ := by
            conv_lhs => rw [← map_sub]
            rw [Complex.norm_conj]
          rw [hd]
          have e1 : ‖(iv u v p.1 q.1 - iv u v p₀.1 q.1) * conj (iv u v p.2 q.2)‖
              ≤ ‖iv u v p.1 q.1 - iv u v p₀.1 q.1‖ := by
            calc ‖(iv u v p.1 q.1 - iv u v p₀.1 q.1) * conj (iv u v p.2 q.2)‖
                ≤ ‖iv u v p.1 q.1 - iv u v p₀.1 q.1‖ * ‖conj (iv u v p.2 q.2)‖ :=
                  norm_mul_le _ _
              _ = ‖iv u v p.1 q.1 - iv u v p₀.1 q.1‖ * 1 := by
                  rw [Complex.norm_conj, hiv1]
              _ = ‖iv u v p.1 q.1 - iv u v p₀.1 q.1‖ := mul_one _
          have e2 : ‖iv u v p₀.1 q.1 * (conj (iv u v p.2 q.2) - conj (iv u v p₀.2 q.2))‖
              ≤ ‖iv u v p.2 q.2 - iv u v p₀.2 q.2‖ := by
            calc ‖iv u v p₀.1 q.1 * (conj (iv u v p.2 q.2) - conj (iv u v p₀.2 q.2))‖
                ≤ ‖iv u v p₀.1 q.1‖ * ‖conj (iv u v p.2 q.2) - conj (iv u v p₀.2 q.2)‖ :=
                  norm_mul_le _ _
              _ = 1 * ‖conj (iv u v p.2 q.2) - conj (iv u v p₀.2 q.2)‖ := by rw [hiv1]
              _ = 1 * ‖iv u v p.2 q.2 - iv u v p₀.2 q.2‖ := by rw [hn1]
              _ = ‖iv u v p.2 q.2 - iv u v p₀.2 q.2‖ := one_mul _
          exact le_trans (norm_add_le _ _)
            (le_trans (add_le_add e1 e2) (add_le_add hbx hby))
        calc ‖iv u v p.1 q.1 * conj (iv u v p.2 q.2)
              - iv u v p₀.1 q.1 * conj (iv u v p₀.2 q.2)‖
            ≤ 2 * (‖T‖ * ‖q.1‖ + ‖L v‖) * ‖p.1 - p₀.1‖
              + 2 * (‖T‖ * ‖q.2‖ + ‖L v‖) * ‖p.2 - p₀.2‖ := hb
          _ ≤ ((‖q.1‖ + ‖q.2‖) * (2 * ‖T‖) + 4 * ‖L v‖)
              * (dist p p₀ + dist p p₀ ^ 2) := by
              have s1 : 2 * (‖T‖ * ‖q.1‖ + ‖L v‖) * ‖p.1 - p₀.1‖
                  ≤ 2 * (‖T‖ * ‖q.1‖ + ‖L v‖) * dist p p₀ :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
              have s2 : 2 * (‖T‖ * ‖q.2‖ + ‖L v‖) * ‖p.2 - p₀.2‖
                  ≤ 2 * (‖T‖ * ‖q.2‖ + ‖L v‖) * dist p p₀ :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              have hs : 0 ≤ dist p p₀ := dist_nonneg
              have hsq : 0 ≤ dist p p₀ ^ 2 := sq_nonneg _
              have p1 : 0 ≤ ‖T‖ * ‖q.1‖ * dist p p₀ ^ 2 :=
                mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsq
              have p2 : 0 ≤ ‖T‖ * ‖q.2‖ * dist p p₀ ^ 2 :=
                mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsq
              have p3 : 0 ≤ ‖L v‖ * dist p p₀ ^ 2 := mul_nonneg (norm_nonneg _) hsq
              nlinarith [s1, s2, p1, p2, p3]
      · intro p₀
        exact ((hintq1.add hintq2).mul_const _).add (integrable_const _)
      · intro p₀ q; positivity
      · intro p
        have hq1 : Continuous fun q : E × E ↦ iv u v p.1 q.1 :=
          (hivC u v).comp (continuous_const.prodMk continuous_fst)
        have hq2 : Continuous fun q : E × E ↦ iv u v p.2 q.2 :=
          (hivC u v).comp (continuous_const.prodMk continuous_snd)
        exact integrable_norm_le_one (hq1.mul (continuous_conj.comp hq2)).aestronglyMeasurable
          (fun q ↦ hivmulc u v u v p.1 q.1 p.2 q.2)
    have hc3 : Continuous (fun p : E × E ↦
        ∫ q : E × E, iv (Real.sqrt 2 • u) 0 p.1 q.2 * iv 0 (Real.sqrt 2 • v) p.2 q.1 ∂ν) := by
      apply continuous_param_integral (μ := ν)
      · intro p₀ p q
        have h1 := (hcomp p p₀).1
        have h2 := (hcomp p p₀).2
        have hbx := hivdiffx (Real.sqrt 2 • u) 0 p.1 p₀.1 q.2
        have hby := hivdiffx 0 (Real.sqrt 2 • v) p.2 p₀.2 q.1
        have hb : ‖iv (Real.sqrt 2 • u) 0 p.1 q.2 * iv 0 (Real.sqrt 2 • v) p.2 q.1
            - iv (Real.sqrt 2 • u) 0 p₀.1 q.2 * iv 0 (Real.sqrt 2 • v) p₀.2 q.1‖
            ≤ 2 * (‖T‖ * ‖q.2‖ + ‖L 0‖) * ‖p.1 - p₀.1‖
              + 2 * (‖T‖ * ‖q.1‖ + ‖L (Real.sqrt 2 • v)‖) * ‖p.2 - p₀.2‖ := by
          have hd : iv (Real.sqrt 2 • u) 0 p.1 q.2 * iv 0 (Real.sqrt 2 • v) p.2 q.1
                - iv (Real.sqrt 2 • u) 0 p₀.1 q.2 * iv 0 (Real.sqrt 2 • v) p₀.2 q.1
              = (iv (Real.sqrt 2 • u) 0 p.1 q.2 - iv (Real.sqrt 2 • u) 0 p₀.1 q.2)
                * iv 0 (Real.sqrt 2 • v) p.2 q.1
                + iv (Real.sqrt 2 • u) 0 p₀.1 q.2
                * (iv 0 (Real.sqrt 2 • v) p.2 q.1 - iv 0 (Real.sqrt 2 • v) p₀.2 q.1) := by ring
          rw [hd]
          have e1 : ‖(iv (Real.sqrt 2 • u) 0 p.1 q.2 - iv (Real.sqrt 2 • u) 0 p₀.1 q.2)
                * iv 0 (Real.sqrt 2 • v) p.2 q.1‖
              ≤ ‖iv (Real.sqrt 2 • u) 0 p.1 q.2 - iv (Real.sqrt 2 • u) 0 p₀.1 q.2‖ := by
            calc ‖(iv (Real.sqrt 2 • u) 0 p.1 q.2 - iv (Real.sqrt 2 • u) 0 p₀.1 q.2)
                    * iv 0 (Real.sqrt 2 • v) p.2 q.1‖
                ≤ ‖iv (Real.sqrt 2 • u) 0 p.1 q.2 - iv (Real.sqrt 2 • u) 0 p₀.1 q.2‖
                    * ‖iv 0 (Real.sqrt 2 • v) p.2 q.1‖ := norm_mul_le _ _
              _ = ‖iv (Real.sqrt 2 • u) 0 p.1 q.2 - iv (Real.sqrt 2 • u) 0 p₀.1 q.2‖ * 1 := by
                  rw [hiv1]
              _ = ‖iv (Real.sqrt 2 • u) 0 p.1 q.2 - iv (Real.sqrt 2 • u) 0 p₀.1 q.2‖ :=
                  mul_one _
          have e2 : ‖iv (Real.sqrt 2 • u) 0 p₀.1 q.2
                * (iv 0 (Real.sqrt 2 • v) p.2 q.1 - iv 0 (Real.sqrt 2 • v) p₀.2 q.1)‖
              ≤ ‖iv 0 (Real.sqrt 2 • v) p.2 q.1 - iv 0 (Real.sqrt 2 • v) p₀.2 q.1‖ := by
            calc ‖iv (Real.sqrt 2 • u) 0 p₀.1 q.2
                    * (iv 0 (Real.sqrt 2 • v) p.2 q.1 - iv 0 (Real.sqrt 2 • v) p₀.2 q.1)‖
                ≤ ‖iv (Real.sqrt 2 • u) 0 p₀.1 q.2‖
                    * ‖iv 0 (Real.sqrt 2 • v) p.2 q.1 - iv 0 (Real.sqrt 2 • v) p₀.2 q.1‖ :=
                  norm_mul_le _ _
              _ = 1 * ‖iv 0 (Real.sqrt 2 • v) p.2 q.1 - iv 0 (Real.sqrt 2 • v) p₀.2 q.1‖ := by
                  rw [hiv1]
              _ = ‖iv 0 (Real.sqrt 2 • v) p.2 q.1 - iv 0 (Real.sqrt 2 • v) p₀.2 q.1‖ :=
                  one_mul _
          exact le_trans (norm_add_le _ _)
            (le_trans (add_le_add e1 e2) (add_le_add hbx hby))
        calc ‖iv (Real.sqrt 2 • u) 0 p.1 q.2 * iv 0 (Real.sqrt 2 • v) p.2 q.1
              - iv (Real.sqrt 2 • u) 0 p₀.1 q.2 * iv 0 (Real.sqrt 2 • v) p₀.2 q.1‖
            ≤ 2 * (‖T‖ * ‖q.2‖ + ‖L 0‖) * ‖p.1 - p₀.1‖
              + 2 * (‖T‖ * ‖q.1‖ + ‖L (Real.sqrt 2 • v)‖) * ‖p.2 - p₀.2‖ := hb
          _ ≤ ((‖q.1‖ + ‖q.2‖) * (2 * ‖T‖) + (2 * ‖L 0‖ + 2 * ‖L (Real.sqrt 2 • v)‖))
              * (dist p p₀ + dist p p₀ ^ 2) := by
              have s1 : 2 * (‖T‖ * ‖q.2‖ + ‖L 0‖) * ‖p.1 - p₀.1‖
                  ≤ 2 * (‖T‖ * ‖q.2‖ + ‖L 0‖) * dist p p₀ :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
              have s2 : 2 * (‖T‖ * ‖q.1‖ + ‖L (Real.sqrt 2 • v)‖) * ‖p.2 - p₀.2‖
                  ≤ 2 * (‖T‖ * ‖q.1‖ + ‖L (Real.sqrt 2 • v)‖) * dist p p₀ :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              have hs : 0 ≤ dist p p₀ := dist_nonneg
              have hsq : 0 ≤ dist p p₀ ^ 2 := sq_nonneg _
              have p1 : 0 ≤ ‖T‖ * ‖q.1‖ * dist p p₀ ^ 2 :=
                mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsq
              have p2 : 0 ≤ ‖T‖ * ‖q.2‖ * dist p p₀ ^ 2 :=
                mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsq
              have p3 : 0 ≤ ‖L 0‖ * dist p p₀ ^ 2 := mul_nonneg (norm_nonneg _) hsq
              have p4 : 0 ≤ ‖L (Real.sqrt 2 • v)‖ * dist p p₀ ^ 2 :=
                mul_nonneg (norm_nonneg _) hsq
              nlinarith [s1, s2, p1, p2, p3, p4]
      · intro p₀
        exact ((hintq1.add hintq2).mul_const _).add
          ((integrable_const _).add (integrable_const _))
      · intro p₀ q; positivity
      · intro p
        have hq1 : Continuous fun q : E × E ↦ iv (Real.sqrt 2 • u) 0 p.1 q.2 :=
          (hivC _ _).comp (continuous_const.prodMk continuous_snd)
        have hq2 : Continuous fun q : E × E ↦ iv 0 (Real.sqrt 2 • v) p.2 q.1 :=
          (hivC _ _).comp (continuous_const.prodMk continuous_fst)
        exact integrable_norm_le_one (hq1.mul hq2).aestronglyMeasurable
          (fun q ↦ hivmul _ _ _ _ p.1 q.2 p.2 q.1)
    have hcBC' : ∀ a : E, Continuous (fun z : E × E ↦
        ∫ d : E, iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z.1 z.2 ∂(stdGaussian E)) := by
      intro a
      apply continuous_param_integral (μ := stdGaussian E)
      · intro z₀ z d
        have h1 := (hcomp z z₀).1
        have h2 := (hcomp z z₀).2
        have hdx := hivdiffx 0 (Real.sqrt 2 • v) z.1 z₀.1 z.2
        have hdy := hivdiffy 0 (Real.sqrt 2 • v) z₀.1 z.2 z₀.2
        have hb : ‖iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z.1 z.2
            - iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2‖
            ≤ ‖iv 0 (Real.sqrt 2 • v) z.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z.2‖
              + ‖iv 0 (Real.sqrt 2 • v) z₀.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2‖ := by
          have hd : iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z.1 z.2
                - iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2
              = iv (Real.sqrt 2 • u) 0 a d * ((iv 0 (Real.sqrt 2 • v) z.1 z.2
                  - iv 0 (Real.sqrt 2 • v) z₀.1 z.2)
                + (iv 0 (Real.sqrt 2 • v) z₀.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2)) := by
            ring
          rw [hd]
          calc ‖iv (Real.sqrt 2 • u) 0 a d * ((iv 0 (Real.sqrt 2 • v) z.1 z.2
                  - iv 0 (Real.sqrt 2 • v) z₀.1 z.2)
                + (iv 0 (Real.sqrt 2 • v) z₀.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2))‖
              ≤ ‖iv (Real.sqrt 2 • u) 0 a d‖ * ‖(iv 0 (Real.sqrt 2 • v) z.1 z.2
                  - iv 0 (Real.sqrt 2 • v) z₀.1 z.2)
                + (iv 0 (Real.sqrt 2 • v) z₀.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2)‖ :=
                norm_mul_le _ _
            _ = 1 * ‖(iv 0 (Real.sqrt 2 • v) z.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z.2)
                + (iv 0 (Real.sqrt 2 • v) z₀.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2)‖ := by
                rw [hiv1]
            _ = ‖(iv 0 (Real.sqrt 2 • v) z.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z.2)
                + (iv 0 (Real.sqrt 2 • v) z₀.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2)‖ :=
                one_mul _
            _ ≤ ‖iv 0 (Real.sqrt 2 • v) z.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z.2‖
                + ‖iv 0 (Real.sqrt 2 • v) z₀.1 z.2 - iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2‖ :=
                norm_add_le _ _
        have hbound : ‖iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z.1 z.2
            - iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2‖
            ≤ 2 * (‖T‖ * ‖z.2‖ + ‖L (Real.sqrt 2 • v)‖) * ‖z.1 - z₀.1‖
              + 2 * (‖T‖ * ‖z₀.1‖ + ‖L 0‖) * ‖z.2 - z₀.2‖ :=
          le_trans hb (add_le_add hdx hdy)
        have hz1 : ‖z.2‖ ≤ ‖z₀‖ + dist z z₀ := by
          have h3 : ‖z.2‖ ≤ ‖z.2 - z₀.2‖ + ‖z₀.2‖ :=
            calc ‖z.2‖ = ‖(z.2 - z₀.2) + z₀.2‖ := by
                  conv_lhs => rw [show z.2 = (z.2 - z₀.2) + z₀.2 from by abel]
                _ ≤ ‖z.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
          have h4 : ‖z₀.2‖ ≤ ‖z₀‖ := (hncomp z₀).2
          linarith
        have hz2 : ‖z₀.1‖ ≤ ‖z₀‖ := (hncomp z₀).1
        calc ‖iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z.1 z.2
              - iv (Real.sqrt 2 • u) 0 a d * iv 0 (Real.sqrt 2 • v) z₀.1 z₀.2‖
            ≤ 2 * (‖T‖ * ‖z.2‖ + ‖L (Real.sqrt 2 • v)‖) * ‖z.1 - z₀.1‖
              + 2 * (‖T‖ * ‖z₀.1‖ + ‖L 0‖) * ‖z.2 - z₀.2‖ := hbound
          _ ≤ ((‖z₀‖ * (4 * ‖T‖) + 2 * ‖T‖)
              + (2 * ‖L 0‖ + 2 * ‖L (Real.sqrt 2 • v)‖))
              * (dist z z₀ + dist z z₀ ^ 2) := by
              have s1 : 2 * (‖T‖ * ‖z.2‖ + ‖L (Real.sqrt 2 • v)‖) * ‖z.1 - z₀.1‖
                  ≤ 2 * (‖T‖ * ‖z.2‖ + ‖L (Real.sqrt 2 • v)‖) * dist z z₀ :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
              have s2 : 2 * (‖T‖ * ‖z₀.1‖ + ‖L 0‖) * ‖z.2 - z₀.2‖
                  ≤ 2 * (‖T‖ * ‖z₀.1‖ + ‖L 0‖) * dist z z₀ :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              have hb2 : ‖T‖ * ‖z.2‖ * dist z z₀
                  ≤ ‖T‖ * (‖z₀‖ + dist z z₀) * dist z z₀ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz1 (norm_nonneg _))
                  dist_nonneg
              have hb3 : ‖T‖ * ‖z₀.1‖ * dist z z₀ ≤ ‖T‖ * ‖z₀‖ * dist z z₀ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz2 (norm_nonneg _))
                  dist_nonneg
              have p1 : 0 ≤ ‖T‖ * dist z z₀ := mul_nonneg (norm_nonneg _) dist_nonneg
              have p2 : 0 ≤ ‖T‖ * ‖z₀‖ * dist z z₀ ^ 2 :=
                mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (sq_nonneg _)
              have p3 : 0 ≤ ‖L 0‖ * dist z z₀ ^ 2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
              have p4 : 0 ≤ ‖L (Real.sqrt 2 • v)‖ * dist z z₀ ^ 2 :=
                mul_nonneg (norm_nonneg _) (sq_nonneg _)
              nlinarith [s1, s2, hb2, hb3, p1, p2, p3, p4]
      · intro z₀
        exact integrable_const _
      · intro z₀ d; positivity
      · intro z
        have hcf : Continuous fun d : E ↦ iv (Real.sqrt 2 • u) 0 a d :=
          (hivC _ _).comp (continuous_const.prodMk continuous_id)
        exact integrable_norm_le_one (hcf.mul continuous_const).aestronglyMeasurable
          (fun d ↦ hivmul _ _ _ _ a d z.1 z.2)

    have hρC : Continuous ρ := by fun_prop
    have hMinvar : (ν.prod ν).map (Prod.map ρ ρ) = ν.prod ν := by
      have hνval : ν = (stdGaussian E).prod (stdGaussian E) := rfl
      rw [hνval, hρ]
      rw [← Measure.map_prod_map _ _ hρC.measurable hρC.measurable]
      rw [stdGaussian_prod_rotate_raw]
    have hRE : ∀ p q : E × E,
        ((⟪p.1, T q.1⟫_ℝ : ℂ) + (⟪p.1, L v⟫_ℝ : ℂ) + (⟪q.1, L u⟫_ℝ : ℂ))
          - ((⟪p.2, T q.2⟫_ℝ : ℂ) + (⟪p.2, L v⟫_ℝ : ℂ) + (⟪q.2, L u⟫_ℝ : ℂ))
        = ((⟪(ρ p).1, T (ρ q).2⟫_ℝ : ℂ) + (⟪(ρ q).2, L (Real.sqrt 2 • u)⟫_ℝ : ℂ))
          + ((⟪(ρ p).2, T (ρ q).1⟫_ℝ : ℂ) + (⟪(ρ p).2, L (Real.sqrt 2 • v)⟫_ℝ : ℂ)) :=
      fun p q ↦ rotLp_exponent T L u v (WithLp.toLp 2 p, WithLp.toLp 2 q)
    have hpcomb : ∀ p q : E × E,
        iv u v p.1 q.1 * conj (iv u v p.2 q.2)
          = cexp ((I : ℂ) * ((((⟪p.1, T q.1⟫_ℝ : ℂ) + (⟪p.1, L v⟫_ℝ : ℂ)
            + (⟪q.1, L u⟫_ℝ : ℂ))
            - ((⟪p.2, T q.2⟫_ℝ : ℂ) + (⟪p.2, L v⟫_ℝ : ℂ) + (⟪q.2, L u⟫_ℝ : ℂ))))) := by
      intro p q
      have he : conj (iv u v p.2 q.2)
          = cexp (-(I * ((⟪p.2, T q.2⟫_ℝ : ℂ) + (⟪p.2, L v⟫_ℝ : ℂ)
            + (⟪q.2, L u⟫_ℝ : ℂ)))) := by
        show conj (cexp (I * ((⟪p.2, T q.2⟫_ℝ : ℂ) + (⟪p.2, L v⟫_ℝ : ℂ)
            + (⟪q.2, L u⟫_ℝ : ℂ)))) = _
        rw [← exp_conj]
        congr 1
        simp only [map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
        ring
      rw [he]
      show cexp (I * ((⟪p.1, T q.1⟫_ℝ : ℂ) + (⟪p.1, L v⟫_ℝ : ℂ) + (⟪q.1, L u⟫_ℝ : ℂ)))
          * cexp (-(I * ((⟪p.2, T q.2⟫_ℝ : ℂ) + (⟪p.2, L v⟫_ℝ : ℂ)
            + (⟪q.2, L u⟫_ℝ : ℂ)))) = _
      rw [← Complex.exp_add]
      congr 1
      ring
    have hsplit : ∀ p q : E × E,
        cexp ((I : ℂ) * (((⟪(ρ p).1, T (ρ q).2⟫_ℝ : ℂ)
          + (⟪(ρ q).2, L (Real.sqrt 2 • u)⟫_ℝ : ℂ))
          + ((⟪(ρ p).2, T (ρ q).1⟫_ℝ : ℂ) + (⟪(ρ p).2, L (Real.sqrt 2 • v)⟫_ℝ : ℂ))))
          = iv (Real.sqrt 2 • u) 0 (ρ p).1 (ρ q).2
            * iv 0 (Real.sqrt 2 • v) (ρ p).2 (ρ q).1 := by
      intro p q
      have h1 : iv (Real.sqrt 2 • u) 0 (ρ p).1 (ρ q).2
          = cexp ((I : ℂ) * ((⟪(ρ p).1, T (ρ q).2⟫_ℝ : ℂ)
            + (⟪(ρ q).2, L (Real.sqrt 2 • u)⟫_ℝ : ℂ))) := by
        show cexp (I * ((⟪(ρ p).1, T (ρ q).2⟫_ℝ : ℂ) + (⟪(ρ p).1, L 0⟫_ℝ : ℂ)
            + (⟪(ρ q).2, L (Real.sqrt 2 • u)⟫_ℝ : ℂ))) = _
        rw [map_zero L, inner_zero_right, Complex.ofReal_zero, add_zero]
      have h2 : iv 0 (Real.sqrt 2 • v) (ρ p).2 (ρ q).1
          = cexp ((I : ℂ) * ((⟪(ρ p).2, T (ρ q).1⟫_ℝ : ℂ)
            + (⟪(ρ p).2, L (Real.sqrt 2 • v)⟫_ℝ : ℂ))) := by
        show cexp (I * ((⟪(ρ p).2, T (ρ q).1⟫_ℝ : ℂ) + (⟪(ρ p).2, L (Real.sqrt 2 • v)⟫_ℝ : ℂ)
            + (⟪(ρ q).1, L 0⟫_ℝ : ℂ))) = _
        rw [map_zero L, inner_zero_right, Complex.ofReal_zero, add_zero]
      rw [h1, h2, ← Complex.exp_add]
      congr 1
      ring

    have hΨC : Continuous (fun r : (E × E) × (E × E) ↦
        iv u v r.1.1 r.1.2 * conj (iv u v r.2.1 r.2.2)) := by
      show Continuous (fun r : (E × E) × (E × E) ↦
        cexp ((I : ℂ) * ((⟪r.1.1, T r.1.2⟫_ℝ : ℂ) + (⟪r.1.1, L v⟫_ℝ : ℂ)
          + (⟪r.1.2, L u⟫_ℝ : ℂ)))
        * conj (cexp ((I : ℂ) * ((⟪r.2.1, T r.2.2⟫_ℝ : ℂ) + (⟪r.2.1, L v⟫_ℝ : ℂ)
          + (⟪r.2.2, L u⟫_ℝ : ℂ)))))
      fun_prop
    have hΨint : Integrable (fun r : (E × E) × (E × E) ↦
        iv u v r.1.1 r.1.2 * conj (iv u v r.2.1 r.2.2)) (ν.prod ν) :=
      integrable_norm_le_one hΨC.aestronglyMeasurable
        (fun r ↦ hivmulc u v u v r.1.1 r.1.2 r.2.1 r.2.2)
    calc (∫ r : (E × E) × (E × E),
          iv u v r.1.1 r.1.2 * conj (iv u v r.2.1 r.2.2) ∂(ν.prod ν))
        = ∫ P : E × E, ∫ Q : E × E, iv u v P.1 P.2 * conj (iv u v Q.1 Q.2) ∂ν ∂ν :=
          integral_prod _ hΨint
      _ = ∫ x : E, ∫ y : E, ∫ Q : E × E, iv u v x y * conj (iv u v Q.1 Q.2)
            ∂ν ∂(stdGaussian E) ∂(stdGaussian E) :=
          integral_prod _ hΨint.integral_prod_left
      _ = ∫ x : E, ∫ y : E, ∫ x' : E, ∫ y' : E, iv u v x y * conj (iv u v x' y')
            ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) := by
          exact integral_congr_ae (ae_of_all _ (fun x ↦ integral_congr_ae (ae_of_all _
            (fun y ↦ integral_prod _ (hsliceΨ (x, y))))))
      _ = ∫ x : E, ∫ x' : E, ∫ y : E, ∫ y' : E, iv u v x y * conj (iv u v x' y')
            ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) := by
          exact integral_congr_ae (ae_of_all _ (fun x ↦ integral_integral_swap (
            show Integrable (Function.uncurry fun y x' : E ↦
              ∫ y' : E, iv u v x y * conj (iv u v x' y') ∂(stdGaussian E))
              ((stdGaussian E).prod (stdGaussian E)) from
            integrable_norm_le_one ((hcBC x).aestronglyMeasurable)
              (fun z ↦ integral_norm_le_one
                (Continuous.aestronglyMeasurable
                  (show Continuous fun d : E ↦ iv u v x z.1 * conj (iv u v z.2 d) from
                    (continuous_const : Continuous fun _ : E ↦ iv u v x z.1).mul
                      (continuous_conj.comp ((hivC u v).comp
                        (continuous_const.prodMk continuous_id)))))
                (fun y' ↦ hivmulc u v u v x z.1 z.2 y')))))
      _ = ∫ p : E × E, ∫ q : E × E, iv u v p.1 q.1 * conj (iv u v p.2 q.2) ∂ν ∂ν := by
          have hmg : ∀ x x' : E, (∫ y : E, ∫ y' : E, iv u v x y * conj (iv u v x' y')
              ∂(stdGaussian E) ∂(stdGaussian E))
              = ∫ q : E × E, iv u v x q.1 * conj (iv u v x' q.2) ∂ν :=
            fun x x' ↦ integral_integral (integrable_norm_le_one
              (Continuous.aestronglyMeasurable
                (show Continuous (fun q : E × E ↦ iv u v x q.1 * conj (iv u v x' q.2)) from
                  ((hivC u v).comp (continuous_const.prodMk continuous_fst)).mul
                    (continuous_conj.comp ((hivC u v).comp
                      (continuous_const.prodMk continuous_snd)))))
              (fun q ↦ hivmulc u v u v x q.1 x' q.2))
          rw [integral_congr_ae (ae_of_all _ (fun x ↦ integral_congr_ae (ae_of_all _
            (fun x' ↦ hmg x x'))))]
          exact integral_integral (integrable_norm_le_one hc2.aestronglyMeasurable
            (fun p ↦ integral_norm_le_one
              (Continuous.aestronglyMeasurable
                (show Continuous (fun q : E × E ↦ iv u v p.1 q.1 * conj (iv u v p.2 q.2)) from
                  ((hivC u v).comp (continuous_const.prodMk continuous_fst)).mul
                    (continuous_conj.comp ((hivC u v).comp
                      (continuous_const.prodMk continuous_snd)))))
              (fun q ↦ hivmulc u v u v p.1 q.1 p.2 q.2)))
      _ = ∫ p : E × E, ∫ q : E × E, iv (Real.sqrt 2 • u) 0 (ρ p).1 (ρ q).2
            * iv 0 (Real.sqrt 2 • v) (ρ p).2 (ρ q).1 ∂ν ∂ν := by
          rw [integral_congr_ae (ae_of_all _ (fun p ↦ integral_congr_ae (ae_of_all _
            (fun q ↦ by rw [hpcomb p q, hRE p q, hsplit p q]))))]
      _ = ∫ z : (E × E) × (E × E),
            iv (Real.sqrt 2 • u) 0 (ρ z.1).1 (ρ z.2).2
            * iv 0 (Real.sqrt 2 • v) (ρ z.1).2 (ρ z.2).1 ∂(ν.prod ν) := by
          have hf1 : Continuous fun z : (E × E) × (E × E) ↦
              iv (Real.sqrt 2 • u) 0 (ρ z.1).1 (ρ z.2).2 :=
            (hivC _ _).comp (((hρC.comp continuous_fst).fst).prodMk
              ((hρC.comp continuous_snd).snd))
          have hf2 : Continuous fun z : (E × E) × (E × E) ↦
              iv 0 (Real.sqrt 2 • v) (ρ z.1).2 (ρ z.2).1 :=
            (hivC _ _).comp (((hρC.comp continuous_fst).snd).prodMk
              ((hρC.comp continuous_snd).fst))
          exact integral_integral (integrable_norm_le_one (hf1.mul hf2).aestronglyMeasurable
            (fun z ↦ hivmul _ _ _ _ (ρ z.1).1 (ρ z.2).2 (ρ z.1).2 (ρ z.2).1))
      _ = ∫ z : (E × E) × (E × E),
            iv (Real.sqrt 2 • u) 0 z.1.1 z.2.2 * iv 0 (Real.sqrt 2 • v) z.1.2 z.2.1
            ∂(ν.prod ν) := by
          have hmap : (∫ z : (E × E) × (E × E),
              iv (Real.sqrt 2 • u) 0 z.1.1 z.2.2 * iv 0 (Real.sqrt 2 • v) z.1.2 z.2.1
              ∂(ν.prod ν))
              = ∫ z : (E × E) × (E × E),
                iv (Real.sqrt 2 • u) 0 (ρ z.1).1 (ρ z.2).2
                * iv 0 (Real.sqrt 2 • v) (ρ z.1).2 (ρ z.2).1 ∂(ν.prod ν) := by
            conv_lhs => rw [← hMinvar]
            rw [integral_map (hρC.prodMap hρC).aemeasurable
              (Continuous.aestronglyMeasurable (by fun_prop))]
            rfl
          rw [hmap]
      _ = ∫ x : E, ∫ x' : E, ∫ y : E, ∫ y' : E,
            iv (Real.sqrt 2 • u) 0 x y' * iv 0 (Real.sqrt 2 • v) x' y
            ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) := by
          have hFint : Integrable (fun z : (E × E) × (E × E) ↦
              iv (Real.sqrt 2 • u) 0 z.1.1 z.2.2 * iv 0 (Real.sqrt 2 • v) z.1.2 z.2.1)
              (ν.prod ν) :=
            integrable_norm_le_one
              (((hivC _ _).comp
                  ((continuous_fst.comp continuous_fst).prodMk
                    (continuous_snd.comp continuous_snd))).mul
                ((hivC _ _).comp
                  ((continuous_snd.comp continuous_fst).prodMk
                    (continuous_fst.comp continuous_snd)))).aestronglyMeasurable
              (fun z ↦ hivmul _ _ _ _ z.1.1 z.2.2 z.1.2 z.2.1)
          rw [integral_prod _ hFint]
          rw [integral_prod _ hFint.integral_prod_left]
          have hpair : ∀ x x' : E, (∫ q : E × E,
                iv (Real.sqrt 2 • u) 0 x q.2 * iv 0 (Real.sqrt 2 • v) x' q.1 ∂ν)
              = ∫ y : E, ∫ y' : E, iv (Real.sqrt 2 • u) 0 x y'
                * iv 0 (Real.sqrt 2 • v) x' y
                ∂(stdGaussian E) ∂(stdGaussian E) :=
            fun x x' ↦ integral_prod
              (fun q : E × E ↦
                iv (Real.sqrt 2 • u) 0 x q.2 * iv 0 (Real.sqrt 2 • v) x' q.1)
              (integrable_norm_le_one (μ := ν)
                (Continuous.aestronglyMeasurable
                  (show Continuous (fun q : E × E ↦
                      iv (Real.sqrt 2 • u) 0 x q.2 * iv 0 (Real.sqrt 2 • v) x' q.1) from
                    ((hivC _ _).comp (continuous_const.prodMk continuous_snd)).mul
                      ((hivC _ _).comp (continuous_const.prodMk continuous_fst))))
                (fun q ↦ hivmul _ _ _ _ x q.2 x' q.1))
          exact integral_congr_ae (ae_of_all _ (fun x ↦ integral_congr_ae (ae_of_all _
            (fun x' ↦ hpair x x'))))
      _ = ∫ x : E, ∫ y : E, ∫ x' : E, ∫ y' : E,
            iv (Real.sqrt 2 • u) 0 x y' * iv 0 (Real.sqrt 2 • v) x' y
            ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E) := by
          exact integral_congr_ae (ae_of_all _ (fun x ↦ integral_integral_swap (
            show Integrable (Function.uncurry fun x' y : E ↦
              ∫ y' : E, iv (Real.sqrt 2 • u) 0 x y' * iv 0 (Real.sqrt 2 • v) x' y
                ∂(stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) from
            integrable_norm_le_one ((hcBC' x).aestronglyMeasurable)
              (fun z ↦ integral_norm_le_one
                (Continuous.aestronglyMeasurable
                  (show Continuous (fun d : E ↦
                    iv (Real.sqrt 2 • u) 0 x d * iv 0 (Real.sqrt 2 • v) z.1 z.2) from
                    ((hivC _ _).comp (continuous_const.prodMk continuous_id)).mul
                      continuous_const))
                (fun d ↦ hivmul _ _ _ _ x d z.1 z.2)))))
      _ = (∫ p : E × E, iv (Real.sqrt 2 • u) 0 p.1 p.2 ∂ν)
            * (∫ q : E × E, iv 0 (Real.sqrt 2 • v) q.1 q.2 ∂ν) := by
          have e1 : ∀ x y x' : E, (∫ y' : E,
                iv (Real.sqrt 2 • u) 0 x y' * iv 0 (Real.sqrt 2 • v) x' y
                ∂(stdGaussian E))
              = (∫ y' : E, iv (Real.sqrt 2 • u) 0 x y' ∂(stdGaussian E))
                * iv 0 (Real.sqrt 2 • v) x' y :=
            fun _ _ _ ↦ integral_mul_const _ _
          have e2 : ∀ x y : E, (∫ x' : E,
                (∫ y' : E, iv (Real.sqrt 2 • u) 0 x y' ∂(stdGaussian E))
                * iv 0 (Real.sqrt 2 • v) x' y ∂(stdGaussian E))
              = (∫ y' : E, iv (Real.sqrt 2 • u) 0 x y' ∂(stdGaussian E))
                * (∫ x' : E, iv 0 (Real.sqrt 2 • v) x' y ∂(stdGaussian E)) :=
            fun _ _ ↦ integral_const_mul _ _
          have e3 : ∀ x : E, (∫ y : E,
                (∫ y' : E, iv (Real.sqrt 2 • u) 0 x y' ∂(stdGaussian E))
                * (∫ x' : E, iv 0 (Real.sqrt 2 • v) x' y ∂(stdGaussian E))
                ∂(stdGaussian E))
              = (∫ y' : E, iv (Real.sqrt 2 • u) 0 x y' ∂(stdGaussian E))
                * (∫ y : E, ∫ x' : E, iv 0 (Real.sqrt 2 • v) x' y
                    ∂(stdGaussian E) ∂(stdGaussian E)) :=
            fun _ ↦ integral_const_mul _ _
          have h_x : ∀ x : E, (∫ y : E, ∫ x' : E, ∫ y' : E,
                iv (Real.sqrt 2 • u) 0 x y' * iv 0 (Real.sqrt 2 • v) x' y
                ∂(stdGaussian E) ∂(stdGaussian E) ∂(stdGaussian E))
              = (∫ y' : E, iv (Real.sqrt 2 • u) 0 x y' ∂(stdGaussian E))
                * (∫ y : E, ∫ x' : E, iv 0 (Real.sqrt 2 • v) x' y
                    ∂(stdGaussian E) ∂(stdGaussian E)) := by
            intro x
            rw [integral_congr_ae (ae_of_all _ (fun y ↦ integral_congr_ae (ae_of_all _
              (fun x' ↦ e1 x y x'))))]
            rw [integral_congr_ae (ae_of_all _ (fun y ↦ e2 x y))]
            exact e3 x
          rw [integral_congr_ae (ae_of_all _ h_x)]
          rw [integral_mul_const _ _]
          rw [integral_integral (hiv (Real.sqrt 2 • u) 0)]
          rw [integral_integral_swap (show Integrable (Function.uncurry fun y x' : E ↦
              iv 0 (Real.sqrt 2 • v) x' y) ((stdGaussian E).prod (stdGaussian E)) from
            integrable_norm_le_one ((hivC _ _).comp continuous_swap).aestronglyMeasurable
              (fun q ↦ (hiv1 0 (Real.sqrt 2 • v) q.2 q.1).le))]
          rw [integral_integral (hiv 0 (Real.sqrt 2 • v))]

  have hre : (gaussianBilinearCF T L u v * conj (gaussianBilinearCF T L u v)).re
      = ‖gaussianBilinearCF T L u v‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_eq_norm_sq _
  rw [← hre, hconj]

private theorem rpow_split_one {θ c0 x y : ℝ} (hθ : 0 ≤ θ) (hθ' : 0 ≤ 1 - θ)
    (hc0 : 0 < c0) (hx : 0 < x) (hy : 0 < y) :
    x ^ θ * y ^ (1 - θ) = c0 * (x / c0) ^ θ * (y / c0) ^ (1 - θ) := by
  have hx2 : x = c0 * (x / c0) := by field_simp
  have hy2 : y = c0 * (y / c0) := by field_simp
  have hmerge : c0 ^ θ * c0 ^ (1 - θ) = c0 := by
    rw [← Real.rpow_add_of_nonneg hc0.le hθ hθ', show θ + (1 - θ) = 1 from by ring,
      Real.rpow_one]
  calc x ^ θ * y ^ (1 - θ) = (c0 * (x / c0)) ^ θ * (c0 * (y / c0)) ^ (1 - θ) := by
        rw [← hx2, ← hy2]
      _ = (c0 ^ θ * (x / c0) ^ θ) * (c0 ^ (1 - θ) * (y / c0) ^ (1 - θ)) := by
        rw [Real.mul_rpow hc0.le (div_nonneg hx.le hc0.le),
          Real.mul_rpow hc0.le (div_nonneg hy.le hc0.le)]
      _ = (c0 ^ θ * c0 ^ (1 - θ)) * ((x / c0) ^ θ * (y / c0) ^ (1 - θ)) := by ring
      _ = c0 * ((x / c0) ^ θ * (y / c0) ^ (1 - θ)) := by rw [hmerge]
      _ = c0 * (x / c0) ^ θ * (y / c0) ^ (1 - θ) := by ring

private theorem rpow_interp_sq {θ c0 x y : ℝ} (hθ : 0 ≤ θ) (hθ' : 0 ≤ 1 - θ)
    (hc0 : 0 < c0) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    c0 * x ^ (2 * θ) * (c0 * y ^ (2 * (1 - θ))) = (c0 * x ^ θ * y ^ (1 - θ)) ^ 2 := by
  have h2a : x ^ (2 * θ) = (x ^ θ) ^ 2 := by
    rw [show (2 * θ) = θ + θ from by ring, Real.rpow_add_of_nonneg hx hθ hθ, ← pow_two]
  have h2b : y ^ (2 * (1 - θ)) = (y ^ (1 - θ)) ^ 2 := by
    rw [show (2 * (1 - θ)) = (1 - θ) + (1 - θ) from by ring,
      Real.rpow_add_of_nonneg hy hθ' hθ', ← pow_two]
  rw [h2a, h2b]
  ring

theorem gaussianCF_geometricInterpolation (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a b : F)
    (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 1) :
    ‖gaussianBilinearCF T L (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖ =
      (gaussianBilinearCF T L a 0).re ^ θ * (gaussianBilinearCF T L 0 b).re ^ (1 - θ) := by
  classical
  obtain ⟨hpa, hpb, hp0, hs⟩ := gaussianCF_oneSidedQuadraticScaling T L a b
  have hsa : ∀ t : ℝ, gaussianBilinearCF T L (t • a) 0 =
      gaussianBilinearCF T L 0 0 *
        (gaussianBilinearCF T L a 0 / gaussianBilinearCF T L 0 0) ^ ((t ^ 2 : ℝ) : ℂ) :=
    fun t ↦ (hs t).1
  have hsb : ∀ t : ℝ, gaussianBilinearCF T L 0 (t • b) =
      gaussianBilinearCF T L 0 0 *
        (gaussianBilinearCF T L 0 b / gaussianBilinearCF T L 0 0) ^ ((t ^ 2 : ℝ) : ℂ) :=
    fun t ↦ (hs t).2 t
  have hima : ∀ a' : F, (gaussianBilinearCF T L a' 0).im = 0 := by
    intro a'
    rw [gaussianBilinearCF_a_zero, gaussian_anisotropic_integral T (L a'),
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_im]
  have himb : ∀ b' : F, (gaussianBilinearCF T L 0 b').im = 0 := by
    intro b'
    rw [gaussianBilinearCF_b_zero, gaussian_anisotropic_integral T.adjoint (L b'),
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_im]
  have hof : ∀ z : ℂ, z.im = 0 → z = ((z.re : ℝ) : ℂ) := fun z hz ↦
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact hz)

  have hra : ∀ t : ℝ, (gaussianBilinearCF T L (t • a) 0).re
      = (gaussianBilinearCF T L 0 0).re
        * ((gaussianBilinearCF T L a 0).re / (gaussianBilinearCF T L 0 0).re) ^ (t ^ 2) := by
    intro t
    have hscal := hsa t
    have hz1 : gaussianBilinearCF T L a 0
        = (((gaussianBilinearCF T L a 0).re : ℝ) : ℂ) := hof _ (hima a)
    have hz2 : gaussianBilinearCF T L (0 : F) 0
        = (((gaussianBilinearCF T L (0 : F) 0).re : ℝ) : ℂ) := hof _ (hima 0)
    rw [hz1, hz2] at hscal
    rw [hscal, ← Complex.ofReal_div,
      ← Complex.ofReal_cpow (div_nonneg hpa.le hp0.le),
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hrb : ∀ t : ℝ, (gaussianBilinearCF T L 0 (t • b)).re
      = (gaussianBilinearCF T L 0 0).re
        * ((gaussianBilinearCF T L 0 b).re / (gaussianBilinearCF T L 0 0).re) ^ (t ^ 2) := by
    intro t
    have hscal := hsb t
    have hz1 : gaussianBilinearCF T L 0 b
        = (((gaussianBilinearCF T L 0 b).re : ℝ) : ℂ) := hof _ (himb b)
    have hz2 : gaussianBilinearCF T L (0 : F) 0
        = (((gaussianBilinearCF T L (0 : F) 0).re : ℝ) : ℂ) := hof _ (hima 0)
    rw [hz1, hz2] at hscal
    rw [hscal, ← Complex.ofReal_div,
      ← Complex.ofReal_cpow (div_nonneg hpb.le hp0.le),
      ← Complex.ofReal_mul, Complex.ofReal_re]

  have hnsq := gaussianBilinearCF_norm_sq T L (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)
  rw [smul_smul, smul_smul] at hnsq
  have ht2 : (Real.sqrt 2 * Real.sqrt θ) ^ 2 = 2 * θ := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt hθ₁]
  have ht2' : (Real.sqrt 2 * Real.sqrt (1 - θ)) ^ 2 = 2 * (1 - θ) := by
    have h1 : 0 ≤ 1 - θ := by linarith
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt h1]
  have hva := hra (Real.sqrt 2 * Real.sqrt θ)
  have hvb := hrb (Real.sqrt 2 * Real.sqrt (1 - θ))
  rw [ht2] at hva
  rw [ht2'] at hvb
  have hprod : (gaussianBilinearCF T L ((Real.sqrt 2 * Real.sqrt θ) • a) 0
      * gaussianBilinearCF T L 0 ((Real.sqrt 2 * Real.sqrt (1 - θ)) • b)).re
      = (gaussianBilinearCF T L ((Real.sqrt 2 * Real.sqrt θ) • a) 0).re
        * (gaussianBilinearCF T L 0 ((Real.sqrt 2 * Real.sqrt (1 - θ)) • b)).re := by
    rw [Complex.mul_re, hima _, himb _, mul_zero, sub_zero]
  have hsplit := rpow_split_one hθ₁ (by linarith) hp0 hpa hpb
  rw [hsplit]
  rw [show ‖gaussianBilinearCF T L (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖
      = Real.sqrt (‖gaussianBilinearCF T L (Real.sqrt θ • a)
        (Real.sqrt (1 - θ) • b)‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm,
    hnsq, hprod, hva, hvb]
  have hnn : 0 ≤ (gaussianBilinearCF T L 0 0).re
      * ((gaussianBilinearCF T L a 0).re / (gaussianBilinearCF T L 0 0).re) ^ θ
      * ((gaussianBilinearCF T L 0 b).re / (gaussianBilinearCF T L 0 0).re) ^ (1 - θ) :=
    mul_nonneg (mul_nonneg hp0.le
      (Real.rpow_nonneg (div_nonneg hpa.le hp0.le) θ))
      (Real.rpow_nonneg (div_nonneg hpb.le hp0.le) (1 - θ))
  refine (Real.sqrt_eq_iff_mul_self_eq ?_ hnn).mpr ?_
  · exact mul_nonneg (mul_nonneg hp0.le
      (Real.rpow_nonneg (div_nonneg hpa.le hp0.le) (2 * θ)))
      (mul_nonneg hp0.le (Real.rpow_nonneg (div_nonneg hpb.le hp0.le) (2 * (1 - θ))))
  · rw [← sq]
    exact rpow_interp_sq hθ₁ (by linarith) hp0
      (div_nonneg hpa.le hp0.le) (div_nonneg hpb.le hp0.le)

private theorem gaussianCF_integrand_norm_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a b : F) (p : E × E) :
    ‖cexp ((I : ℂ) * ((⟪p.1, T p.2⟫_ℝ : ℂ) + (⟪p.1, L b⟫_ℝ : ℂ)
      + (⟪p.2, L a⟫_ℝ : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : ((I : ℂ) * ((⟪p.1, T p.2⟫_ℝ : ℂ) + (⟪p.1, L b⟫_ℝ : ℂ)
      + (⟪p.2, L a⟫_ℝ : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im]
  rw [hre, Real.exp_zero]

private theorem gaussianBilinearCF_norm_le_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a b : F) :
    ‖gaussianBilinearCF T L a b‖ ≤ 1 := by
  have hcont : Continuous fun p : E × E ↦
      cexp ((I : ℂ) * ((⟪p.1, T p.2⟫_ℝ : ℂ) + (⟪p.1, L b⟫_ℝ : ℂ) + (⟪p.2, L a⟫_ℝ : ℂ))) := by
    fun_prop
  have hiv : Integrable (Function.uncurry fun (x y : E) ↦
      cexp ((I : ℂ) * ((⟪x, T y⟫_ℝ : ℂ) + (⟪x, L b⟫_ℝ : ℂ) + (⟪y, L a⟫_ℝ : ℂ))))
      ((stdGaussian E).prod (stdGaussian E)) :=
    integrable_norm_le_one hcont.aestronglyMeasurable
      (fun p ↦ (gaussianCF_integrand_norm_one T L a b p).le)
  rw [gaussianBilinearCF, integral_integral hiv]
  exact integral_norm_le_one hcont.aestronglyMeasurable
    (fun p ↦ (gaussianCF_integrand_norm_one T L a b p).le)

theorem gaussianCF_twoCoordinateCompression
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T : Ω → (E →L[ℝ] E)) (L : Ω → (F →L[ℝ] E)) (hT : Measurable T) (hL : Measurable L)
    (a b : F) (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 1) :
    (∫ ω, ‖gaussianBilinearCF (T ω) (L ω)
        (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖ ∂ν ≤
      (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ *
        (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ)) ∧
      ((∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ *
        (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ) ≤
        max (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν)
          (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν)) := by
  classical

  have hjoint : ∀ (a' b' : F), Integrable
      (fun ω : Ω ↦ gaussianBilinearCF (T ω) (L ω) a' b') ν := by
    intro a' b'
    have hTp : Measurable fun q : Ω × (E × E) ↦ T q.1 := hT.comp measurable_fst
    have hLp : Measurable fun q : Ω × (E × E) ↦ L q.1 := hL.comp measurable_fst
    have hq1 : Measurable fun q : Ω × (E × E) ↦ (q.2.1 : E) :=
      measurable_fst.comp measurable_snd
    have hq2 : Measurable fun q : Ω × (E × E) ↦ (q.2.2 : E) :=
      measurable_snd.comp measurable_snd
    have hclm : Measurable fun z : (E →L[ℝ] E) × E ↦ z.1 z.2 :=
      (Continuous.clm_apply continuous_fst continuous_snd).measurable
    have hTe : Measurable fun q : Ω × (E × E) ↦ (T q.1) q.2.2 :=
      hclm.comp (Measurable.prodMk hTp hq2)
    have hLb : Measurable fun q : Ω × (E × E) ↦ (L q.1) b' :=
      ((Continuous.clm_apply continuous_id
        (continuous_const : Continuous fun _ : (F →L[ℝ] E) ↦ b')).measurable).comp hLp
    have hLa : Measurable fun q : Ω × (E × E) ↦ (L q.1) a' :=
      ((Continuous.clm_apply continuous_id
        (continuous_const : Continuous fun _ : (F →L[ℝ] E) ↦ a')).measurable).comp hLp
    have hinn : Measurable fun z : E × E ↦ ⟪z.1, z.2⟫_ℝ := continuous_inner.measurable
    have hi1 : Measurable fun q : Ω × (E × E) ↦ ⟪q.2.1, (T q.1) q.2.2⟫_ℝ :=
      hinn.comp (Measurable.prodMk hq1 hTe)
    have hi2 : Measurable fun q : Ω × (E × E) ↦ ⟪q.2.1, (L q.1) b'⟫_ℝ :=
      hinn.comp (Measurable.prodMk hq1 hLb)
    have hi3 : Measurable fun q : Ω × (E × E) ↦ ⟪q.2.2, (L q.1) a'⟫_ℝ :=
      hinn.comp (Measurable.prodMk hq2 hLa)
    have hcast : Measurable fun r : ℝ ↦ ((r : ℝ) : ℂ) := Complex.continuous_ofReal.measurable
    have hsum : Measurable fun q : Ω × (E × E) ↦
        ((⟪q.2.1, (T q.1) q.2.2⟫_ℝ : ℂ) + (⟪q.2.1, (L q.1) b'⟫_ℝ : ℂ)
          + (⟪q.2.2, (L q.1) a'⟫_ℝ : ℂ)) :=
      ((hcast.comp hi1).add (hcast.comp hi2)).add (hcast.comp hi3)
    have hGm : Measurable fun q : Ω × (E × E) ↦
        cexp ((I : ℂ) * ((⟪q.2.1, (T q.1) q.2.2⟫_ℝ : ℂ) + (⟪q.2.1, (L q.1) b'⟫_ℝ : ℂ)
          + (⟪q.2.2, (L q.1) a'⟫_ℝ : ℂ))) :=
      ((by fun_prop : Continuous fun z : ℂ ↦ cexp ((I : ℂ) * z)).measurable).comp hsum
    have hGint : Integrable (fun q : Ω × (E × E) ↦
        cexp ((I : ℂ) * ((⟪q.2.1, (T q.1) q.2.2⟫_ℝ : ℂ) + (⟪q.2.1, (L q.1) b'⟫_ℝ : ℂ)
          + (⟪q.2.2, (L q.1) a'⟫_ℝ : ℂ))))
        (ν.prod ((stdGaussian E).prod (stdGaussian E))) :=
      integrable_norm_le_one hGm.aestronglyMeasurable
        (fun q ↦ (gaussianCF_integrand_norm_one (T q.1) (L q.1) a' b' (q.2.1, q.2.2)).le)
    have hEq : ∀ ω : Ω, gaussianBilinearCF (T ω) (L ω) a' b'
        = ∫ p : E × E,
          cexp ((I : ℂ) * ((⟪p.1, T ω p.2⟫_ℝ : ℂ) + (⟪p.1, L ω b'⟫_ℝ : ℂ)
            + (⟪p.2, L ω a'⟫_ℝ : ℂ)))
          ∂((stdGaussian E).prod (stdGaussian E)) := by
      intro ω
      have hcont : Continuous fun p : E × E ↦
          cexp ((I : ℂ) * ((⟪p.1, T ω p.2⟫_ℝ : ℂ) + (⟪p.1, L ω b'⟫_ℝ : ℂ)
            + (⟪p.2, L ω a'⟫_ℝ : ℂ))) := by
        fun_prop
      have hivω : Integrable (Function.uncurry fun (x y : E) ↦
          cexp ((I : ℂ) * ((⟪x, T ω y⟫_ℝ : ℂ) + (⟪x, L ω b'⟫_ℝ : ℂ)
            + (⟪y, L ω a'⟫_ℝ : ℂ))))
          ((stdGaussian E).prod (stdGaussian E)) :=
        integrable_norm_le_one hcont.aestronglyMeasurable
          (fun p ↦ (gaussianCF_integrand_norm_one (T ω) (L ω) a' b' p).le)
      rw [gaussianBilinearCF, integral_integral hivω]
    exact hGint.integral_prod_left.congr (ae_of_all _ (fun ω ↦ (hEq ω).symm))

  have hXpos : ∀ ω : Ω, 0 < (gaussianBilinearCF (T ω) (L ω) a 0).re := fun ω ↦
    (gaussianCF_oneSidedQuadraticScaling (T ω) (L ω) a b).1
  have hYpos : ∀ ω : Ω, 0 < (gaussianBilinearCF (T ω) (L ω) 0 b).re := fun ω ↦
    (gaussianCF_oneSidedQuadraticScaling (T ω) (L ω) a b).2.1
  have hXle : ∀ ω : Ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ≤ 1 := fun ω ↦
    ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
      (gaussianBilinearCF_norm_le_one (T ω) (L ω) a 0)
  have hYle : ∀ ω : Ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ≤ 1 := fun ω ↦
    ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
      (gaussianBilinearCF_norm_le_one (T ω) (L ω) 0 b)
  have hXs : AEStronglyMeasurable (fun ω : Ω ↦ (gaussianBilinearCF (T ω) (L ω) a 0).re) ν :=
    Complex.continuous_re.comp_aestronglyMeasurable (hjoint a 0).aestronglyMeasurable
  have hYs : AEStronglyMeasurable (fun ω : Ω ↦ (gaussianBilinearCF (T ω) (L ω) 0 b).re) ν :=
    Complex.continuous_re.comp_aestronglyMeasurable (hjoint 0 b).aestronglyMeasurable
  have hXint : Integrable (fun ω : Ω ↦ (gaussianBilinearCF (T ω) (L ω) a 0).re) ν :=
    (integrable_const (1 : ℝ)).mono' hXs
      (ae_of_all _ (fun ω ↦ abs_le.mpr ⟨by linarith [hXpos ω], hXle ω⟩))
  have hYint : Integrable (fun ω : Ω ↦ (gaussianBilinearCF (T ω) (L ω) 0 b).re) ν :=
    (integrable_const (1 : ℝ)).mono' hYs
      (ae_of_all _ (fun ω ↦ abs_le.mpr ⟨by linarith [hYpos ω], hYle ω⟩))

  have hg2 : ∀ ω : Ω, ‖gaussianBilinearCF (T ω) (L ω) (Real.sqrt θ • a)
        (Real.sqrt (1 - θ) • b)‖
      = (gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
        * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ) :=
    fun ω ↦ gaussianCF_geometricInterpolation (T ω) (L ω) a b θ hθ₁ hθ₂
  have part1 : (∫ ω, ‖gaussianBilinearCF (T ω) (L ω)
        (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖ ∂ν ≤
      (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ *
        (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ)) := by
    by_cases hθ0 : θ = 0
    · subst hθ0
      have hg0 : ∀ ω : Ω, ‖gaussianBilinearCF (T ω) (L ω) 0 b‖
          = (gaussianBilinearCF (T ω) (L ω) 0 b).re := by
        intro ω
        have h2 := gaussianCF_geometricInterpolation (T ω) (L ω) a b 0 le_rfl (by norm_num)
        rw [show (1 : ℝ) - 0 = 1 from by norm_num, Real.sqrt_zero, zero_smul, Real.sqrt_one,
          one_smul, Real.rpow_zero, Real.rpow_one, one_mul] at h2
        exact h2
      rw [show (1 : ℝ) - 0 = 1 from by norm_num, Real.sqrt_zero, zero_smul, Real.sqrt_one,
        one_smul, integral_congr_ae (ae_of_all _ hg0), Real.rpow_zero, one_mul,
        Real.rpow_one]
    · by_cases hθ1 : θ = 1
      · subst hθ1
        have hg1v : ∀ ω : Ω, ‖gaussianBilinearCF (T ω) (L ω) a 0‖
            = (gaussianBilinearCF (T ω) (L ω) a 0).re := by
          intro ω
          have h2 := gaussianCF_geometricInterpolation (T ω) (L ω) a b 1 (by norm_num) le_rfl
          rw [show (1 : ℝ) - 1 = 0 from by ring, Real.sqrt_one, one_smul, Real.sqrt_zero,
            zero_smul, Real.rpow_one, Real.rpow_zero, mul_one] at h2
          exact h2
        rw [show (1 : ℝ) - 1 = 0 from by ring, Real.sqrt_one, one_smul, Real.sqrt_zero,
          zero_smul, integral_congr_ae (ae_of_all _ hg1v), Real.rpow_one, Real.rpow_zero,
          mul_one]
      · have hθ0' : 0 < θ := lt_of_le_of_ne hθ₁ (Ne.symm hθ0)
        have hθ1' : θ < 1 := lt_of_le_of_ne hθ₂ hθ1
        have h1θne : 1 - θ ≠ 0 := sub_ne_zero.mpr (by linarith)
        have hpq : (1 / θ).HolderConjugate (1 / (1 - θ)) :=
          ⟨by field_simp; ring, one_div_pos.mpr hθ0', one_div_pos.mpr (by linarith)⟩
        have hXθs : AEStronglyMeasurable (fun ω : Ω ↦
            (gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ) ν :=
          (Real.continuous_rpow_const hθ₁).comp_aestronglyMeasurable hXs
        have hYθs : AEStronglyMeasurable (fun ω : Ω ↦
            (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) ν :=
          (Real.continuous_rpow_const (by linarith)).comp_aestronglyMeasurable hYs
        have hSM : AEStronglyMeasurable (fun ω : Ω ↦
            (gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
            * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) ν := hXθs.mul hYθs
        have hnn : ∀ ω : Ω, 0 ≤ (gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
            * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ) := fun ω ↦
          mul_nonneg (Real.rpow_nonneg (hXpos ω).le θ) (Real.rpow_nonneg (hYpos ω).le _)
        have hmul : ∀ ω : Ω, ((ENNReal.ofReal
              ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ) : ℝ≥0∞)) *
              ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ))
            = ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
              * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) :=
          fun ω ↦ (ENNReal.ofReal_mul (Real.rpow_nonneg (hXpos ω).le θ)).symm
        have hFp : ∀ ω : Ω, ((ENNReal.ofReal
              ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ) : ℝ≥0∞)) ^ (1 / θ)
            = ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) a 0).re) := by
          intro ω
          have hXnn : 0 ≤ (gaussianBilinearCF (T ω) (L ω) a 0).re := (hXpos ω).le
          have hxnn : 0 ≤ (gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ :=
            Real.rpow_nonneg hXnn θ
          rw [ENNReal.ofReal_rpow_of_nonneg hxnn (one_div_nonneg.mpr (le_of_lt hθ0')),
            ← Real.rpow_mul hXnn, show θ * (1 / θ) = 1 from by field_simp, Real.rpow_one]
        have hGq : ∀ ω : Ω, ((ENNReal.ofReal
              ((gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) : ℝ≥0∞)) ^ (1 / (1 - θ))
            = ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) 0 b).re) := by
          intro ω
          have hYnn : 0 ≤ (gaussianBilinearCF (T ω) (L ω) 0 b).re := (hYpos ω).le
          have hynn : 0 ≤ (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ) :=
            Real.rpow_nonneg hYnn _
          rw [ENNReal.ofReal_rpow_of_nonneg hynn (one_div_nonneg.mpr (by linarith)),
            ← Real.rpow_mul hYnn, show (1 - θ) * (1 / (1 - θ)) = 1 from by field_simp,
            Real.rpow_one]
        have hchain : (∫⁻ ω, ENNReal.ofReal
              ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
              * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) ∂ν)
            ≤ (∫⁻ ω, ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) a 0).re) ∂ν) ^ θ
              * (∫⁻ ω, ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) 0 b).re) ∂ν)
                ^ (1 - θ) := by
          calc (∫⁻ ω, ENNReal.ofReal
                ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
                * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) ∂ν)
              = (∫⁻ ω, (ENNReal.ofReal
                  ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ) : ℝ≥0∞)
                * ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) ∂ν) :=
                lintegral_congr_ae (ae_of_all _ (fun ω ↦ (hmul ω).symm))
            _ ≤ (∫⁻ ω, (ENNReal.ofReal
                  ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ) : ℝ≥0∞) ^ (1 / θ) ∂ν)
                ^ (1 / (1 / θ))
              * (∫⁻ ω, (ENNReal.ofReal
                  ((gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) : ℝ≥0∞)
                ^ (1 / (1 - θ)) ∂ν) ^ (1 / (1 / (1 - θ))) :=
                ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq
                  ((aestronglyMeasurable_iff_aemeasurable.mp hXθs).ennreal_ofReal)
                  ((aestronglyMeasurable_iff_aemeasurable.mp hYθs).ennreal_ofReal)
            _ = (∫⁻ ω, ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) a 0).re) ∂ν) ^ θ
                * (∫⁻ ω, ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) 0 b).re) ∂ν)
                  ^ (1 - θ) := by
                rw [lintegral_congr_ae (ae_of_all _ hFp),
                  lintegral_congr_ae (ae_of_all _ hGq),
                  show (1 : ℝ) / (1 / θ) = θ from by field_simp,
                  show (1 : ℝ) / (1 / (1 - θ)) = 1 - θ from by field_simp]
        have hIX : 0 ≤ ∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν :=
          integral_nonneg (fun ω ↦ (hXpos ω).le)
        have hIY : 0 ≤ ∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν :=
          integral_nonneg (fun ω ↦ (hYpos ω).le)
        rw [show (∫⁻ ω, ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) a 0).re) ∂ν)
              = ENNReal.ofReal (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) from
              (ofReal_integral_eq_lintegral_ofReal hXint (ae_of_all _ (fun ω ↦ (hXpos ω).le))).symm,
            show (∫⁻ ω, ENNReal.ofReal ((gaussianBilinearCF (T ω) (L ω) 0 b).re) ∂ν)
              = ENNReal.ofReal (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) from
              (ofReal_integral_eq_lintegral_ofReal hYint (ae_of_all _ (fun ω ↦ (hYpos ω).le))).symm,
            ENNReal.ofReal_rpow_of_nonneg hIX hθ₁,
            ENNReal.ofReal_rpow_of_nonneg hIY (by linarith),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hIX θ)] at hchain
        have hnetop : (∫⁻ ω, ENNReal.ofReal
              ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
              * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) ∂ν) ≠ ⊤ := by
          intro h
          rw [h] at hchain
          exact absurd (top_le_iff.mp hchain) ENNReal.ofReal_ne_top
        rw [integral_congr_ae (ae_of_all _ hg2),
          integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hSM]
        have hIYnn : 0 ≤ ∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν :=
          integral_nonneg (fun ω ↦ (hYpos ω).le)
        calc ((∫⁻ ω, ENNReal.ofReal
                ((gaussianBilinearCF (T ω) (L ω) a 0).re ^ θ
                * (gaussianBilinearCF (T ω) (L ω) 0 b).re ^ (1 - θ)) ∂ν)).toReal
            ≤ ((ENNReal.ofReal ((∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ
              * (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ)) : ℝ≥0∞)).toReal :=
              (ENNReal.toReal_le_toReal hnetop ENNReal.ofReal_ne_top).mpr hchain
          _ = (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ
              * (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ) :=
              ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg
                (integral_nonneg (fun ω ↦ (hXpos ω).le)) θ) (Real.rpow_nonneg hIYnn _))

  have part2 : ((∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ
        * (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ) ≤
      max (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν)
        (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν)) := by
    have hXnn : 0 ≤ ∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν :=
      integral_nonneg (fun ω ↦ (hXpos ω).le)
    have hYnn : 0 ≤ ∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν :=
      integral_nonneg (fun ω ↦ (hYpos ω).le)
    have hmax : 0 ≤ max (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν)
        (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) :=
      le_trans hXnn (le_max_left _ _)
    calc (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ
          * (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ)
        ≤ (max (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν)
            (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν)) ^ θ
          * (max (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν)
            (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν)) ^ (1 - θ) :=
          mul_le_mul (Real.rpow_le_rpow hXnn (le_max_left _ _) hθ₁)
            (Real.rpow_le_rpow hYnn (le_max_right _ _) (by linarith))
            (Real.rpow_nonneg hYnn _) (Real.rpow_nonneg hmax _)
      _ = max (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν)
          (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) := by
          rw [← Real.rpow_add_of_nonneg hmax hθ₁ (by linarith),
            show θ + (1 - θ) = 1 from by ring, Real.rpow_one]
  exact ⟨part1, part2⟩

private theorem norm_cexp_imag_one (r : ℝ) : ‖cexp (r * I)‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : ((r : ℂ) * I).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [hre, Real.exp_zero]

private theorem charFun_norm_le_one (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    ‖charFun μ t‖ ≤ 1 := by
  rw [charFun_apply]
  exact integral_norm_le_one (Continuous.aestronglyMeasurable (by fun_prop))
    (fun x ↦ (norm_cexp_imag_one (⟪x, t⟫_ℝ)).le)

private theorem exists_symmetric_sqrt_quad (T : E →L[ℝ] E)
    (hTsym : (T.toLinearMap).IsSymmetric) (hTpsd : ∀ x : E, 0 ≤ ⟪x, T x⟫_ℝ) :
    ∃ B : E →L[ℝ] E, (∀ x y : E, ⟪B x, y⟫_ℝ = ⟪B y, x⟫_ℝ) ∧
      (∀ x : E, ‖B x‖ ^ 2 = ⟪x, T x⟫_ℝ) := by
  classical
  set n := Module.finrank ℝ E with hn
  set e := hTsym.eigenvectorBasis rfl with he
  set ev := hTsym.eigenvalues rfl with hev
  have hon : ∀ i j : Fin n, ⟪e i, e j⟫_ℝ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have heig : ∀ i : Fin n, T (e i) = ↑(ev i) • e i := fun i ↦ hTsym.apply_eigenvectorBasis rfl i
  have hpos : ∀ i : Fin n, 0 ≤ ev i := by
    intro i
    have h2 : ⟪e i, T (e i)⟫_ℝ = ev i := by
      rw [heig, real_inner_smul_right, hon i i, if_pos rfl, mul_one]
    rw [← h2]; exact hTpsd _
  have hcoe : ∀ x : E, ∀ i : Fin n, (e.toBasis.repr x) i = ⟪e i, x⟫_ℝ := fun x i ↦
    (OrthonormalBasis.coe_toBasis_repr_apply e x i).trans (OrthonormalBasis.repr_apply_apply e x i)
  have hxsum : ∀ x : E, ∑ i, (e.toBasis.repr x) i • (e.toBasis i : E) = x := fun x ↦
    Module.Basis.sum_repr e.toBasis x
  have hLT : (e.toBasis.constr ℝ fun i ↦ (ev i) • e i) = T.toLinearMap := by
    refine Module.Basis.ext e.toBasis fun i ↦ ?_
    rw [Module.Basis.constr_basis]
    exact (heig i).symm
  have heig' : ∀ i : Fin n, T ((e.toBasis i : E)) = ↑(ev i) • e i := fun i ↦ heig i
  have hTexp : ∀ x : E, T x = ∑ i, (⟪e i, x⟫_ℝ) • ((ev i) • e i) := by
    intro x
    calc T x = T (∑ i, (e.toBasis.repr x) i • (e.toBasis i : E)) := by rw [hxsum x]
      _ = ∑ i, (e.toBasis.repr x) i • T (e.toBasis i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
      _ = ∑ i, (⟪e i, x⟫_ℝ) • ((ev i) • e i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [heig' i, hcoe x i]
  set B : E →L[ℝ] E :=
    (e.toBasis.constr ℝ fun i ↦ (Real.sqrt (ev i)) • e i).toContinuousLinearMap with hBdef
  have hBbasis : ∀ i : Fin n, B ((e.toBasis i : E)) = (Real.sqrt (ev i)) • e i := by
    intro i
    have h1 : B ((e.toBasis i : E))
        = (e.toBasis.constr ℝ fun i ↦ (Real.sqrt (ev i)) • e i) (e.toBasis i) := rfl
    rw [h1, Module.Basis.constr_basis]
  have hBexp : ∀ x : E, B x = ∑ i, (⟪e i, x⟫_ℝ) • ((Real.sqrt (ev i)) • e i) := by
    intro x
    calc B x = B (∑ i, (e.toBasis.repr x) i • (e.toBasis i : E)) := by rw [hxsum x]
      _ = ∑ i, (e.toBasis.repr x) i • B (e.toBasis i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
      _ = ∑ i, (⟪e i, x⟫_ℝ) • ((Real.sqrt (ev i)) • e i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hBbasis i, hcoe x i]
  have hpair : ∀ x y : E, ⟪B x, y⟫_ℝ
      = ∑ i, (Real.sqrt (ev i)) * (⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ) := by
    intro x y
    rw [hBexp x, sum_inner]
    simp only [real_inner_smul_left]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  refine ⟨B, ?_, ?_⟩
  · intro x y
    rw [hpair x y, hpair y x]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  · intro x
    have hcoef : ∀ i : Fin n, ⟪e i, B x⟫_ℝ = (Real.sqrt (ev i)) * ⟪e i, x⟫_ℝ := by
      intro i
      rw [hBexp x]
      have hsum : ∑ j, (⟪e j, x⟫_ℝ) • ((Real.sqrt (ev j)) • e j)
          = ∑ j, ((⟪e j, x⟫_ℝ) * Real.sqrt (ev j)) • e j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [smul_smul]
      rw [hsum, e.orthonormal.inner_right_fintype _ i]
      ring
    have hqB : ‖B x‖ ^ 2 = ∑ i, (ev i) * (⟪e i, x⟫_ℝ) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hpair x (B x)]
      simp only [hcoef]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hc : 0 ≤ ev i := hpos i
      calc Real.sqrt (ev i) * (⟪e i, x⟫_ℝ * (Real.sqrt (ev i) * ⟪e i, x⟫_ℝ))
          = Real.sqrt (ev i) * (Real.sqrt (ev i) * (⟪e i, x⟫_ℝ * ⟪e i, x⟫_ℝ)) := by ring
        _ = ev i * (⟪e i, x⟫_ℝ * ⟪e i, x⟫_ℝ) := by rw [← mul_assoc, Real.mul_self_sqrt hc]
        _ = ev i * (⟪e i, x⟫_ℝ) ^ 2 := by rw [← sq]
    have hqT : ⟪x, T x⟫_ℝ = ∑ i, (ev i) * (⟪e i, x⟫_ℝ) ^ 2 := by
      rw [hTexp x, inner_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [real_inner_smul_right, real_inner_comm]
      ring
    rw [hqB, hqT]

private theorem laplace_eq_charFun_re (Q B : E →L[ℝ] E)
    (hBsymm : ∀ x y : E, ⟪B x, y⟫_ℝ = ⟪B y, x⟫_ℝ)
    (hquad : ∀ x : E, ⟪x, Q x⟫_ℝ = ‖B x‖ ^ 2 / 2)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    Integrable (fun z ↦ (charFun μ (B z)).re) (stdGaussian E) ∧
      ∫ x, Real.exp (-⟪x, Q x⟫_ℝ) ∂μ = ∫ z, (charFun μ (B z)).re ∂(stdGaussian E) := by
  classical
  have hkey : ∀ r : ℝ, (cexp (-(↑r : ℂ) ^ 2 / 2)).re = Real.exp (-r ^ 2 / 2) := by
    intro r
    have h1 : -(↑r : ℂ) ^ 2 / 2 = ((-(r ^ 2 / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.exp_ofReal_re]
    congr 1
    ring
  have hpt : ∀ x : E, Real.exp (-⟪x, Q x⟫_ℝ) = (charFun (stdGaussian E) (B x)).re := by
    intro x
    rw [charFun_stdGaussian, hkey]
    congr 1
    linarith [hquad x]
  have hintCx : ∀ x : E, Integrable (fun z ↦ cexp (⟪z, B x⟫_ℝ * I)) (stdGaussian E) :=
    fun x ↦ integrable_norm_le_one (Continuous.aestronglyMeasurable (by fun_prop))
      (fun z ↦ (norm_cexp_imag_one _).le)
  have hintCz : ∀ z : E, Integrable (fun x ↦ cexp (⟪x, B z⟫_ℝ * I)) μ :=
    fun z ↦ integrable_norm_le_one (Continuous.aestronglyMeasurable (by fun_prop))
      (fun x ↦ (norm_cexp_imag_one _).le)
  have hinner : ∀ z : E, (∫ x, (cexp (⟪z, B x⟫_ℝ * I)).re ∂μ) = (charFun μ (B z)).re := by
    intro z
    rw [integral_congr_ae (ae_of_all _ (fun x ↦ by
      show (cexp (⟪z, B x⟫_ℝ * I)).re = (cexp (⟪x, B z⟫_ℝ * I)).re
      have hswap : ⟪z, B x⟫_ℝ = ⟪x, B z⟫_ℝ :=
        (real_inner_comm (B x) z).trans ((hBsymm x z).trans (real_inner_comm x (B z)))
      rw [hswap]))]
    have h2 : (∫ x, (cexp (⟪x, B z⟫_ℝ * I)).re ∂μ)
        = ((∫ x, cexp (⟪x, B z⟫_ℝ * I) ∂μ)).re := integral_re (hintCz z)
    rw [h2, charFun_apply]
  have hcont : Continuous fun q : E × E ↦ (cexp (⟪q.2, B q.1⟫_ℝ * I)).re := by fun_prop
  have hint : Integrable (fun q : E × E ↦ (cexp (⟪q.2, B q.1⟫_ℝ * I)).re)
      (μ.prod (stdGaussian E)) :=
    (integrable_const (1 : ℝ)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ (fun q ↦ by
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm _).trans (le_of_eq (norm_cexp_imag_one _))))
  refine ⟨?_, ?_⟩
  · rw [show (fun z : E ↦ (charFun μ (B z)).re)
        = fun z ↦ ∫ x, (cexp (⟪z, B x⟫_ℝ * I)).re ∂μ from funext fun z ↦ (hinner z).symm]
    exact hint.integral_prod_right
  · calc ∫ x, Real.exp (-⟪x, Q x⟫_ℝ) ∂μ
        = ∫ x, ∫ z, (cexp (⟪z, B x⟫_ℝ * I)).re ∂(stdGaussian E) ∂μ := by
          refine integral_congr_ae (ae_of_all _ (fun x ↦ ?_))
          show Real.exp (-⟪x, Q x⟫_ℝ)
            = ∫ z, (cexp (⟪z, B x⟫_ℝ * I)).re ∂(stdGaussian E)
          rw [hpt x, charFun_apply]
          exact (integral_re (hintCx x)).symm
      _ = ∫ z, ∫ x, (cexp (⟪z, B x⟫_ℝ * I)).re ∂μ ∂(stdGaussian E) :=
          integral_integral_swap hint
      _ = ∫ z, (charFun μ (B z)).re ∂(stdGaussian E) :=
          integral_congr_ae (ae_of_all _ (fun z ↦ hinner z))

theorem fourier_to_laplace (μX μY : Measure E) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (h : ∀ t : E, (charFun μX t).re ≤ (charFun μY t).re) :
    matrixLaplaceLE μY μX := by
  intro Q hQ
  set T : E →L[ℝ] E := Q + Q.adjoint with hT
  have hTsym : (T.toLinearMap).IsSymmetric := by
    intro x y
    show ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ
    simp only [hT, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    ring
  have hTquad : ∀ x : E, ⟪x, T x⟫_ℝ = ⟪x, Q x⟫_ℝ + ⟪x, Q x⟫_ℝ := by
    intro x
    have h1 : ⟪x, T x⟫_ℝ = ⟪x, Q x⟫_ℝ + ⟪Q x, x⟫_ℝ := by
      simp only [hT, ContinuousLinearMap.add_apply, inner_add_right,
        ContinuousLinearMap.adjoint_inner_right]
    rw [h1, real_inner_comm (Q x) x]
  have hTpsd : ∀ x : E, 0 ≤ ⟪x, T x⟫_ℝ := by
    intro x
    rw [hTquad x]
    linarith [hQ x]
  obtain ⟨B, hBsymm, hBq⟩ := exists_symmetric_sqrt_quad T hTsym hTpsd
  have hquad : ∀ x : E, ⟪x, Q x⟫_ℝ = ‖B x‖ ^ 2 / 2 := by
    intro x
    have h1 : ‖B x‖ ^ 2 = ⟪x, Q x⟫_ℝ + ⟪x, Q x⟫_ℝ := by
      rw [hBq x, hTquad x]
    linarith
  obtain ⟨hintX, hIX⟩ := laplace_eq_charFun_re Q B hBsymm hquad μX
  obtain ⟨hintY, hIY⟩ := laplace_eq_charFun_re Q B hBsymm hquad μY
  rw [hIY, hIX]
  exact integral_mono hintX hintY (fun z ↦ h (B z))

end Qatlib.Concepts.BosonFock.PermAnalysis
