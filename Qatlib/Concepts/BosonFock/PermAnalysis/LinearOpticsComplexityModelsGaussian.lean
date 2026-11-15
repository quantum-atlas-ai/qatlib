/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs
public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift
public import Qatlib.Foundations.ComplexGeometry.PhaseRecovery.TriangulationStabilityThec
public import Qatlib.Foundations.ProbabilityCore.Concentration.GaussianShiftTVDBoundThec
public import Qatlib.Concepts.BosonFock.PermAnalysis.BosonDistributionNormalizationThec
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Algebra.Order.Chebyshev
public import Qatlib.Concepts.BosonFock.PermAnalysis.LinearOpticsComplexityModelsPermanent

@[expose] public section
open Qatlib.Concepts.BosonFock.PermAnalysis
open Qatlib.Concepts.CountingClasses.ClassTransport

set_option autoImplicit false

open Qatlib

open scoped BigOperators Nat ComplexConjugate Matrix

open Module MeasureTheory

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib.Foundations.ComplexGeometry.PhaseRecovery Qatlib.Foundations.ProbabilityCore.Concentration
open MeasureTheory
open scoped Classical
set_option maxHeartbeats 2000000
/-- The actual standard complex density, retained in primitive form for local unfolding. -/
private noncomputable def g17gauss (z : ℂ) : ℝ := Real.pi⁻¹ * Real.exp (-Complex.normSq z)

/-- The shared actual complex Gaussian density is nonnegative. -/
private theorem g17gauss_nonneg (z : ℂ) : 0 ≤ g17gauss z :=
  Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.nonneg z

/-- The shared actual complex Gaussian density has integral one. -/
private theorem g17gauss_integral : (∫ z : ℂ, g17gauss z) = 1 :=
  Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.mass

/-- The actual product Gaussian translation bound is supplied by the shared mathematical layer. -/
theorem clause17_clause4a : ∀ (N : ℕ) (v : Fin N → ℂ),
    (1 / 2) * ∫ x : Fin N → ℂ,
        |∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i - v i))))
          - ∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i))))|
      ∂MeasureTheory.volume
    ≤ Real.sqrt (∑ i, Complex.normSq (v i)) :=
  Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.shiftBound

/-- The first moment of the unnormalized real Gaussian vanishes. -/
private theorem clause17_1d_odd : (∫ x : ℝ, x * Real.exp (-(x ^ 2 : ℝ))) = 0 := by
  have hIoi : (∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-(x ^ 2 : ℝ))) = 1 / 2 := by
    have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := 1) (by norm_num) (by norm_num)
    have hgr : ∀ x ∈ (Set.Ioi (0 : ℝ)), x * Real.exp (-(x ^ 2 : ℝ))
        = (x : ℝ) ^ (1 : ℝ) * Real.exp (-((x : ℝ) ^ (2 : ℝ))) := by
      intro x _hx
      rw [Real.rpow_one, Real.rpow_two]
    rw [setIntegral_congr_fun measurableSet_Ioi hgr]
    have hG : ((1 : ℝ) / 2) * Real.Gamma ((1 + 1) / 2) = 1 / 2 := by
      rw [show (1 + 1 : ℝ) / 2 = 1 by norm_num]
      simp
    exact h.trans hG
  have hIic : (∫ x in Set.Iic (0 : ℝ), x * Real.exp (-(x ^ 2 : ℝ))) = -(1 / 2) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun x => x * Real.exp (-(x ^ 2 : ℝ)))
    have hL : (fun x : ℝ => (fun x => x * Real.exp (-(x ^ 2 : ℝ))) (-x))
        = fun x => -(x * Real.exp (-(x ^ 2 : ℝ))) := by
      funext x
      simp only [neg_mul]
      congr 1
      rw [neg_sq]
    rw [hL, integral_neg] at h
    simp only [neg_zero] at h
    rw [hIoi] at h
    linarith
  have hfi : Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2 : ℝ))) := by
    have := integrable_mul_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num)
    simpa [neg_one_mul] using this
  have hcomp := integral_add_compl (s := Set.Iic (0:ℝ)) (hs := measurableSet_Iic)
    (f := fun x : ℝ => x * Real.exp (-(x ^ 2 : ℝ))) hfi
  rw [Set.compl_Iic, hIic, hIoi] at hcomp
  linarith

/-- The squared-norm moment of `g17gauss` is one. -/
private theorem g17gauss_second_moment : (∫ z : ℂ, Complex.normSq z * g17gauss z) = 1 := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2) (by norm_num) (by norm_num)
  have hG2 : Real.Gamma 2 = 1 := by simp
  have hG : ((2 * Real.pi / 2) * Real.Gamma ((2 + 2) / 2) : ℝ) = Real.pi := by
    rw [show ((2 + 2) / 2 : ℝ) = 2 by norm_num, hG2]
    ring
  have hconst : (fun z : ℂ => Complex.normSq z * g17gauss z)
      = fun z => Real.pi⁻¹ * (Complex.normSq z * Real.exp (-Complex.normSq z)) := by
    funext z
    simp only [g17gauss]
    ring
  rw [hconst, integral_const_mul]
  have hz2 : (∫ z : ℂ, Complex.normSq z * Real.exp (-Complex.normSq z))
      = ∫ z : ℂ, ‖z‖ ^ (2:ℝ) * Real.exp (-‖z‖ ^ (2:ℝ)) := by
    congr 1
    funext z
    simp only [Complex.normSq_eq_norm_sq]
    rw [← Real.rpow_two (‖z‖)]
  rw [hz2, h, hG]
  exact inv_mul_cancel₀ Real.pi_pos.ne'

/-- The real-coordinate first moment of `g17gauss` vanishes. -/
private theorem g17gauss_re_moment : (∫ z : ℂ, z.re * g17gauss z) = 0 := by
  let g := fun p : ℝ × ℝ => (p.1 * Real.pi⁻¹ * Real.exp (-p.1 ^ 2)) * Real.exp (-p.2 ^ 2)
  have hf (z : ℂ) : z.re * g17gauss z = g (Complex.measurableEquivRealProd z) := by
    simp only [g17gauss, g, Complex.measurableEquivRealProd_apply, Complex.normSq_apply,
      neg_add, Real.exp_add, pow_two]
    ring
  have he := Complex.volume_preserving_equiv_real_prod.integral_comp' g
  simp_rw [hf]
  rw [he]
  change (∫ y : ℝ × ℝ, g y ∂(volume : Measure ℝ).prod (volume : Measure ℝ)) = 0
  dsimp [g]
  rw [integral_prod_mul (fun x : ℝ => x * Real.pi⁻¹ * Real.exp (-x ^ 2))
      (fun y : ℝ => Real.exp (-y ^ 2))]
  have hx : (∫ x : ℝ, x * Real.pi⁻¹ * Real.exp (-x ^ 2)) = 0 := by
    have h1 : (fun x : ℝ => x * Real.pi⁻¹ * Real.exp (-x ^ 2))
        = fun x => Real.pi⁻¹ * (x * Real.exp (-x ^ 2)) := by
      funext x
      ring
    rw [h1, integral_const_mul, clause17_1d_odd, mul_zero]
  rw [hx, zero_mul]

/-- The imaginary-coordinate first moment of `g17gauss` vanishes. -/
private theorem g17gauss_im_moment : (∫ z : ℂ, z.im * g17gauss z) = 0 := by
  let g := fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * (p.2 * Real.pi⁻¹ * Real.exp (-p.2 ^ 2))
  have hf (z : ℂ) : z.im * g17gauss z = g (Complex.measurableEquivRealProd z) := by
    simp only [g17gauss, g, Complex.measurableEquivRealProd_apply, Complex.normSq_apply,
      neg_add, Real.exp_add, pow_two]
    ring
  have he := Complex.volume_preserving_equiv_real_prod.integral_comp' g
  simp_rw [hf]
  rw [he]
  change (∫ y : ℝ × ℝ, g y ∂(volume : Measure ℝ).prod (volume : Measure ℝ)) = 0
  dsimp [g]
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2))
      (fun y : ℝ => y * Real.pi⁻¹ * Real.exp (-y ^ 2))]
  have hy : (∫ y : ℝ, y * Real.pi⁻¹ * Real.exp (-y ^ 2)) = 0 := by
    have h1 : (fun y : ℝ => y * Real.pi⁻¹ * Real.exp (-y ^ 2))
        = fun y => Real.pi⁻¹ * (y * Real.exp (-y ^ 2)) := by
      funext y
      ring
    rw [h1, integral_const_mul, clause17_1d_odd, mul_zero]
  rw [hy, mul_zero]

/-- The Gaussian density `g17gauss` is continuous. -/
private theorem g17gauss_continuous : Continuous g17gauss := by
  unfold g17gauss
  fun_prop

/-- The Gaussian density `g17gauss` is integrable. -/
private theorem g17gauss_integrable : Integrable g17gauss :=
  Integrable.of_integral_ne_zero (by rw [g17gauss_integral]; norm_num)

/-- The complex norm multiplied by the unnormalized Gaussian kernel is integrable. -/
private theorem g17gauss_norm_kernel_integrable :
    Integrable (fun z : ℂ => ‖z‖ * Real.exp (-Complex.normSq z)) := by
  have hne : (∫ z : ℂ, ‖z‖ * Real.exp (-Complex.normSq z)) ≠ 0 := by
    have h1 : (fun z : ℂ => ‖z‖ * Real.exp (-Complex.normSq z))
        = fun z => ‖z‖ ^ (1:ℝ) * Real.exp (-‖z‖ ^ (2:ℝ)) := by
      funext z
      rw [Complex.normSq_eq_norm_sq, Real.rpow_one, ← Real.rpow_two (‖z‖)]
    rw [h1, Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 1) (by norm_num) (by norm_num)]
    have h3 : ((2 * Real.pi / 2) * Real.Gamma ((1 + 2) / 2) : ℝ) ≠ 0 := by
      rw [show ((1 + 2) / 2 : ℝ) = 1 / 2 + 1 by ring,
        Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0)]
      positivity
    exact h3
  exact Integrable.of_integral_ne_zero hne

/-- The real coordinate multiplied by `g17gauss` is integrable. -/
private theorem g17gauss_re_integrable : Integrable (fun z : ℂ => z.re * g17gauss z) := by
  have hg : Integrable (fun z : ℂ => ‖z‖ * g17gauss z) := by
    have h2 : (fun z : ℂ => ‖z‖ * g17gauss z)
        = fun z => Real.pi⁻¹ * (‖z‖ * Real.exp (-Complex.normSq z)) := by
      funext z
      simp only [g17gauss]
      ring
    rw [h2]
    exact g17gauss_norm_kernel_integrable.const_mul _
  have hcont : Continuous (fun z : ℂ => z.re * g17gauss z) :=
    Continuous.mul Complex.continuous_re g17gauss_continuous
  refine Integrable.mono hg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hnn : 0 ≤ g17gauss z := by
    unfold g17gauss
    positivity
  have hle : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg z) hnn)]
  exact mul_le_mul_of_nonneg_right hle hnn

/-- The imaginary coordinate multiplied by `g17gauss` is integrable. -/
private theorem g17gauss_im_integrable : Integrable (fun z : ℂ => z.im * g17gauss z) := by
  have hg : Integrable (fun z : ℂ => ‖z‖ * g17gauss z) := by
    have h2 : (fun z : ℂ => ‖z‖ * g17gauss z)
        = fun z => Real.pi⁻¹ * (‖z‖ * Real.exp (-Complex.normSq z)) := by
      funext z
      simp only [g17gauss]
      ring
    rw [h2]
    exact g17gauss_norm_kernel_integrable.const_mul _
  have hcont : Continuous (fun z : ℂ => z.im * g17gauss z) :=
    Continuous.mul Complex.continuous_im g17gauss_continuous
  refine Integrable.mono hg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hnn : 0 ≤ g17gauss z := by
    unfold g17gauss
    positivity
  have hle : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg z) hnn)]
  exact mul_le_mul_of_nonneg_right hle hnn

/-- The Gaussian average of the squared norm of the translated variable is the squared norm of
`v` plus one. -/
private theorem g17gauss_shift_moment (v : ℂ) :
    (∫ z : ℂ, Complex.normSq (v + z) * g17gauss z) = Complex.normSq v + 1 := by
  have hexp : ∀ z : ℂ, Complex.normSq (v + z) = Complex.normSq v + Complex.normSq z
      + (2 * v.re * z.re + 2 * v.im * z.im) := by
    intro z
    rw [Complex.normSq_add]
    have hre : ((v * conj z) : ℂ).re = v.re * z.re + v.im * z.im := by
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hre]
    ring
  have hfun : (fun z : ℂ => Complex.normSq (v + z) * g17gauss z)
      = fun z => (Complex.normSq v * g17gauss z + Complex.normSq z * g17gauss z)
          + (2 * v.re * (z.re * g17gauss z) + 2 * v.im * (z.im * g17gauss z)) := by
    funext z
    rw [hexp]
    ring
  rw [hfun]
  have hfi1 : Integrable (fun z : ℂ => Complex.normSq v * g17gauss z) :=
    g17gauss_integrable.const_mul _
  have hfi2 : Integrable (fun z : ℂ => Complex.normSq z * g17gauss z) :=
    Integrable.of_integral_ne_zero (by rw [g17gauss_second_moment]; norm_num)
  have hfi3 : Integrable (fun z : ℂ => 2 * v.re * (z.re * g17gauss z)) :=
    g17gauss_re_integrable.const_mul _
  have hfi4 : Integrable (fun z : ℂ => 2 * v.im * (z.im * g17gauss z)) :=
    g17gauss_im_integrable.const_mul _
  have hAB := integral_add (f := fun z : ℂ => Complex.normSq v * g17gauss z)
    (g := fun z : ℂ => Complex.normSq z * g17gauss z) hfi1 hfi2
  have hCD := integral_add (f := fun z : ℂ => 2 * v.re * (z.re * g17gauss z))
    (g := fun z : ℂ => 2 * v.im * (z.im * g17gauss z)) hfi3 hfi4
  have hABCD := integral_add
    (f := fun z : ℂ => Complex.normSq v * g17gauss z + Complex.normSq z * g17gauss z)
    (g := fun z : ℂ => 2 * v.re * (z.re * g17gauss z) + 2 * v.im * (z.im * g17gauss z))
    (hfi1.add hfi2) (hfi3.add hfi4)
  rw [hABCD, hAB, hCD]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have h2' : (∫ a : ℂ, (fun z => Complex.normSq z * g17gauss z) a) = 1 := by
    simpa using g17gauss_second_moment
  rw [g17gauss_integral, h2', g17gauss_re_moment, g17gauss_im_moment]
  ring

/-- The squared norm of a finite product of complex numbers is the product of their squared
norms. -/
private theorem clause17_normSq_prod {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    Complex.normSq (∏ i, f i) = ∏ i, Complex.normSq (f i) :=
  map_prod ({ toFun := Complex.normSq, map_one' := Complex.normSq_one, map_mul' := Complex.normSq_mul } : ℂ →* ℝ) f Finset.univ

/-- Integrating a function of one coordinate against the product Gaussian reduces to its
integral against the single-coordinate Gaussian. -/
private theorem clause17_integral_pi_special {n : ℕ} (k : Fin n) (u : ℂ → ℝ) :
    (∫ y : Fin n → ℂ, u (y k) * ∏ j, g17gauss (y j))
      = ∫ z : ℂ, u z * g17gauss z := by
  set f : Fin n → ℂ → ℝ := fun j z => if j = k then u z * g17gauss z else g17gauss z with hfdef
  have hprod : ∀ y : Fin n → ℂ, u (y k) * ∏ j, g17gauss (y j) = ∏ j, f j (y j) := by
    intro y
    have h1 : ∏ j, f j (y j) = (u (y k) * g17gauss (y k))
        * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase k, g17gauss (y j) := by
      rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => f j (y j)) (a := k) (Finset.mem_univ k)]
      congr 1
      · simp only [hfdef]
        simp
      · refine Finset.prod_congr rfl fun j hj => ?_
        have hjk : j ≠ k := by simpa using hj
        simp only [hfdef]
        rw [ite_eq_right hjk]
    have h2 : u (y k) * ∏ j, g17gauss (y j)
        = (u (y k) * g17gauss (y k))
          * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase k, g17gauss (y j) := by
      rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => g17gauss (y j)) (a := k) (Finset.mem_univ k)]
      ring
    rw [h2, h1]
  have hrew : (fun y : Fin n → ℂ => u (y k) * ∏ j, g17gauss (y j))
      = (fun y => ∏ j, f j (y j)) := by
    funext y
    exact hprod y
  rw [hrew, integral_fintype_prod_volume_eq_prod (f := f)]
  have hsz : ∀ j : Fin n, (∫ z : ℂ, f j z) = if j = k then ∫ z, u z * g17gauss z
      else ∫ z : ℂ, g17gauss z := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [hfdef]
      simp
    · have h1 : (if j = k then ∫ z : ℂ, u z * g17gauss z else ∫ z : ℂ, g17gauss z)
          = ∫ z : ℂ, g17gauss z := ite_eq_right hj
      rw [h1]
      simp only [hfdef, ite_eq_right hj]
  rw [Finset.prod_congr rfl fun j _ => hsz j]
  have hk2 : ∏ j : Fin n, (if j = k then ∫ z : ℂ, u z * g17gauss z else ∫ z : ℂ, g17gauss z)
      = (∫ z : ℂ, u z * g17gauss z) * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase k,
          ∫ z : ℂ, g17gauss z := by
    rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => (if j = k then ∫ z : ℂ, u z * g17gauss z else ∫ z : ℂ, g17gauss z))
        (a := k) (Finset.mem_univ k)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun j hj => by
        have hjk : j ≠ k := by simpa using hj
        rw [ite_eq_right hjk]
  rw [hk2, Finset.prod_congr rfl (fun j _ => g17gauss_integral),
    Finset.prod_const_one, mul_one]

/-- The Gaussian average of a squared permutation-product term factors into the product of the
squared entry norms plus one. -/
private theorem clause17_perm_single_moment {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) :
    (∫ G : Fin n → Fin n → ℂ,
        (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G)
      = ∏ i, (Complex.normSq (V i (σ i)) + 1) := by
  have hpt : ∀ G : Fin n → Fin n → ℂ,
      (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G
        = ∏ i, (Complex.normSq (V i (σ i) + G i (σ i)) * ∏ j, g17gauss (G i j)) := by
    intro G
    show (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * (∏ i, ∏ j, g17gauss (G i j)) = _
    rw [← Finset.prod_mul_distrib]
  have key : (∫ G : Fin n → Fin n → ℂ,
        (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G)
      = (∫ G : Fin n → Fin n → ℂ,
          ∏ i, (Complex.normSq (V i (σ i) + G i (σ i)) * ∏ j, g17gauss (G i j))) := by
    congr 1
    funext G
    exact hpt G
  have hFubini : (∫ G : Fin n → Fin n → ℂ,
        ∏ i, (Complex.normSq (V i (σ i) + G i (σ i)) * ∏ j, g17gauss (G i j)))
      = ∏ i, (∫ y : Fin n → ℂ, Complex.normSq (V i (σ i) + y (σ i)) * ∏ j, g17gauss (y j)) :=
    integral_fintype_prod_volume_eq_prod (f := fun (i : Fin n) (y : Fin n → ℂ) =>
      Complex.normSq (V i (σ i) + y (σ i)) * ∏ j, g17gauss (y j))
  rw [key, hFubini]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (clause17_integral_pi_special (σ i) (fun z => Complex.normSq (V i (σ i) + z))).trans
    (g17gauss_shift_moment (V i (σ i)))

/-- The squared norm of a sum over permutations is at most `n` factorial times the sum of the
squared norms. -/
private theorem clause17_normSq_sum_le {n : ℕ} (P : Equiv.Perm (Fin n) → ℂ) :
    Complex.normSq (∑ σ, P σ) ≤ (n ! : ℝ) * ∑ σ, Complex.normSq (P σ) := by
  rw [Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ σ, P σ‖ ≤ ∑ σ, ‖P σ‖ := norm_sum_le _ _
  have h2 : (∑ σ, ‖P σ‖) ^ 2 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ σ, ‖P σ‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (f := fun σ : Equiv.Perm (Fin n) => ‖P σ‖)
    simp only [Finset.card_univ] at this
    exact_mod_cast this
  have h3 : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = (n ! : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [h3] at h2
  have h4 : ∑ σ, ‖P σ‖ ^ 2 = ∑ σ, Complex.normSq (P σ) :=
    Finset.sum_congr rfl fun σ _ => (Complex.normSq_eq_norm_sq (P σ)).symm
  rw [h4] at h2
  nlinarith [sq_nonneg (∑ σ, ‖P σ‖), norm_nonneg (∑ σ, P σ), h1]

/-- If all entry norms are at most a nonnegative `R`, the permanent norm is at most `n`
factorial times `R` to the power `n`. -/
private theorem clause17_permanent_abs_le {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hV : ∀ i j, Complex.normSq (V i j) ≤ R ^ 2) :
    ‖Matrix.permanent V‖ ≤ (n ! : ℝ) * R ^ n := by
  have hle : ∀ i j, ‖V i j‖ ≤ R := by
    intro i j
    have h1 : ‖V i j‖ ^ 2 ≤ R ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hV i j
    have h2 : ‖V i j‖ ≤ Real.sqrt (R ^ 2) :=
      (Real.le_sqrt (norm_nonneg _) (sq_nonneg R)).2 h1
    rwa [Real.sqrt_sq hR] at h2
  have hperm : Matrix.permanent V = ∑ σ : Equiv.Perm (Fin n), ∏ i, V i (σ i) :=
    (clause17_permSum_permanent V).symm
  rw [hperm]
  have hsum : ‖∑ σ : Equiv.Perm (Fin n), ∏ i, V i (σ i)‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖∏ i, V i (σ i)‖ := norm_sum_le _ _
  have hterm : ∀ σ : Equiv.Perm (Fin n), ‖∏ i, V i (σ i)‖ ≤ R ^ n := by
    intro σ
    have h1 : ‖∏ i, V i (σ i)‖ = ∏ i, ‖V i (σ i)‖ :=
      map_prod ({ toFun := (‖·‖), map_one' := norm_one, map_mul' := norm_mul } : ℂ →* ℝ)
        (fun i => V i (σ i)) Finset.univ
    rw [h1]
    have h2 : ∏ i, ‖V i (σ i)‖ ≤ ∏ i : Fin n, R :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hle i (σ i)
    have h3 : (∏ i : Fin n, R) = R ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h3] at h2
    exact h2
  have h4 : ∑ σ : Equiv.Perm (Fin n), ‖∏ i, V i (σ i)‖
      ≤ ∑ σ : Equiv.Perm (Fin n), R ^ n :=
    Finset.sum_le_sum fun σ _ => hterm σ
  have h5 : (∑ σ : Equiv.Perm (Fin n), R ^ n) = (n ! : ℝ) * R ^ n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-- The Gaussian matrix density `loGaussianMatDensity` has integral one. -/
private theorem clause17_matDensity_integral (n : ℕ) :
    (∫ G : Fin n → Fin n → ℂ, loGaussianMatDensity n G) = 1 := by
  have h1 : (fun G : Fin n → Fin n → ℂ => loGaussianMatDensity n G)
      = fun G => ∏ i, ∏ j, g17gauss (G i j) := funext fun _ => rfl
  have h2 : (∫ G : Fin n → Fin n → ℂ, ∏ i, ∏ j, g17gauss (G i j))
      = ∏ i, (∫ y : Fin n → ℂ, ∏ j, g17gauss (y j)) :=
    integral_fintype_prod_volume_eq_prod
      (f := fun (_i : Fin n) (y : Fin n → ℂ) => ∏ j, g17gauss (y j))
  have h3 : ∀ _i : Fin n, (∫ y : Fin n → ℂ, ∏ j, g17gauss (y j))
      = ∏ j, (∫ z : ℂ, g17gauss z) :=
    fun _i => integral_fintype_prod_volume_eq_prod
      (f := fun (_j : Fin n) (z : ℂ) => g17gauss z)
  rw [h1, h2, Finset.prod_congr rfl fun i _ => h3 i,
    Finset.prod_congr rfl fun _ _ => g17gauss_integral]
  simp

/-- The Gaussian matrix density `loGaussianMatDensity` is continuous. -/
private theorem clause17_matDensity_continuous (n : ℕ) :
    Continuous (loGaussianMatDensity n) := by
  have h1 : loGaussianDensity = g17gauss := rfl
  have h2 : (fun G : Fin n → Fin n → ℂ => loGaussianMatDensity n G)
      = fun G => ∏ i : Fin n, ∏ j : Fin n, g17gauss (G i j) := funext fun _ => rfl
  show Continuous (fun G : Fin n → Fin n → ℂ => loGaussianMatDensity n G)
  rw [h2]
  refine continuous_finsetProd Finset.univ fun i _ =>
    continuous_finsetProd Finset.univ fun j _ =>
      g17gauss_continuous.comp (by fun_prop)

/-- The permanent of the sum of `V` and the matrix defined by `G` depends continuously on `G`. -/
private theorem clause17_permContinuous {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun G : Fin n → Fin n → ℂ => Matrix.permanent (V + Matrix.of G)) := by
  have h : (fun G : Fin n → Fin n → ℂ => Matrix.permanent (V + Matrix.of G))
      = fun G => ∑ σ : Equiv.Perm (Fin n), ∏ i, (V i (σ i) + G i (σ i)) := by
    funext G
    rw [← clause17_permSum_permanent]
    exact Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => by
      rw [Matrix.add_apply, Matrix.of_apply]
  rw [h]
  fun_prop

/-- Bounds the Gaussian mean squared change of the permanent by four times the squared factorial
times the stated entry-bound factor. -/
theorem clause17_clause4b : ∀ (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ) (R : ℝ), 0 ≤ R →
    (∀ i j, Complex.normSq (V i j) ≤ R ^ 2) →
    (∫ G : Fin n → Fin n → ℂ,
        Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
          * loGaussianMatDensity n G
      ∂MeasureTheory.volume)
      ≤ 4 * (n ! : ℝ) ^ 2 * (1 + R ^ 2) ^ n := by
  intro n V R hR hV
  have hDint : (∫ G : Fin n → Fin n → ℂ, loGaussianMatDensity n G) = 1 :=
    clause17_matDensity_integral n
  have hDge : ∀ G : Fin n → Fin n → ℂ, 0 ≤ loGaussianMatDensity n G := by
    intro G
    unfold loGaussianMatDensity
    exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
      unfold loGaussianDensity
      positivity
  have hσfi : ∀ σ : Equiv.Perm (Fin n),
      Integrable (fun G : Fin n → Fin n → ℂ =>
        (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G) := by
    intro σ
    refine Integrable.of_integral_ne_zero ?_
    rw [clause17_perm_single_moment V σ]
    exact (Finset.prod_pos fun i _ =>
      add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (by norm_num)).ne'
  have hP : ∀ (G : Fin n → Fin n → ℂ) (σ : Equiv.Perm (Fin n)),
      Complex.normSq (∏ i, (V + Matrix.of G) i (σ i))
        = ∏ i, Complex.normSq (V i (σ i) + G i (σ i)) := by
    intro G σ
    rw [clause17_normSq_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Matrix.add_apply, Matrix.of_apply]
  have hCS : ∀ G : Fin n → Fin n → ℂ,
      Complex.normSq (Matrix.permanent (V + Matrix.of G))
        ≤ (n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
            (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) := by
    intro G
    have h := clause17_normSq_sum_le
      (fun σ : Equiv.Perm (Fin n) => ∏ i, (V + Matrix.of G) i (σ i))
    rw [clause17_permSum_permanent] at h
    rw [Finset.sum_congr rfl fun σ _ => hP G σ] at h
    exact h
  have hsub : ∀ G : Fin n → Fin n → ℂ,
      Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
        ≤ 2 * Complex.normSq (Matrix.permanent (V + Matrix.of G))
          + 2 * Complex.normSq (Matrix.permanent V) := by
    intro G
    have h1 : ‖Matrix.permanent (V + Matrix.of G) - Matrix.permanent V‖
        ≤ ‖Matrix.permanent (V + Matrix.of G)‖ + ‖Matrix.permanent V‖ := norm_sub_le _ _
    have h3 : (‖Matrix.permanent (V + Matrix.of G)‖ + ‖Matrix.permanent V‖) ^ 2
        ≤ 2 * ‖Matrix.permanent (V + Matrix.of G)‖ ^ 2 + 2 * ‖Matrix.permanent V‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Matrix.permanent (V + Matrix.of G)‖ - ‖Matrix.permanent V‖)]
    have h4 : ‖Matrix.permanent (V + Matrix.of G) - Matrix.permanent V‖ ^ 2
        ≤ 2 * ‖Matrix.permanent (V + Matrix.of G)‖ ^ 2 + 2 * ‖Matrix.permanent V‖ ^ 2 := by
      nlinarith [h1, h3,
        norm_nonneg (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V),
        norm_nonneg (Matrix.permanent (V + Matrix.of G)),
        norm_nonneg (Matrix.permanent V)]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact h4

  have hsumfi : Integrable (fun G : Fin n → Fin n → ℂ =>
      ∑ σ : Equiv.Perm (Fin n),
        (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G) :=
    integrable_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n))) fun σ _ => hσfi σ
  have hF1pt : ∀ G : Fin n → Fin n → ℂ,
      Complex.normSq (Matrix.permanent (V + Matrix.of G)) * loGaussianMatDensity n G
        ≤ (n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
            (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G := by
    intro G
    have hD : 0 ≤ loGaussianMatDensity n G := hDge G
    have hG := hCS G
    have h3 : Complex.normSq (Matrix.permanent (V + Matrix.of G)) * loGaussianMatDensity n G
        ≤ ((n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
            (∏ i, Complex.normSq (V i (σ i) + G i (σ i)))) * loGaussianMatDensity n G :=
      mul_le_mul_of_nonneg_right hG hD
    have h5 : ((∑ σ : Equiv.Perm (Fin n), (∏ i, Complex.normSq (V i (σ i) + G i (σ i)))) *
          loGaussianMatDensity n G)
        = ∑ σ : Equiv.Perm (Fin n),
            (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G :=
      Finset.sum_mul _ _ _
    have h4 : ((n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
          (∏ i, Complex.normSq (V i (σ i) + G i (σ i)))) * loGaussianMatDensity n G
        = (n ! : ℝ) * ((∑ σ : Equiv.Perm (Fin n),
            (∏ i, Complex.normSq (V i (σ i) + G i (σ i)))) * loGaussianMatDensity n G) := by
      ring
    rw [h4, h5] at h3
    exact h3
  have hF1fi : Integrable (fun G : Fin n → Fin n → ℂ =>
      Complex.normSq (Matrix.permanent (V + Matrix.of G)) * loGaussianMatDensity n G) := by
    have hdom : Integrable (fun G : Fin n → Fin n → ℂ =>
        (n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
          (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G) :=
      hsumfi.const_mul _
    refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall fun G => ?_)
    · exact Continuous.aestronglyMeasurable
        ((Complex.continuous_normSq.comp (clause17_permContinuous V)).mul
          (clause17_matDensity_continuous n))
    · have hn : 0 ≤ Complex.normSq (Matrix.permanent (V + Matrix.of G))
          * loGaussianMatDensity n G := mul_nonneg (Complex.normSq_nonneg _) (hDge G)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact hF1pt G
  have hF2fi : Integrable (fun G : Fin n → Fin n → ℂ =>
      Complex.normSq (Matrix.permanent V) * loGaussianMatDensity n G) := by
    have hDfi : Integrable (fun G : Fin n → Fin n → ℂ => loGaussianMatDensity n G) :=
      Integrable.of_integral_ne_zero (by rw [hDint]; norm_num)
    exact hDfi.const_mul _

  have hFfi : Integrable (fun G : Fin n → Fin n → ℂ =>
      Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
        * loGaussianMatDensity n G) := by
    have hsum : Integrable (fun G : Fin n → Fin n → ℂ =>
        2 * (Complex.normSq (Matrix.permanent (V + Matrix.of G)) * loGaussianMatDensity n G)
          + 2 * (Complex.normSq (Matrix.permanent V) * loGaussianMatDensity n G)) :=
      (hF1fi.const_mul 2).add (hF2fi.const_mul 2)
    refine Integrable.mono' hsum ?_ (Filter.Eventually.of_forall fun G => ?_)
    · exact Continuous.aestronglyMeasurable
        ((Complex.continuous_normSq.comp ((clause17_permContinuous V).sub continuous_const)).mul
          (clause17_matDensity_continuous n))
    · have hG := hsub G
      have hD : 0 ≤ loGaussianMatDensity n G := hDge G
      have h1 : Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
          * loGaussianMatDensity n G
          ≤ (2 * Complex.normSq (Matrix.permanent (V + Matrix.of G))
              + 2 * Complex.normSq (Matrix.permanent V)) * loGaussianMatDensity n G :=
        mul_le_mul_of_nonneg_right hG hD
      rw [add_mul] at h1
      have h2 : (2 * Complex.normSq (Matrix.permanent (V + Matrix.of G)))
          * loGaussianMatDensity n G
          = 2 * (Complex.normSq (Matrix.permanent (V + Matrix.of G))
              * loGaussianMatDensity n G) := by ring
      have h3 : (2 * Complex.normSq (Matrix.permanent V)) * loGaussianMatDensity n G
          = 2 * (Complex.normSq (Matrix.permanent V) * loGaussianMatDensity n G) := by ring
      rw [h2, h3] at h1
      have hn : 0 ≤ Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
          * loGaussianMatDensity n G := mul_nonneg (Complex.normSq_nonneg _) (hDge G)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact h1
  have hmain : (∫ G : Fin n → Fin n → ℂ,
        Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
          * loGaussianMatDensity n G)
      ≤ (∫ G : Fin n → Fin n → ℂ,
          2 * (Complex.normSq (Matrix.permanent (V + Matrix.of G)) * loGaussianMatDensity n G)
            + 2 * (Complex.normSq (Matrix.permanent V) * loGaussianMatDensity n G)) :=
    integral_mono_ae hFfi ((hF1fi.const_mul 2).add (hF2fi.const_mul 2))
      (Filter.Eventually.of_forall fun G => by
        have hG := hsub G
        have hD : 0 ≤ loGaussianMatDensity n G := hDge G
        have h1 := mul_le_mul_of_nonneg_right hG hD
        rw [add_mul] at h1
        have h2 : (2 * Complex.normSq (Matrix.permanent (V + Matrix.of G)))
            * loGaussianMatDensity n G
            = 2 * (Complex.normSq (Matrix.permanent (V + Matrix.of G))
                * loGaussianMatDensity n G) := by ring
        have h3 : (2 * Complex.normSq (Matrix.permanent V)) * loGaussianMatDensity n G
            = 2 * (Complex.normSq (Matrix.permanent V) * loGaussianMatDensity n G) := by ring
        rw [h2, h3] at h1
        exact h1)
  rw [integral_add (hF1fi.const_mul 2) (hF2fi.const_mul 2)] at hmain
  rw [integral_const_mul, integral_const_mul] at hmain

  have hF1le : (∫ G : Fin n → Fin n → ℂ,
        Complex.normSq (Matrix.permanent (V + Matrix.of G)) * loGaussianMatDensity n G)
      ≤ (n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
          ∏ i, (Complex.normSq (V i (σ i)) + 1) := by
    have hdom : Integrable (fun G : Fin n → Fin n → ℂ =>
        (n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
          (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G) :=
      hsumfi.const_mul _
    have hle := integral_mono_ae hF1fi hdom
      (Filter.Eventually.of_forall fun G => hF1pt G)
    have hdomint : (∫ G : Fin n → Fin n → ℂ,
        (n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
          (∏ i, Complex.normSq (V i (σ i) + G i (σ i))) * loGaussianMatDensity n G)
        = (n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
            ∏ i, (Complex.normSq (V i (σ i)) + 1) := by
      rw [integral_const_mul, integral_finsetSum Finset.univ fun σ _ => hσfi σ,
        Finset.sum_congr rfl fun σ _ => clause17_perm_single_moment V σ]
    rw [hdomint] at hle
    exact hle

  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ∏ i, (Complex.normSq (V i (σ i)) + 1) ≤ (1 + R ^ 2) ^ n := by
    intro σ
    have h1 : ∏ i : Fin n, (Complex.normSq (V i (σ i)) + 1)
        ≤ ∏ i : Fin n, (R ^ 2 + 1) :=
      Finset.prod_le_prod₀ (fun i _ => add_nonneg (Complex.normSq_nonneg _) (by norm_num)) fun i _ => by
        have := hV i (σ i)
        linarith
    have h2 : (∏ i : Fin n, (R ^ 2 + 1)) = (1 + R ^ 2) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [h2] at h1
    exact h1
  have hsumle : (∑ σ : Equiv.Perm (Fin n), ∏ i, (Complex.normSq (V i (σ i)) + 1))
      ≤ (n ! : ℝ) * (1 + R ^ 2) ^ n := by
    have h1 : (∑ σ : Equiv.Perm (Fin n), ∏ i, (Complex.normSq (V i (σ i)) + 1))
        ≤ ∑ σ : Equiv.Perm (Fin n), (1 + R ^ 2) ^ n :=
      Finset.sum_le_sum fun σ _ => hterm σ
    have h2 : (∑ σ : Equiv.Perm (Fin n), ((1 + R ^ 2) ^ n : ℝ))
        = (n ! : ℝ) * (1 + R ^ 2) ^ n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    rw [h2] at h1
    exact h1

  have hpV : Complex.normSq (Matrix.permanent V) ≤ ((n ! : ℝ) * R ^ n) ^ 2 := by
    have h1 := clause17_permanent_abs_le V R hR hV
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖Matrix.permanent V‖), norm_nonneg (Matrix.permanent V)]
  have hF2val : (∫ G : Fin n → Fin n → ℂ,
      Complex.normSq (Matrix.permanent V) * loGaussianMatDensity n G)
      = Complex.normSq (Matrix.permanent V) := by
    rw [integral_const_mul, hDint, mul_one]

  calc (∫ G : Fin n → Fin n → ℂ,
          Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
            * loGaussianMatDensity n G)
      ≤ 2 * (∫ G : Fin n → Fin n → ℂ,
            Complex.normSq (Matrix.permanent (V + Matrix.of G)) * loGaussianMatDensity n G)
          + 2 * (∫ G : Fin n → Fin n → ℂ,
            Complex.normSq (Matrix.permanent V) * loGaussianMatDensity n G) := hmain
    _ ≤ 2 * ((n ! : ℝ) * ∑ σ : Equiv.Perm (Fin n),
            ∏ i, (Complex.normSq (V i (σ i)) + 1))
          + 2 * Complex.normSq (Matrix.permanent V) := by
        rw [hF2val]
        gcongr
    _ ≤ 2 * ((n ! : ℝ) * ((n ! : ℝ) * (1 + R ^ 2) ^ n))
          + 2 * (((n ! : ℝ) * R ^ n) ^ 2) := by
        gcongr
    _ ≤ 4 * (n ! : ℝ) ^ 2 * (1 + R ^ 2) ^ n := by
        have h1 : ((n ! : ℝ) * R ^ n) ^ 2 = (n ! : ℝ) ^ 2 * (R ^ 2) ^ n := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [h1]
        have h2 : (R ^ 2) ^ n ≤ (1 + R ^ 2) ^ n :=
          pow_le_pow_left₀ (by positivity) (by linarith) n
        have h3 : 2 * ((n ! : ℝ) * ((n ! : ℝ) * (1 + R ^ 2) ^ n))
            + 2 * ((n ! : ℝ) ^ 2 * (R ^ 2) ^ n)
            ≤ 4 * (n ! : ℝ) ^ 2 * (1 + R ^ 2) ^ n := by
          nlinarith [sq_nonneg ((n ! : ℝ)), h2, mul_nonneg (by positivity :
              (0:ℝ) ≤ (n ! : ℝ) ^ 2) (by positivity : (0:ℝ) ≤ (1 + R ^ 2) ^ n),
            mul_nonneg (by positivity :
              (0:ℝ) ≤ (n ! : ℝ) ^ 2) (pow_nonneg (sq_nonneg R) n)]
        exact h3
end Qatlib.Concepts.BosonFock.PermAnalysis
