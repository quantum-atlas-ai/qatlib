/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TimeDepSim11.MainResults.AverageHamiltonianBound
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Gaussian smoothing of actual time-ordered evolution

Fixed source: arXiv:1102.1360v1, Appendix B, pp.5--6. The Gaussian
convolution retains its full real-line tails. The discrepancy is derived from
actual Dyson propagators and a full-line Duhamel integral; its connection to
actual finite-interval propagator errors is proved by `smoothing_evolution_limit`.

The main estimate assumes continuity, a uniform norm bound, compact time
support, positive Gaussian width and pointwise Hermiticity. Gaussian
normalization, absolute moments, convolution regularity and the Fubini
hypotheses are all proved, rather than supplied as error certificates.
-/

set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Papers.TimeDepSim11.MainResults.AverageHamiltonianBound
namespace Qatlib.Papers.TimeDepSim11.MainResults.GaussianSmoothingBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

/-- The normalized real Gaussian density of width `σ`. -/
def gaussianKernel (σ u : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt (2 * Real.pi))) * Real.exp (-(u ^ 2) / (2 * σ ^ 2))

/-- The normalized Gaussian kernel is integrable for positive width. -/
theorem gaussian_integrable (σ : ℝ) (hσ : 0 < σ) :
    Integrable (gaussianKernel σ) := by
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  convert (integrable_exp_neg_mul_sq hb).const_mul (1 / (σ * Real.sqrt (2 * Real.pi))) using 1
  funext u
  dsimp [gaussianKernel]
  congr 2
  ring

/-- The absolute first-moment integrand is genuinely Bochner integrable. -/
theorem gaussian_moment_integrable (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun u => gaussianKernel σ u * |u|) := by
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  convert (integrable_mul_exp_neg_mul_sq hb).norm.const_mul
    (1 / (σ * Real.sqrt (2 * Real.pi))) using 1
  funext u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  dsimp [gaussianKernel]
  rw [show -(u ^ 2) / (2 * σ ^ 2) = -(1 / (2 * σ ^ 2)) * u ^ 2 by ring]
  ring

/-- The Gaussian kernel has total mass one. -/
theorem gaussian_mass (σ : ℝ) (hσ : 0 < σ) :
    (∫ u : ℝ, gaussianKernel σ u) = 1 := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hfun : gaussianKernel σ = fun u =>
      (1 / (σ * Real.sqrt (2 * Real.pi))) *
        Real.exp (-(1 / (2 * σ ^ 2)) * u ^ 2) := by
    funext u
    dsimp [gaussianKernel]
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_gaussian]
  have hscale : Real.pi / (1 / (2 * σ ^ 2)) = σ ^ 2 * (2 * Real.pi) := by
    field_simp
  rw [hscale, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq_eq_abs, abs_of_pos hσ]
  have hroot : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

/-- The positive half-line first moment of an unnormalized Gaussian. -/
theorem gaussian_half_moment (b : ℝ) (hb : 0 < b) :
    (∫ u : ℝ in Ioi 0, u * Real.exp (-b * u ^ 2)) = (2 * b)⁻¹ := by
  have h := integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  convert h using 1 <;> simp

/-- The Gaussian density has absolute first moment sigma times sqrt two over pi. -/
theorem gaussian_kernel_abs_moment (σ : ℝ) (hσ : 0 < σ) :
    (∫ u : ℝ, gaussianKernel σ u * |u|) = σ * Real.sqrt (2 / Real.pi) := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  have hrew : (fun u : ℝ => gaussianKernel σ u * |u|) =
      (fun u => (1 / (σ * Real.sqrt (2 * Real.pi))) *
        (|u| * Real.exp (-(1 / (2 * σ ^ 2)) * |u| ^ 2))) := by
    funext u
    simp only [gaussianKernel, sq_abs]
    rw [show -(u ^ 2) / (2 * σ ^ 2) = -(1 / (2 * σ ^ 2)) * u ^ 2 by ring]
    ring
  rw [hrew, integral_const_mul,
    integral_comp_abs (f := fun u => u * Real.exp (-(1 / (2 * σ ^ 2)) * u ^ 2)),
    gaussian_half_moment _ hb]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have htwo : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

/-- Gaussian convolution of the actual Hamiltonian matrix field. -/
def smoothedHamiltonian {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ t : ℝ) : Matrix I I ℂ :=
  ∫ s : ℝ, gaussianKernel σ (t-s) • H s

/-- The full-line Duhamel discrepancy, including the Gaussian tails outside the source support. -/
def smoothingDiscrepancy {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ : ℝ) : Matrix I I ℂ :=
  (-Complex.I) • ∫ t : ℝ,
    star (orderedEvolution (fun u => Complex.I • H u) 0 t) *
      (H t - smoothedHamiltonian H σ t) *
      orderedEvolution (fun u => Complex.I • smoothedHamiltonian H σ u) 0 t

/-- Gaussian convolution of a bounded continuous matrix field is absolutely integrable at every time. -/
theorem smoothed_integrable {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (σ M : ℝ) (hσ : 0 < σ)
    (hb : ∀ s, ‖H s‖ ≤ M) (t : ℝ) :
    Integrable (fun s : ℝ => gaussianKernel σ (t-s) • H s) := by
  have hg : Continuous (gaussianKernel σ) := by unfold gaussianKernel; fun_prop
  have hm : AEStronglyMeasurable (fun s : ℝ => gaussianKernel σ (t-s) • H s) := by
    exact ((hg.comp (continuous_const.sub continuous_id)).smul hH).aestronglyMeasurable
  refine (((gaussian_integrable σ hσ).comp_sub_left t).mul_const M).mono' hm ?_
  filter_upwards with s
  have hp : 0 ≤ gaussianKernel σ (t-s) := by unfold gaussianKernel; positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left (hb s) hp

/-- Averaging against the normalized Gaussian preserves the uniform operator-norm bound. -/
theorem smoothed_bounded {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ M : ℝ) (hσ : 0 < σ)
    (hb : ∀ s, ‖H s‖ ≤ M) (t : ℝ) : ‖smoothedHamiltonian H σ t‖ ≤ M := by
  have hg := ((gaussian_integrable σ hσ).comp_sub_left t).mul_const M
  have hh : ∀ s : ℝ, ‖gaussianKernel σ (t-s) • H s‖ ≤ gaussianKernel σ (t-s)*M := by
    intro s
    have hp : 0 ≤ gaussianKernel σ (t-s) := by unfold gaussianKernel; positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (hb s) hp
  have hn := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hh)
  refine hn.trans_eq ?_
  rw [integral_mul_const, integral_sub_left_eq_self, gaussian_mass σ hσ, one_mul]

/-- Gaussian averaging preserves pointwise Hermiticity. -/
theorem smoothed_hermitian {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ : ℝ) (hh : ∀ s, (H s).IsHermitian)
    (hk : ∀ t, Integrable (fun s : ℝ => gaussianKernel σ (t-s) • H s)) (t : ℝ) :
    (smoothedHamiltonian H σ t).IsHermitian := by
  change star (∫ s : ℝ, gaussianKernel σ (t-s) • H s) = _
  have he := (starL' ℝ : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ).toContinuousLinearMap.integral_comp_comm (hk t)
  have hefun : (fun s : ℝ => star (gaussianKernel σ (t-s) • H s)) =
      fun s : ℝ => gaussianKernel σ (t-s) • H s := by
    funext s
    rw [star_smul, star_trivial, show star (H s) = H s from (hh s).eq]
  simpa only [ContinuousLinearEquiv.coe_coe, starL'_apply, hefun, smoothedHamiltonian] using he.symm

/-- The Gaussian density is bounded by its normalizing constant. -/
theorem gaussian_bound (σ : ℝ) (hσ : 0 < σ) (u : ℝ) :
    gaussianKernel σ u ≤ 1/(σ*Real.sqrt (2*Real.pi)) := by
  have hc : 0 ≤ 1/(σ*Real.sqrt (2*Real.pi)) := by positivity
  have he : Real.exp (-(u^2)/(2*σ^2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) (by positivity)
  simpa only [gaussianKernel, mul_one] using mul_le_mul_of_nonneg_left he hc

/-- A continuous matrix field supported in a compact time window is Bochner integrable. -/
theorem supported_integrable {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (T : ℝ)
    (hsupp : ∀ s, (s < 0 ∨ T < s) → H s = 0) : Integrable H := by
  have hc : HasCompactSupport H := HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := T))
    (fun s hs => hsupp s (by simpa only [mem_Icc, not_and_or, not_le] using hs))
  exact hH.integrable_of_hasCompactSupport hc

/-- Gaussian convolution is continuous, including its tails beyond the source time window. -/
theorem smoothed_continuous {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (σ T : ℝ) (hσ : 0 < σ)
    (hsupp : ∀ s, (s < 0 ∨ T < s) → H s = 0) : Continuous (smoothedHamiltonian H σ) := by
  have hg : Continuous (gaussianKernel σ) := by unfold gaussianKernel; fun_prop
  let c := 1/(σ*Real.sqrt (2*Real.pi))
  have hdom : Integrable (fun s : ℝ => c*‖H s‖) :=
    (supported_integrable H hH T hsupp).norm.const_mul c
  apply continuous_of_dominated
    (fun t => ((hg.comp (continuous_const.sub continuous_id)).smul hH).aestronglyMeasurable)
    (fun t => Filter.Eventually.of_forall fun s => ?_) hdom
    (Filter.Eventually.of_forall fun s => (hg.comp (continuous_id.sub continuous_const)).smul continuous_const)
  have hp : 0 ≤ gaussianKernel σ (t-s) := by unfold gaussianKernel; positivity
  change ‖gaussianKernel σ (t-s) • H s‖ ≤ c*‖H s‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_right (gaussian_bound σ hσ (t-s)) (norm_nonneg _)

/-- Both summands in the source Fubini rearrangement are absolutely integrable. -/
theorem fubini_integrable {I : Type} [Fintype I] [DecidableEq I]
    (H U V : ℝ → Matrix I I ℂ) (hH : Continuous H) (hUc : Continuous U) (hVc : Continuous V)
    (σ T : ℝ) (hσ : 0 < σ) (hsupp : ∀ s, (s < 0 ∨ T < s) → H s = 0)
    (hU : ∀ s, ‖U s‖ ≤ 1) (hV : ∀ s, ‖V s‖ ≤ 1) :
    Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (U p.1)*H p.1*V p.1)) (volume.prod volume) ∧
    Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (U p.2)*H p.1*V p.2)) (volume.prod volume) := by
  have hg : Continuous (gaussianKernel σ) := by unfold gaussianKernel; fun_prop
  have hHi := supported_integrable H hH T hsupp
  have hdom0 := hHi.norm.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ)
    (gaussian_integrable σ hσ)
  have hdom : Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1)*‖H p.1‖)
      (volume.prod volume) := by
    simpa [Function.comp_def, mul_comm] using hdom0.swap
  have hn (s t : ℝ) : ‖star (U t)*H s*V t‖ ≤ ‖H s‖ := by
    calc
      _ ≤ (‖star (U t)‖*‖H s‖)*‖V t‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖H s‖)*1 := by
        rw [norm_star]
        gcongr
        · exact hU t
        · exact hV t
      _ = ‖H s‖ := by ring
  constructor
  · refine hdom.mono' (by apply Continuous.aestronglyMeasurable; fun_prop) ?_
    filter_upwards with p
    have hp : 0 ≤ gaussianKernel σ (p.2-p.1) := by unfold gaussianKernel; positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (hn p.1 p.1) hp
  · refine hdom.mono' (by apply Continuous.aestronglyMeasurable; fun_prop) ?_
    filter_upwards with p
    have hp : 0 ≤ gaussianKernel σ (p.2-p.1) := by unfold gaussianKernel; positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (hn p.1 p.2) hp

/-- Fubini and Gaussian normalization identify the paired cancellation with the full Duhamel integrand. -/
theorem gaussian_cancellation {I : Type} [Fintype I] [DecidableEq I]
    (H U V : ℝ → Matrix I I ℂ) (σ : ℝ) (hσ : 0 < σ)
    (hk : ∀ t, Integrable (fun s : ℝ => gaussianKernel σ (t-s) • H s))
    (hf0 : Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (U p.1)*H p.1*V p.1)) (volume.prod volume))
    (hf1 : Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (U p.2)*H p.1*V p.2)) (volume.prod volume)) :
    (∫ s : ℝ, ∫ t : ℝ, gaussianKernel σ (t-s) •
      (star (U s)*H s*V s - star (U t)*H s*V t)) =
    ∫ t : ℝ, star (U t)*(H t-smoothedHamiltonian H σ t)*V t := by
  let F0 := fun s t : ℝ => gaussianKernel σ (t-s) • (star (U s)*H s*V s)
  let F1 := fun s t : ℝ => gaussianKernel σ (t-s) • (star (U t)*H s*V t)
  have hm (s : ℝ) : (∫ t : ℝ, gaussianKernel σ (t-s)) = 1 := by
    rw [integral_sub_right_eq_self]
    exact gaussian_mass σ hσ
  have hi0 (s : ℝ) : (∫ t : ℝ, F0 s t) = star (U s)*H s*V s := by
    dsimp [F0]
    rw [integral_smul_const, hm, one_smul]
  have hi1 (t : ℝ) : (∫ s : ℝ, F1 s t) = star (U t)*smoothedHamiltonian H σ t*V t := by
    let W := ContinuousLinearMap.mulLeftRight ℝ (Matrix I I ℂ) (star (U t)) (V t)
    have hw := W.integral_comp_comm (hk t)
    simpa only [W, ContinuousLinearMap.mulLeftRight_apply, map_smul,
      smul_mul_assoc, mul_smul_comm, smoothedHamiltonian, F1] using hw
  have h0 : Integrable (fun s : ℝ => star (U s)*H s*V s) := by
    convert hf0.integral_prod_left using 1
    funext s
    exact (hi0 s).symm
  have h1 : Integrable (fun t : ℝ => star (U t)*smoothedHamiltonian H σ t*V t) := by
    convert hf1.integral_prod_right using 1
    funext t
    exact (hi1 t).symm
  simp_rw [smul_sub]
  change (∫ s : ℝ, ∫ t : ℝ, F0 s t-F1 s t) = _
  rw [integral_integral (hf0.sub hf1), integral_sub hf0 hf1,
    ← integral_integral (f := F0) hf0, ← integral_integral (f := F1) hf1,
    integral_integral_swap (f := F1) hf1]
  simp_rw [hi0, hi1]
  rw [← integral_sub h0 h1]
  congr 1
  funext t
  simp only [Matrix.mul_sub, Matrix.sub_mul]

/-- The full-line Duhamel integrand is absolutely integrable under the source Fubini conditions. -/
theorem gaussian_duhamel_int {I : Type} [Fintype I] [DecidableEq I]
    (H U V : ℝ → Matrix I I ℂ) (σ : ℝ) (hσ : 0 < σ)
    (hk : ∀ t, Integrable (fun s : ℝ => gaussianKernel σ (t-s) • H s))
    (hf0 : Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (U p.1)*H p.1*V p.1)) (volume.prod volume))
    (hf1 : Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (U p.2)*H p.1*V p.2)) (volume.prod volume)) :
    Integrable (fun t : ℝ => star (U t)*(H t-smoothedHamiltonian H σ t)*V t) := by
  have hi0 (s : ℝ) : (∫ t : ℝ, gaussianKernel σ (t-s) •
      (star (U s)*H s*V s)) = star (U s)*H s*V s := by
    rw [integral_smul_const, integral_sub_right_eq_self, gaussian_mass σ hσ, one_smul]
  have hi1 (t : ℝ) : (∫ s : ℝ, gaussianKernel σ (t-s) •
      (star (U t)*H s*V t)) = star (U t)*smoothedHamiltonian H σ t*V t := by
    let W := ContinuousLinearMap.mulLeftRight ℝ (Matrix I I ℂ) (star (U t)) (V t)
    have hw := W.integral_comp_comm (hk t)
    simpa only [W, ContinuousLinearMap.mulLeftRight_apply, map_smul,
      smul_mul_assoc, mul_smul_comm, smoothedHamiltonian] using hw
  have h0 : Integrable (fun s : ℝ => star (U s)*H s*V s) := by
    convert hf0.integral_prod_left using 1
    funext s
    exact (hi0 s).symm
  have h1 : Integrable (fun t : ℝ => star (U t)*smoothedHamiltonian H σ t*V t) := by
    convert hf1.integral_prod_right using 1
    funext t
    exact (hi1 t).symm
  convert h0.sub h1 using 1
  funext t
  simp only [Matrix.mul_sub, Matrix.sub_mul, Pi.sub_apply]

/-- The paired operator cancellation has the source Gaussian-moment bound. -/
theorem paired_gaussian_bound {I : Type} [Fintype I] [DecidableEq I]
    (H U V : ℝ → Matrix I I ℂ) (σ T M : ℝ) (hσ : 0 < σ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hH : ∀ s, ‖H s‖ ≤ M) (hU : ∀ s, ‖U s‖ ≤ 1) (hV : ∀ s, ‖V s‖ ≤ 1)
    (hUl : ∀ s t, ‖U s-U t‖ ≤ M*|s-t|)
    (hVl : ∀ s t, ‖V s-V t‖ ≤ M*|s-t|)
    (hsupp : ∀ s, (s < 0 ∨ T < s) → H s = 0) :
    ‖∫ s : ℝ, ∫ t : ℝ, gaussianKernel σ (t-s) •
      (star (U s)*H s*V s-star (U t)*H s*V t)‖ ≤
      2*M^2*T*Real.sqrt (2/Real.pi)*σ := by
  let F := fun s : ℝ => ∫ t : ℝ, gaussianKernel σ (t-s) •
    (star (U s)*H s*V s-star (U t)*H s*V t)
  have hn (s : ℝ) : ‖F s‖ ≤ 2*M^2*(σ*Real.sqrt (2/Real.pi)) := by
    have hg : Integrable (fun t : ℝ => 2*M^2*(gaussianKernel σ (t-s)*|t-s|)) :=
      ((gaussian_moment_integrable σ hσ).comp_sub_right s).const_mul (2*M^2)
    have hb (t : ℝ) : ‖gaussianKernel σ (t-s) •
        (star (U s)*H s*V s-star (U t)*H s*V t)‖ ≤
        2*M^2*(gaussianKernel σ (t-s)*|t-s|) := by
      have hp : 0 ≤ gaussianKernel σ (t-s) := by dsimp [gaussianKernel]; positivity
      have hp1 := paired_norm H U V M s t hM (hH s) (hU t) (hV s) (hUl s t) (hVl s t)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
      calc
        _ ≤ gaussianKernel σ (t-s) * (2*M^2*|s-t|) := mul_le_mul_of_nonneg_left hp1 hp
        _ = _ := by rw [abs_sub_comm s t]; ring
    have hh := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hb)
    dsimp [F]
    refine hh.trans_eq ?_
    rw [integral_const_mul, integral_sub_right_eq_self (fun u : ℝ => gaussianKernel σ u * |u|) s,
      gaussian_kernel_abs_moment σ hσ]
  have hcut : (∫ s : ℝ, F s) = ∫ s in (0 : ℝ)..T, F s := by
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have hs0 : s < 0 ∨ T < s := by simpa only [mem_Icc, not_and_or, not_le] using hs
    simp [F, hsupp s hs0]
  change ‖∫ s : ℝ, F s‖ ≤ _
  rw [hcut]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
    (fun s _ => hn s)
  rw [sub_zero, abs_of_nonneg hT] at hb
  exact hb.trans_eq (by ring)

/-- Gaussian smoothing has the source error bound under explicit analytic Fubini regularity. -/
theorem smoothing_error_regular {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H)
    (T M σ : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hbound : ∀ t, ‖H t‖ ≤ M) (hσ : 0 < σ)
    (hsupp : ∀ t, (t < 0 ∨ T < t) → H t = 0)
    (hHerm : ∀ t, (H t).IsHermitian)
    (hSmooth : Continuous (smoothedHamiltonian H σ))
    (hSmoothHerm : ∀ t, (smoothedHamiltonian H σ t).IsHermitian)
    (hSmoothBound : ∀ t, ‖smoothedHamiltonian H σ t‖ ≤ M)
    (hk : ∀ t, Integrable (fun s : ℝ => gaussianKernel σ (t-s) • H s))
    (hf0 : Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (orderedEvolution (fun u => Complex.I • H u) 0 p.1) * H p.1 *
        orderedEvolution (fun u => Complex.I • smoothedHamiltonian H σ u) 0 p.1)) (volume.prod volume))
    (hf1 : Integrable (fun p : ℝ × ℝ => gaussianKernel σ (p.2-p.1) •
      (star (orderedEvolution (fun u => Complex.I • H u) 0 p.2) * H p.1 *
        orderedEvolution (fun u => Complex.I • smoothedHamiltonian H σ u) 0 p.2)) (volume.prod volume)) :
    ‖smoothingDiscrepancy H σ‖ ≤ 2*M^2*T*Real.sqrt (2/Real.pi)*σ := by
  let A := fun u => Complex.I • H u
  let B := fun u => Complex.I • smoothedHamiltonian H σ u
  let U := orderedEvolution A 0
  let V := orderedEvolution B 0
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hUn (u : ℝ) : ‖U u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I H hH hHerm 0 u)
  have hVn (u : ℝ) : ‖V u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I (smoothedHamiltonian H σ)
      hSmooth hSmoothHerm 0 u)
  have hAn (u : ℝ) : ‖A u‖ ≤ M := by simpa [A, norm_smul] using hbound u
  have hBn (u : ℝ) : ‖B u‖ ≤ M := by simpa [B, norm_smul] using hSmoothBound u
  have hUl (s t : ℝ) : ‖U s-U t‖ ≤ M*|s-t| :=
    ode_lipschitz A U M t s (orderedEvolution_hasDerivAt A hAc 0) hUn hAn
  have hVl (s t : ℝ) : ‖V s-V t‖ ≤ M*|s-t| :=
    ode_lipschitz B V M t s (orderedEvolution_hasDerivAt B hBc 0) hVn hBn
  unfold smoothingDiscrepancy
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  change ‖∫ t : ℝ, star (U t)*(H t-smoothedHamiltonian H σ t)*V t‖ ≤ _
  rw [← gaussian_cancellation H U V σ hσ hk hf0 hf1]
  exact paired_gaussian_bound H U V σ T M hσ hT hM hbound hUn hVn hUl hVl hsupp

/-- Gaussian smoothing of a bounded continuous Hermitian Hamiltonian obeys the source bound. -/
theorem smoothing_error_bound {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H)
    (T M σ : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hbound : ∀ t, ‖H t‖ ≤ M) (hσ : 0 < σ)
    (hsupp : ∀ t, (t < 0 ∨ T < t) → H t = 0)
    (hHerm : ∀ t, (H t).IsHermitian) :
    ‖smoothingDiscrepancy H σ‖ ≤ 2*M^2*T*Real.sqrt (2/Real.pi)*σ := by
  have hSmooth := smoothed_continuous H hH σ T hσ hsupp
  have hk := smoothed_integrable H hH σ M hσ hbound
  have hSmoothHerm := smoothed_hermitian H σ hHerm hk
  have hSmoothBound := smoothed_bounded H σ M hσ hbound
  let A := fun u => Complex.I • H u
  let B := fun u => Complex.I • smoothedHamiltonian H σ u
  let U := orderedEvolution A 0
  let V := orderedEvolution B 0
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun u =>
    (orderedEvolution_hasDerivAt A hAc 0 u).continuousAt
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun u =>
    (orderedEvolution_hasDerivAt B hBc 0 u).continuousAt
  have hUn (u : ℝ) : ‖U u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I H hH hHerm 0 u)
  have hVn (u : ℝ) : ‖V u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I (smoothedHamiltonian H σ)
      hSmooth hSmoothHerm 0 u)
  obtain ⟨hf0, hf1⟩ := fubini_integrable H U V hH hUc hVc σ T hσ hsupp hUn hVn
  exact smoothing_error_regular H hH T M σ hT hM hbound hσ hsupp hHerm hSmooth
    hSmoothHerm hSmoothBound hk hf0 hf1

/-- The normalized trace discrepancy has the same norm as the actual propagator difference. -/
theorem finite_trace_norm {I : Type} [Fintype I] [DecidableEq I]
    (H K : ℝ → Matrix I I ℂ) (hH : Continuous H) (hK : Continuous K)
    (hh : ∀ t, (H t).IsHermitian) (hk : ∀ t, (K t).IsHermitian) (a b : ℝ) :
    ‖(1-star (orderedEvolution (fun u => Complex.I • H u) 0 b)*
      orderedEvolution (fun u => Complex.I • K u) 0 b) -
      (1-star (orderedEvolution (fun u => Complex.I • H u) 0 a)*
      orderedEvolution (fun u => Complex.I • K u) 0 a)‖ =
    ‖orderedEvolution (fun u => Complex.I • H u) a b -
      orderedEvolution (fun u => Complex.I • K u) a b‖ := by
  let A := fun u => Complex.I • H u
  let B := fun u => Complex.I • K u
  let U := orderedEvolution A 0
  let V := orderedEvolution B 0
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hUb := ordered_evolution_hermitian_unitary I H hH hh 0 b
  have hUa := ordered_evolution_hermitian_unitary I H hH hh 0 a
  have hVa := ordered_evolution_hermitian_unitary I K hK hk 0 a
  have hUaa : U a*star (U a) = 1 := Matrix.mem_unitaryGroup_iff.mp hUa
  have hUbb : U b*star (U b) = 1 := Matrix.mem_unitaryGroup_iff.mp hUb
  have hVaa : V a*star (V a) = 1 := Matrix.mem_unitaryGroup_iff.mp hVa
  have heU : U b*star (U a) = orderedEvolution A a b := by
    have hc := orderedEvolution_cocycle A hAc 0 a b
    change orderedEvolution A a b*U a = U b at hc
    rw [← hc, mul_assoc, hUaa, mul_one]
  have heV : V b*star (V a) = orderedEvolution B a b := by
    have hc := orderedEvolution_cocycle B hBc 0 a b
    change orderedEvolution B a b*V a = V b at hc
    rw [← hc, mul_assoc, hVaa, mul_one]
  have he : U b*((1-star (U b)*V b)-(1-star (U a)*V a))*star (V a) =
      orderedEvolution A a b-orderedEvolution B a b := by
    calc
      _ = (U b*star (U a))*(V a*star (V a))-(U b*star (U b))*(V b*star (V a)) := by noncomm_ring
      _ = _ := by rw [heU, heV, hUbb, hVaa, mul_one, one_mul]
  have hn := congrArg norm he
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hVa), CStarRing.norm_mem_unitary_mul _ hUb] at hn
  exact hn

/-- Full-line discrepancy is the limit of actual finite evolution discrepancies. -/
theorem smoothing_discrepancy_trace {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ : ℝ) (hH : Continuous H)
    (hHerm : ∀ t, (H t).IsHermitian)
    (hSmooth : Continuous (smoothedHamiltonian H σ))
    (hint : Integrable (fun t : ℝ =>
      star (orderedEvolution (fun u => Complex.I • H u) 0 t) *
      (H t-smoothedHamiltonian H σ t) *
      orderedEvolution (fun u => Complex.I • smoothedHamiltonian H σ u) 0 t)) :
    Filter.Tendsto (fun n : ℕ =>
      (1 - star (orderedEvolution (fun u => Complex.I • H u) 0 (n : ℝ)) *
        orderedEvolution (fun u => Complex.I • smoothedHamiltonian H σ u) 0 (n : ℝ)) -
      (1 - star (orderedEvolution (fun u => Complex.I • H u) 0 (-(n : ℝ))) *
        orderedEvolution (fun u => Complex.I • smoothedHamiltonian H σ u) 0 (-(n : ℝ))))
      Filter.atTop (nhds (smoothingDiscrepancy H σ)) := by
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hi := intervalIntegral_tendsto_integral hint (Filter.tendsto_neg_atTop_atBot.comp hn) hn
  have hs := hi.const_smul (-Complex.I)
  convert hs using 1
  · funext n
    exact duhamel_finite H (smoothedHamiltonian H σ) hH hSmooth hHerm 0 (-(n : ℝ)) (n : ℝ)
  · rfl

/-- The actual finite propagator errors converge to a limit satisfying the source Gaussian bound. -/
theorem smoothing_evolution_limit {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H)
    (T M σ : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hbound : ∀ t, ‖H t‖ ≤ M) (hσ : 0 < σ)
    (hsupp : ∀ t, (t < 0 ∨ T < t) → H t = 0)
    (hHerm : ∀ t, (H t).IsHermitian) :
    ∃ e : ℝ, Filter.Tendsto (fun n : ℕ =>
      ‖orderedEvolution (fun u => Complex.I • H u) (-(n : ℝ)) (n : ℝ) -
        orderedEvolution (fun u => Complex.I • smoothedHamiltonian H σ u) (-(n : ℝ)) (n : ℝ)‖)
      Filter.atTop (nhds e) ∧ e ≤ 2*M^2*T*Real.sqrt (2/Real.pi)*σ := by
  refine ⟨‖smoothingDiscrepancy H σ‖, ?_, smoothing_error_bound H hH T M σ hT hM hbound hσ hsupp hHerm⟩
  have hSmooth := smoothed_continuous H hH σ T hσ hsupp
  have hk := smoothed_integrable H hH σ M hσ hbound
  have hSmoothHerm := smoothed_hermitian H σ hHerm hk
  let A := fun u => Complex.I • H u
  let B := fun u => Complex.I • smoothedHamiltonian H σ u
  let U := orderedEvolution A 0
  let V := orderedEvolution B 0
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun u =>
    (orderedEvolution_hasDerivAt A hAc 0 u).continuousAt
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun u =>
    (orderedEvolution_hasDerivAt B hBc 0 u).continuousAt
  have hUn (u : ℝ) : ‖U u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I H hH hHerm 0 u)
  have hVn (u : ℝ) : ‖V u‖ ≤ 1 :=
    l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I (smoothedHamiltonian H σ)
      hSmooth hSmoothHerm 0 u)
  obtain ⟨hf0, hf1⟩ := fubini_integrable H U V hH hUc hVc σ T hσ hsupp hUn hVn
  have hint := gaussian_duhamel_int H U V σ hσ hk hf0 hf1
  have ht := (smoothing_discrepancy_trace H σ hH hHerm hSmooth hint).norm
  convert ht using 1
  funext n
  exact (finite_trace_norm H (smoothedHamiltonian H σ) hH hSmooth hHerm hSmoothHerm (-(n : ℝ)) (n : ℝ)).symm

/-- A nonzero compactly supported Hermitian Hamiltonian witnesses consistency of the repaired model. -/
def nonzeroHamiltonian (t : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  (max 0 (1-|t-1|)) • 1

/-- The explicit nonzero example satisfies continuity, Hermiticity, boundedness and support. -/
theorem nonzero_model_valid :
    Continuous nonzeroHamiltonian ∧
    (∀ t, (nonzeroHamiltonian t).IsHermitian) ∧
    (∀ t, ‖nonzeroHamiltonian t‖ ≤ 1) ∧
    (∀ t, (t < 0 ∨ (2 : ℝ) < t) → nonzeroHamiltonian t = 0) ∧
    nonzeroHamiltonian 1 ≠ 0 := by
  refine ⟨by unfold nonzeroHamiltonian; fun_prop, ?_, ?_, ?_, ?_⟩
  · intro t
    exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all (max 0 (1-|t-1|)))
  · intro t
    have hc0 : 0 ≤ max 0 (1-|t-1|) := le_max_left _ _
    have hc1 : max 0 (1-|t-1|) ≤ 1 := max_le (by norm_num) (by linarith [abs_nonneg (t-1)])
    unfold nonzeroHamiltonian
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc
      _ ≤ max 0 (1-|t-1|)*1 := mul_le_mul_of_nonneg_left l2_norm_one_le hc0
      _ ≤ 1 := by simpa only [mul_one] using hc1
  · intro t ht
    have hc : 1-|t-1| ≤ 0 := by
      rcases ht with ht | ht
      · linarith [neg_le_abs (t-1)]
      · linarith [le_abs_self (t-1)]
    simp [nonzeroHamiltonian, max_eq_left hc]
  · simp [nonzeroHamiltonian]

end
end Qatlib.Papers.TimeDepSim11.MainResults.GaussianSmoothingBound
