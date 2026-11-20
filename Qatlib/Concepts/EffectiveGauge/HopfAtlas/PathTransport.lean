/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PathSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# The classical transport map on continuous pure coefficient paths

One fixed unit initial point is used for every coefficient path. Existence
selects a solution classically; the estimates identify a unique path and
give differentiability in the uniform norm. This is not an executable solver.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace NNReal Topology ContDiff
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- A unit seed and a continuous vector coefficient give a quaternion curve continuous on the
transport interval, starting at the seed, with unit norm throughout and within-interval
derivative given by right multiplication by the embedded imaginary coefficient. -/
private theorem rawTransport_exists (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath) :
    ∃ q : ℝ → ℍ, q 0=q₀ ∧ ContinuousOn q (Icc 0 physicalPeriod) ∧
      (∀ t ∈ Icc 0 physicalPeriod, HasDerivWithinAt q
        (q t*spinOfVector (extendPath K t)) (Icc 0 physicalPeriod) t) ∧
      ∀ t ∈ Icc 0 physicalPeriod, ‖q t‖=1 := by
  apply right_transport_exists physicalPeriod_pos.le
    (spinEmbedding.continuous.comp (continuous_extendPath K)).continuousOn ‖K‖₊
    _ (fun _ _ => rfl) q₀ h₀
  intro t _
  change ‖spinOfVector (extendPath K t)‖ ≤ ‖K‖
  rw [spinOfVector_norm]
  exact K.norm_coe_le_norm _

/-- Definition of raw Transport in the Hopf Atlas construction. -/
private def rawTransport (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath) : ℝ → ℍ :=
  Classical.choose (rawTransport_exists q₀ h₀ K)

/-- The chosen raw transport starts at the unit seed, is continuous on the closed transport
interval, solves the right transport equation there in the within-interval sense, and stays unit
throughout. -/
private theorem rawTransport_spec (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath) :
    rawTransport q₀ h₀ K 0=q₀ ∧ ContinuousOn (rawTransport q₀ h₀ K) (Icc 0 physicalPeriod) ∧
      (∀ t ∈ Icc 0 physicalPeriod, HasDerivWithinAt (rawTransport q₀ h₀ K)
        (rawTransport q₀ h₀ K t*spinOfVector (extendPath K t)) (Icc 0 physicalPeriod) t) ∧
      ∀ t ∈ Icc 0 physicalPeriod, ‖rawTransport q₀ h₀ K t‖=1 :=
  Classical.choose_spec (rawTransport_exists q₀ h₀ K)

/-- Definition of path Transport in the Hopf Atlas construction. -/
def pathTransport (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath) : QuaternionPath :=
  ⟨fun t => Classical.choose
      (show ∃ q : ℝ → ℍ, q 0=q₀ ∧ ContinuousOn q (Icc 0 physicalPeriod) ∧
        (∀ t ∈ Icc 0 physicalPeriod, HasDerivWithinAt q
          (q t*spinOfVector (extendPath K t)) (Icc 0 physicalPeriod) t) ∧
        ∀ t ∈ Icc 0 physicalPeriod, ‖q t‖=1 from by exact rawTransport_exists q₀ h₀ K) t,
    by exact (rawTransport_spec q₀ h₀ K).2.1.domRestrict⟩

/-- The continuous path obtained by transporting a unit seed takes the seed value at the initial
time. -/
@[simp] theorem pathTransport_start (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath) :
    pathTransport q₀ h₀ K transportStart=q₀ := (rawTransport_spec q₀ h₀ K).1

/-- Transport by the quaternion embedding of a coefficient path preserves the unit norm of the
seed at every interval time. -/
@[simp] theorem pathTransport_unit (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath)
    (t : TransportTime) : ‖pathTransport q₀ h₀ K t‖=1 :=
  (rawTransport_spec q₀ h₀ K).2.2.2 t t.2

/-- The extended transported path has within-interval derivative equal to the path value times
its imaginary quaternion coefficient on the right at each interval time. -/
theorem pathTransport_hasDerivWithinAt (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath)
    (t : ℝ) (ht : t ∈ Icc 0 physicalPeriod) :
    HasDerivWithinAt (extendPath (pathTransport q₀ h₀ K))
      (extendPath (pathTransport q₀ h₀ K) t*spinOfVector (extendPath K t))
      (Icc 0 physicalPeriod) t := by
  have he : ∀ u ∈ Icc 0 physicalPeriod,
      extendPath (pathTransport q₀ h₀ K) u=rawTransport q₀ h₀ K u := by
    intro u hu
    rw [extendPath_on _ u hu]
    rfl
  rw [he t ht]
  exact ((rawTransport_spec q₀ h₀ K).2.2.1 t ht).congr_of_mem he ht

/-- The linear variation evaluated on the entire continuous path. -/
def pathVariation (Q : QuaternionPath) : CoefficientPath →L[ℝ] QuaternionPath :=
  ((ContinuousLinearMap.mul ℝ QuaternionPath).flip Q).comp
    (pathVolterra.comp (((ContinuousLinearMap.mul ℝ QuaternionPath).flip (star Q)).comp
      ((ContinuousLinearMap.mul ℝ QuaternionPath Q).comp coefficientEmbedding)))

/-- The first variation in coefficient direction `H` integrates the embedded perturbation
conjugated by the path from zero to `t`, then right-multiplies the integral by `Q t`. -/
@[simp] theorem pathVariation_apply (Q : QuaternionPath) (H : CoefficientPath) (t : TransportTime) :
    pathVariation Q H t =
      (∫ u in (0 : ℝ)..(t : ℝ),
        extendPath Q u*spinOfVector (extendPath H u)*star (extendPath Q u))*Q t := rfl

/-- For two coefficient paths with the same unit seed, the transport difference at time `t` is
bounded by `t` times their supremum-norm difference. Subtracting its first variation leaves a
remainder bounded by `t²` times the squared coefficient difference norm. -/
private theorem pathTransport_point_estimates (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (K J : CoefficientPath) (t : TransportTime) :
    ‖pathTransport q₀ h₀ J t-pathTransport q₀ h₀ K t‖ ≤ (t : ℝ)*‖J-K‖ ∧
    ‖pathTransport q₀ h₀ J t-pathTransport q₀ h₀ K t-
      pathVariation (pathTransport q₀ h₀ K) (J-K) t‖ ≤ (t : ℝ)^2*‖J-K‖^2 := by
  let q := extendPath (pathTransport q₀ h₀ K)
  let r := extendPath (pathTransport q₀ h₀ J)
  let k := fun u => spinOfVector (extendPath K u)
  let l := fun u => spinOfVector (extendPath J u)
  have hsub : Icc (0 : ℝ) (t : ℝ) ⊆ Icc 0 physicalPeriod :=
    fun _ hu => ⟨hu.1, hu.2.trans t.2.2⟩
  have hk : ContinuousOn k (Icc 0 t) :=
    (spinEmbedding.continuous.comp (continuous_extendPath K)).continuousOn
  have hl : ContinuousOn l (Icc 0 t) :=
    (spinEmbedding.continuous.comp (continuous_extendPath J)).continuousOn
  have hq : ∀ u ∈ Icc 0 (t : ℝ), HasDerivWithinAt q (q u*k u) (Icc 0 t) u :=
    fun u hu => (pathTransport_hasDerivWithinAt q₀ h₀ K u (hsub hu)).mono hsub
  have hr : ∀ u ∈ Icc 0 (t : ℝ), HasDerivWithinAt r (r u*l u) (Icc 0 t) u :=
    fun u hu => (pathTransport_hasDerivWithinAt q₀ h₀ J u (hsub hu)).mono hsub
  have hnq : ∀ u ∈ Icc 0 (t : ℝ), ‖q u‖=1 := by
    intro u hu
    simpa only [q, extendPath_on _ u (hsub hu)] using pathTransport_unit q₀ h₀ K ⟨u, hsub hu⟩
  have hnr : ∀ u ∈ Icc 0 (t : ℝ), ‖r u‖=1 := by
    intro u hu
    simpa only [r, extendPath_on _ u (hsub hu)] using pathTransport_unit q₀ h₀ J ⟨u, hsub hu⟩
  have hp : ∀ u ∈ Icc 0 (t : ℝ), (k u).re=0 := fun _ _ => rfl
  have hinit : r 0=q 0 := by
    simp only [r, q, extendPath_on _ 0 ⟨le_rfl, physicalPeriod_pos.le⟩]
    change pathTransport q₀ h₀ J transportStart=pathTransport q₀ h₀ K transportStart
    simp
  have he : ∀ u ∈ Icc 0 (t : ℝ), ‖l u-k u‖ ≤ ‖J-K‖ := by
    intro u _
    change ‖spinEmbedding (extendPath J u)-spinEmbedding (extendPath K u)‖ ≤ ‖J-K‖
    rw [← map_sub, spinEmbedding.norm_map]
    exact (J-K).norm_coe_le_norm _
  have hs := unit_transport_stability t.2.1 hk hl hq hr hp hnq hnr hinit he
  have hR := unit_transport_quadratic_remainder t.2.1 hk hl hq hr hp hnq hnr hinit he
  constructor
  · simpa only [r, q, extendPath_coe, sub_zero] using hs
  · have hi : (fun u => q u*(l u-k u)*star (q u)) =
        fun u => q u*spinOfVector (extendPath (J-K) u)*star (q u) := by
      funext u
      change _ = q u*spinEmbedding (extendPath J u-extendPath K u)*star (q u)
      rw [map_sub]
      rfl
    rw [hi] at hR
    simpa only [r, q, extendPath_coe, sub_zero, pathVariation_apply] using hR

/-- With the same unit seed, transport on the closed interval is Lipschitz in the continuous
coefficient path, with constant equal to the physical period in supremum norm. -/
theorem pathTransport_stability (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K J : CoefficientPath) :
    ‖pathTransport q₀ h₀ J-pathTransport q₀ h₀ K‖ ≤ physicalPeriod*‖J-K‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg physicalPeriod_pos.le (norm_nonneg _))).mpr
  intro t
  exact (pathTransport_point_estimates q₀ h₀ K J t).1.trans
    (mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _))

/-- With a fixed unit seed, subtracting the linear path variation from the transport increment
leaves a supremum-norm error at most the squared period times the squared coefficient increment
norm. -/
theorem pathTransport_quadratic_remainder (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K J : CoefficientPath) :
    ‖pathTransport q₀ h₀ J-pathTransport q₀ h₀ K-
      pathVariation (pathTransport q₀ h₀ K) (J-K)‖ ≤ physicalPeriod^2*‖J-K‖^2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  exact (pathTransport_point_estimates q₀ h₀ K J t).2.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ t.2.1 t.2.2 2) (sq_nonneg _))

/-- At a fixed unit seed, the Fréchet derivative of transport with respect to its continuous
coefficient path is the path variation along the resulting quaternion path. -/
theorem pathTransport_hasFDerivAt (q₀ : ℍ) (h₀ : ‖q₀‖=1) (K : CoefficientPath) :
    HasFDerivAt (pathTransport q₀ h₀) (pathVariation (pathTransport q₀ h₀ K)) K := by
  rw [hasFDerivAt_iff_tendsto]
  have hb : ∀ J : CoefficientPath, ‖J-K‖⁻¹*
      ‖pathTransport q₀ h₀ J-pathTransport q₀ h₀ K-
        pathVariation (pathTransport q₀ h₀ K) (J-K)‖ ≤ physicalPeriod^2*‖J-K‖ := by
    intro J
    by_cases hn : ‖J-K‖=0
    · simp [hn]
    · calc
        _ ≤ ‖J-K‖⁻¹*(physicalPeriod^2*‖J-K‖^2) :=
          mul_le_mul_of_nonneg_left (pathTransport_quadratic_remainder q₀ h₀ K J)
            (inv_nonneg.mpr (norm_nonneg _))
        _ = physicalPeriod^2*‖J-K‖ := by field_simp
  have ht : Filter.Tendsto (fun J : CoefficientPath => physicalPeriod^2*‖J-K‖)
      (𝓝 K) (𝓝 0) := by
    have hc : Continuous (fun J : CoefficientPath => physicalPeriod^2*‖J-K‖) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm)
    simpa using hc.tendsto K
  exact squeeze_zero (fun J => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hb ht

/-- The operator sending a quaternion path to its linear coefficient-variation map is smooth
between the continuous path spaces. -/
theorem contDiff_pathVariation : ContDiff ℝ ∞ pathVariation := by
  have hL : ContDiff ℝ ∞ (ContinuousLinearMap.mul ℝ QuaternionPath :
      QuaternionPath → QuaternionPath →L[ℝ] QuaternionPath) :=
    by exact ContinuousLinearMap.contDiff _
  have hR : ContDiff ℝ ∞
      (fun Q : QuaternionPath => (ContinuousLinearMap.mul ℝ QuaternionPath).flip Q) :=
    by exact ContinuousLinearMap.contDiff _
  have hS : ContDiff ℝ ∞ (fun Q : QuaternionPath => star Q) :=
    (starL' ℝ : QuaternionPath ≃L[ℝ] QuaternionPath).toContinuousLinearMap.contDiff
  exact hR.clm_comp (contDiff_const.clm_comp ((hR.comp hS).clm_comp (hL.clm_comp contDiff_const)))

/-- Smooth dependence on the full Banach space of continuous pure coefficient paths.
The order is C-infinity (`infty`), not the analytic `omega` order. -/
theorem contDiff_pathTransport (q₀ : ℍ) (h₀ : ‖q₀‖=1) :
    ContDiff ℝ ∞ (pathTransport q₀ h₀) := by
  have hd : Differentiable ℝ (pathTransport q₀ h₀) :=
    fun K => (pathTransport_hasFDerivAt q₀ h₀ K).differentiableAt
  have heq : fderiv ℝ (pathTransport q₀ h₀) = fun K => pathVariation (pathTransport q₀ h₀ K) :=
    funext fun K => (pathTransport_hasFDerivAt q₀ h₀ K).fderiv
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => simpa only [Nat.cast_zero, contDiff_zero] using hd.continuous
  | succ n hn =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨hd, by simp, ?_⟩
    rw [heq]
    have hle : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
    exact (contDiff_pathVariation.of_le hle).comp hn

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
