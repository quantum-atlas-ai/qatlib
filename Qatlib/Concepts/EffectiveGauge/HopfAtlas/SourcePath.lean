/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PathTransport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth source families as continuous paths on the physical time interval

Finite-dimensional parameters include the original Euclidean transverse two-space.
Joint smoothness of the
actual source implies smoothness into the uniform continuous-path norm;
smoothness of a path name is not assumed as an extra input promise.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set Metric
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Abbreviation for Transverse Point in the Hopf Atlas construction. -/
abbrev TransversePoint := EuclideanSpace ℝ (Fin 2)

section GenericCurry
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Definition of source Path Over in the Hopf Atlas construction. -/
def sourcePathOver (g : P × ℝ → F) (hg : Continuous g)
    (p : P) : C(TransportTime, F) :=
  ⟨fun t => g (p, t), hg.comp (continuous_const.prodMk continuous_subtype_val)⟩

omit [NormedSpace ℝ P] [NormedSpace ℝ F] in
/-- Original `sourcePathOver_apply` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
@[simp] theorem sourcePathOver_apply (g : P × ℝ → F) (hg : Continuous g)
    (p : P) (t : TransportTime) : sourcePathOver g hg p t=g (p, t) := rfl

omit [NormedSpace ℝ P] [NormedSpace ℝ F] in
/-- Original `continuous_sourcePathOver` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
theorem continuous_sourcePathOver (g : P × ℝ → F) (hg : Continuous g) :
    Continuous (sourcePathOver g hg) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hg.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Definition of path Linear in the Hopf Atlas construction. -/
private def pathLinear (A : C(TransportTime, P →L[ℝ] F)) :
    P →L[ℝ] C(TransportTime, F) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun t => A t v, A.continuous.clm_apply continuous_const⟩
      map_add' := by intro v w; apply ContinuousMap.ext; intro t; exact (A t).map_add v w
      map_smul' := by intro c v; apply ContinuousMap.ext; intro t; exact (A t).map_smul c v }
    ‖A‖ (by
      intro v
      apply (ContinuousMap.norm_le (C := ‖A‖*‖v‖) _ (by positivity)).mpr
      intro t
      exact ((A t).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm t) (norm_nonneg v)))

/-- Original `pathLinear_norm` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
private theorem pathLinear_norm (A : C(TransportTime, P →L[ℝ] F)) :
    ‖pathLinear A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (pathLinear A) (M := ‖A‖) (norm_nonneg A)
  intro v
  apply (ContinuousMap.norm_le (C := ‖A‖*‖v‖) _ (by positivity)).mpr
  intro t
  exact ((A t).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm t) (norm_nonneg v))

/-- Definition of path Linear CLM in the Hopf Atlas construction. -/
private def pathLinearCLM : C(TransportTime, P →L[ℝ] F) →L[ℝ]
    P →L[ℝ] C(TransportTime, F) :=
  LinearMap.mkContinuous
    { toFun := fun A : C(TransportTime, P →L[ℝ] F) => pathLinear A
      map_add' := by intro A B; apply ContinuousLinearMap.ext; intro v; apply ContinuousMap.ext; intro t; rfl
      map_smul' := by intro c A; apply ContinuousLinearMap.ext; intro v; apply ContinuousMap.ext; intro t; rfl }
    1 (by intro A; simpa using pathLinear_norm A)

/-- Original `hasFDerivAt_path_of_pointwise` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
private theorem hasFDerivAt_path_of_pointwise
    (f : P → C(TransportTime, F))
    (D : P → P →L[ℝ] C(TransportTime, F))
    (hD : Continuous D)
    (hf : ∀ p t, HasFDerivAt (fun u => f u t)
      ((ContinuousMap.evalCLM ℝ t).comp (D p)) p) (p₀ : P) :
    HasFDerivAt f (D p₀) p₀ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hnear : ∀ᶠ p in 𝓝 p₀, ‖D p-D p₀‖ ≤ c := by
    have hdiff : Continuous (fun p => D p-D p₀) := hD.sub continuous_const
    have hn : Continuous (norm : (P →L[ℝ] C(TransportTime, F)) → ℝ) :=
      @continuous_norm (P →L[ℝ] C(TransportTime, F)) _
    have hcont : Continuous (fun p => ‖D p-D p₀‖) := hn.comp hdiff
    have h : ∀ᶠ p in 𝓝 p₀, ‖D p-D p₀‖ < c := by
      exact hcont.continuousAt.eventually_lt continuousAt_const
        (by simpa only [sub_self, ContinuousLinearMap.opNorm_zero] using hc)
    filter_upwards [h] with p hp
    exact hp.le
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  filter_upwards [ball_mem_nhds p₀ hδ] with p hp
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).mpr
  intro t
  have hpoint : ∀ u ∈ ball p₀ δ,
      ‖(ContinuousMap.evalCLM ℝ t).comp (D u)-
        (ContinuousMap.evalCLM ℝ t).comp (D p₀)‖ ≤ c := by
    intro u hu
    apply ContinuousLinearMap.opNorm_le_bound _ hc.le
    intro v
    calc
      _ ≤ ‖(D u-D p₀) v‖ := ((D u-D p₀) v).norm_coe_le_norm t
      _ ≤ ‖D u-D p₀‖*‖v‖ := (D u-D p₀).le_opNorm v
      _ ≤ c*‖v‖ := mul_le_mul_of_nonneg_right (hb u hu) (norm_nonneg v)
  exact (convex_ball p₀ δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun u _ => (hf u t).hasFDerivWithinAt) hpoint (mem_ball_self hδ) hp

/-- Definition of source Derivative in the Hopf Atlas construction. -/
private def sourceDerivative (g : P × ℝ → F) (z : P × ℝ) :
    P →L[ℝ] F := (fderiv ℝ g z).comp (ContinuousLinearMap.inl ℝ P ℝ)

/-- Original `continuous_sourceDerivative` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
private theorem continuous_sourceDerivative {g : P × ℝ → F}
    (hg : ContDiff ℝ 1 g) : Continuous (sourceDerivative g) := by
  exact (hg.fderiv_right (m := 0) (by simp)).continuous.clm_comp continuous_const

/-- Original `sourcePathOver_hasFDerivAt` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
private theorem sourcePathOver_hasFDerivAt {g : P × ℝ → F} (hg : ContDiff ℝ 1 g)
    (p : P) : HasFDerivAt (sourcePathOver g hg.continuous)
      (pathLinearCLM (sourcePathOver (sourceDerivative g) (continuous_sourceDerivative hg) p)) p := by
  apply hasFDerivAt_path_of_pointwise (sourcePathOver g hg.continuous)
    (fun u => pathLinearCLM (sourcePathOver (sourceDerivative g) (continuous_sourceDerivative hg) u))
    _ _ p
  · exact pathLinearCLM.continuous.comp (continuous_sourcePathOver _ (continuous_sourceDerivative hg))
  · intro u t
    have hi : HasFDerivAt (fun v : P => (v, (t : ℝ)))
        (ContinuousLinearMap.inl ℝ P ℝ) u := by
      simpa only [ContinuousLinearMap.inl, id] using
        (hasFDerivAt_id u).prodMk (hasFDerivAt_const (t : ℝ) u)
    exact ((hg.differentiable (by norm_num) (u, (t : ℝ))).hasFDerivAt.comp u hi)

variable [FiniteDimensional ℝ P]

/-- Original `contDiff_sourcePathOver_nat` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
private theorem contDiff_sourcePathOver_nat (n : ℕ) :
    ∀ (g : P × ℝ → F) (hg : ContDiff ℝ (n : ℕ∞ω) g),
      ContDiff ℝ (n : ℕ∞ω) (sourcePathOver g hg.continuous) := by
  induction n with
  | zero =>
    intro g hg
    simpa only [Nat.cast_zero, contDiff_zero] using continuous_sourcePathOver g hg.continuous
  | succ n ih =>
    intro g hg
    have hgc : Continuous g := hg.continuous
    change ContDiff ℝ ((n+1 : ℕ) : ℕ∞ω) (sourcePathOver g hgc)
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast Nat.succ_pos n)
    have hd : Differentiable ℝ (sourcePathOver g hg.continuous) :=
      fun p => (sourcePathOver_hasFDerivAt hg1 p).differentiableAt
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv_apply]
    refine ⟨hd, by simp, fun v => ?_⟩
    let gv := fun z : P × ℝ => fderiv ℝ g z (v, 0)
    have hv : ContDiff ℝ (n : ℕ∞ω) gv :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    have heq : (fun p => fderiv ℝ (sourcePathOver g hgc) p v) = sourcePathOver gv hv.continuous := by
      funext p
      apply ContinuousMap.ext
      intro t
      rw [(sourcePathOver_hasFDerivAt hg1 p).fderiv]
      rfl
    rw [heq]
    exact ih gv hv

/-- Joint C-infinity of a source on transverse space times time gives a
C-infinity family in the actual uniform norm on the physical time interval. -/
theorem contDiff_sourcePathOver {g : P × ℝ → F} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (sourcePathOver g hg.continuous) := by
  rw [contDiff_infty]
  intro n
  have hle : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  exact contDiff_sourcePathOver_nat n g (hg.of_le hle)

end GenericCurry

/-! The original two-dimensional public interfaces retain their types. -/
section Curry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Definition of source Path in the Hopf Atlas construction. -/
def sourcePath (g : TransversePoint × ℝ → F) (hg : Continuous g)
    (p : TransversePoint) : C(TransportTime, F) := sourcePathOver g hg p

omit [NormedSpace ℝ F] in
/-- Original `sourcePath_apply` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
@[simp] theorem sourcePath_apply (g : TransversePoint × ℝ → F) (hg : Continuous g)
    (p : TransversePoint) (t : TransportTime) : sourcePath g hg p t=g (p, t) := rfl

omit [NormedSpace ℝ F] in
/-- Original `continuous_sourcePath` guarantee for the `SourcePath` construction; the complete source hypotheses are retained. -/
theorem continuous_sourcePath (g : TransversePoint × ℝ → F) (hg : Continuous g) :
    Continuous (sourcePath g hg) := continuous_sourcePathOver g hg

/-- Joint C-infinity gives a C-infinity family in the actual uniform path norm. -/
theorem contDiff_sourcePath {g : TransversePoint × ℝ → F} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (sourcePath g hg.continuous) := contDiff_sourcePathOver hg

end Curry
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
