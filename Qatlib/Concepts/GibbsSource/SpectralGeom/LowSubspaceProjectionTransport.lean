/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSubspaceResidualTransport

@[expose] public section


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

/-! Exact comparison of two finite-dimensional subspaces presented by isometric
column maps with a common coordinate space. The reverse directed estimate is
proved from finite-dimensional injectivity/surjectivity, not assumed.
The actual-source consumer keeps the true spectral-basis representation explicit. -/

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
namespace ResidualTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℂ E] in
/-- Pythagoras for the range and orthogonal complement of an isometric column map. -/
theorem isometry_norm_sq_split (V : E →L[ℂ] F)
    (hV : ∀ z, ‖V z‖ = ‖z‖) (x : F) :
    ‖x‖ ^ 2 = ‖V.adjoint x‖ ^ 2 + ‖x - trialProjection V x‖ ^ 2 := by
  change ‖x‖ ^ 2 = ‖V.adjoint x‖ ^ 2 + ‖x - V (V.adjoint x)‖ ^ 2
  rw [norm_sub_sq (𝕜 := ℂ), ← V.adjoint_inner_left,
    inner_self_eq_norm_sq (𝕜 := ℂ), hV]
  ring

/-- A finite-dimensional endomorphism and its adjoint share the same strict lower norm bound. -/
theorem lower_bound_adjoint_sq (A : E →L[ℂ] E) {c : ℝ} (hc : 0 < c)
    (hA : ∀ z, c * ‖z‖ ^ 2 ≤ ‖A z‖ ^ 2) (y : E) :
    c * ‖y‖ ^ 2 ≤ ‖A.adjoint y‖ ^ 2 := by
  have hi : Function.Injective A := by
    intro z w hzw
    have hn : A (z-w)=0 := by rw [map_sub, hzw, sub_self]
    have hh := hA (z-w)
    rw [hn, norm_zero, zero_pow (by norm_num : 2≠0)] at hh
    have hz : ‖z-w‖=0 := by
      by_contra hz
      have hp : 0 < ‖z-w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hprod := mul_pos hc (sq_pos_of_pos hp)
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hs : Function.Surjective A :=
    LinearMap.injective_iff_surjective.mp hi
  obtain ⟨z, hz⟩ := hs y
  have hpair : ‖y‖ ^ 2 ≤ ‖A.adjoint y‖ * ‖z‖ := by
    calc
      _ = (inner ℂ y y).re := (inner_self_eq_norm_sq (𝕜 := ℂ) y).symm
      _ = (inner ℂ (A.adjoint y) z).re := by rw [A.adjoint_inner_left, hz]
      _ ≤ ‖inner ℂ (A.adjoint y) z‖ := Complex.re_le_norm _
      _ ≤ ‖A.adjoint y‖ * ‖z‖ := norm_inner_le_norm _ _
  have hh := hA z
  rw [hz] at hh
  by_cases hy : y=0
  · simp [hy]
  have hys : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
  have hsq := pow_le_pow_left₀ (sq_nonneg ‖y‖) hpair 2
  have hm1 := mul_le_mul_of_nonneg_left hsq hc.le
  have hm2 := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖A.adjoint y‖)
  nlinarith

/-- The reverse directed angle is derived from a strict forward bound and equal finite domain. -/
theorem reverse_directed_le (U V : E →L[ℂ] F)
    (hU : ∀ z, ‖U z‖=‖z‖) (hV : ∀ z, ‖V z‖=‖z‖)
    {eps : ℝ} (heps : 0 ≤ eps) (hlt : eps < 1)
    (hbound : ‖((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U‖ ≤ eps) :
    ‖((ContinuousLinearMap.id ℂ F)-trialProjection U).comp V‖ ≤ eps := by
  let A : E →L[ℂ] E := V.adjoint.comp U
  have hc : 0 < 1-eps^2 := by nlinarith
  have hA (z : E) : (1-eps^2)*‖z‖^2 ≤ ‖A z‖^2 := by
    have hp := isometry_norm_sq_split V hV (U z)
    rw [hU] at hp
    have hb := (((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U).le_opNorm z
    have hm := mul_le_mul_of_nonneg_right hbound (norm_nonneg z)
    have hd : ‖U z-trialProjection V (U z)‖ ≤ eps*‖z‖ := hb.trans hm
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    change (1-eps^2)*‖z‖^2 ≤ ‖V.adjoint (U z)‖^2
    nlinarith
  have hadj (z : E) :
      (1-eps^2)*‖z‖^2 ≤ ‖U.adjoint (V z)‖^2 := by
    have h := lower_bound_adjoint_sq A hc hA z
    simpa only [A, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] using h
  apply ContinuousLinearMap.opNorm_le_bound _ heps
  intro z
  change ‖V z-trialProjection U (V z)‖ ≤ eps*‖z‖
  have hp := isometry_norm_sq_split U hU (V z)
  rw [hV] at hp
  have hl := hadj z
  have hnn := mul_nonneg heps (norm_nonneg z)
  nlinarith [norm_nonneg (V z-trialProjection U (V z))]

omit [FiniteDimensional ℂ E] in
/-- Two directed estimates combine without a factor of two, by orthogonal decomposition. -/
theorem norm_trialProjection_sub_le_of_directed
    (U V : E →L[ℂ] F)
    (hU : ∀ z, ‖U z‖=‖z‖) (hV : ∀ z, ‖V z‖=‖z‖)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hforward : ‖((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U‖ ≤ eps)
    (hreverse : ‖((ContinuousLinearMap.id ℂ F)-trialProjection U).comp V‖ ≤ eps) :
    ‖trialProjection U - trialProjection V‖ ≤ eps := by
  have hv (z : E) : V.adjoint (V z)=z := by
    have h := congrArg (fun T : E →L[ℂ] E => T z)
      (V.norm_map_iff_adjoint_comp_self.mp hV)
    simpa using h
  have hperp : IsSelfAdjoint ((ContinuousLinearMap.id ℂ F)-trialProjection U) :=
    (IsSelfAdjoint.one (F →L[ℂ] F)).sub (trialProjection_selfAdjoint U)
  have ha : ‖V.adjoint.comp ((ContinuousLinearMap.id ℂ F)-trialProjection U)‖ ≤ eps := by
    have h : ‖(((ContinuousLinearMap.id ℂ F)-trialProjection U).comp V).adjoint‖
        ≤ eps := by simpa only [LinearIsometryEquiv.norm_map] using hreverse
    simpa only [ContinuousLinearMap.adjoint_comp, hperp.adjoint_eq] using h
  apply ContinuousLinearMap.opNorm_le_bound _ heps
  intro x
  have hpw : trialProjection U (x-trialProjection U x)=0 := by
    rw [map_sub, trialProjection_idempotent U hU, sub_self]
  have h1 : ‖trialProjection U x - trialProjection V (trialProjection U x)‖
      ≤ eps * ‖U.adjoint x‖ := by
    exact ((((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U).le_opNorm
      (U.adjoint x)).trans (mul_le_mul_of_nonneg_right hforward (norm_nonneg _))
  have h2 : ‖trialProjection V (x-trialProjection U x)‖
      ≤ eps * ‖x-trialProjection U x‖ := by
    change ‖V (V.adjoint (x-trialProjection U x))‖ ≤ _
    rw [hV]
    have hb := (V.adjoint.comp ((ContinuousLinearMap.id ℂ F)-trialProjection U)).le_opNorm
      (x-trialProjection U x)
    have hm := mul_le_mul_of_nonneg_right ha (norm_nonneg (x-trialProjection U x))
    have hh := hb.trans hm
    simpa only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      ContinuousLinearMap.id_apply, hpw, sub_zero] using hh
  have horth : inner ℂ
      (trialProjection U x-trialProjection V (trialProjection U x))
      (trialProjection V (x-trialProjection U x))=0 := by
    change inner ℂ
      (trialProjection U x-V (V.adjoint (trialProjection U x)))
      (V (V.adjoint (x-trialProjection U x)))=0
    rw [← V.adjoint_inner_left, map_sub, hv, sub_self, inner_zero_left]
  have heq : (trialProjection U-trialProjection V) x =
      (trialProjection U x-trialProjection V (trialProjection U x)) -
        trialProjection V (x-trialProjection U x) := by
    simp only [_root_.sub_apply, map_sub]
    abel
  have hs : ‖(trialProjection U-trialProjection V) x‖^2 =
      ‖trialProjection U x-trialProjection V (trialProjection U x)‖^2 +
      ‖trialProjection V (x-trialProjection U x)‖^2 := by
    rw [heq, norm_sub_sq (𝕜 := ℂ), horth]
    simp
  have hp := isometry_norm_sq_split U hU x
  have hps := congrArg (fun t : ℝ => eps^2*t) hp
  have h1sq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2sq := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hnn := mul_nonneg heps (norm_nonneg x)
  nlinarith [norm_nonneg ((trialProjection U-trialProjection V) x)]

/-- A strict directed estimate controls the difference of the equal-rank projectors. -/
theorem norm_trialProjection_sub_le
    (U V : E →L[ℂ] F)
    (hU : ∀ z, ‖U z‖=‖z‖) (hV : ∀ z, ‖V z‖=‖z‖)
    {eps : ℝ} (heps : 0 ≤ eps) (hlt : eps < 1)
    (hforward : ‖((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U‖ ≤ eps) :
    ‖trialProjection U-trialProjection V‖ ≤ eps :=
  norm_trialProjection_sub_le_of_directed U V hU hV heps hforward
    (reverse_directed_le U V hU hV heps hlt hforward)

omit [FiniteDimensional ℂ E] in
/-- A directed angle between two orthogonal projections never exceeds one. -/
theorem norm_directed_le_one (U V : E →L[ℂ] F)
    (hU : ∀ z, ‖U z‖=‖z‖) (hV : ∀ z, ‖V z‖=‖z‖) :
    ‖((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  change ‖U z-trialProjection V (U z)‖ ≤ 1*‖z‖
  have hp := isometry_norm_sq_split V hV (U z)
  rw [hU] at hp
  nlinarith [sq_nonneg ‖V.adjoint (U z)‖, norm_nonneg z,
    norm_nonneg (U z-trialProjection V (U z))]

/-- Exact equal-rank principal-angle norm identity, including the boundary value one. -/
theorem norm_trialProjection_sub_eq_directed
    (U V : E →L[ℂ] F)
    (hU : ∀ z, ‖U z‖=‖z‖) (hV : ∀ z, ‖V z‖=‖z‖) :
    ‖trialProjection U-trialProjection V‖ =
      ‖((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U‖ := by
  let d := ‖((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U‖
  have hd : 0 ≤ d := norm_nonneg _
  apply le_antisymm
  · change ‖trialProjection U-trialProjection V‖ ≤ d
    by_cases hlt : d<1
    · exact norm_trialProjection_sub_le U V hU hV hd hlt le_rfl
    · have hone : ‖trialProjection U-trialProjection V‖ ≤ 1 :=
        norm_trialProjection_sub_le_of_directed U V hU hV (by norm_num)
          (norm_directed_le_one U V hU hV) (norm_directed_le_one V U hV hU)
      exact hone.trans (le_of_not_gt hlt)
  · have hu (z : E) : U.adjoint (U z)=z := by
      have h := congrArg (fun T : E →L[ℂ] E => T z)
        (U.norm_map_iff_adjoint_comp_self.mp hU)
      simpa using h
    have hid : ((ContinuousLinearMap.id ℂ F)-trialProjection V).comp U =
        (trialProjection U-trialProjection V).comp U := by
      ext z
      change U z-trialProjection V (U z) =
        U (U.adjoint (U z))-trialProjection V (U z)
      rw [hu]
    have hun : ‖U‖ ≤ 1 := ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
      (fun z hz => by rw [hU, hz])
    rw [hid]
    exact ((trialProjection U-trialProjection V).opNorm_comp_le U).trans
      (by simpa using mul_le_mul_of_nonneg_left hun (norm_nonneg (trialProjection U-trialProjection V)))


section ActualSource
variable {D : ℕ}

/-- Full residual to a two-sided actual spectral-projector estimate.
The exact true-low basis V is explicit: its projection must equal the actual
positive-low spectral cut. No desired angle estimate is assumed about V. -/
theorem source_low_trialProjection_sub_norm_le
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0 ≤ (hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • G)
    (U V : E →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D))
    (hU : ∀ z, ‖U z‖ = ‖z‖) (hV : ∀ z, ‖V z‖ = ‖z‖)
    {cutoff μ lam η : ℝ} (hcut : cutoff < μ) (hgap : lam < μ)
    (hVrange : trialProjection V = sourceMap (sourcePositiveLowProjection L hL cutoff))
    (hsep : ∀ i, 0 < sourceEigenvalues L hL i →
      cutoff < sourceEigenvalues L hL i → μ ≤ sourceEigenvalues L hL i)
    (hcenter : ∀ z, inner ℂ (sourceEuclideanVector G) (U z) = 0)
    (hcap : ∀ z, (inner ℂ z (trialCompression (sourceMap L) U z)).re ≤ lam * ‖z‖ ^ 2)
    (hres : ‖trialResidual (sourceMap L) U‖ ≤ η) :
    ‖trialProjection U-sourceMap (sourcePositiveLowProjection L hL cutoff)‖
      ≤ η / (μ-lam) := by
  rw [← hVrange, norm_trialProjection_sub_eq_directed U V hU hV, hVrange]
  exact source_low_trial_norm_le L hL hpos G hker U hcut hgap hsep hcenter hcap hres

end ActualSource

end ResidualTransport
end Qatlib.Concepts.GibbsSource.SpectralGeom
