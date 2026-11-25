/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.VanishCharge.ClebschFieldBridge
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Gauss linking integral of two closed space curves

[Kedia2018SuperfluidHelicity], Section II and Eq. (6),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
For two `C¹` closed curves parametrized on `[0, 2π]`, the Gauss linking integral
`(4π)⁻¹ ∮∮ ((γ₁' × γ₂') · (γ₁ - γ₂)) / |γ₁ - γ₂|³` is defined as an iterated interval
integral. We prove that the integral is symmetric under exchanging the two curves and that
it vanishes for curves lying in one affine plane: both facts are properties of the
analytic integral itself, before any topological interpretation.

The construction takes disjointness and smoothness as explicit hypotheses. The integral is
an analytic object; its integrality (equality with the topological linking number of the
two closed curves) is a classical theorem of topology that is not reproved here. Dynamics,
reconnection and the singular-core limit of the paper remain outside this module.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open MeasureTheory
open scoped BigOperators Real

/-! ### Cartesian algebra helpers -/

/-- The cross product exchanges its arguments up to sign. -/
theorem cross3_antisymm (u v : Fin 3 → ℝ) : cross3 v u = -(cross3 u v) := by
  funext j
  fin_cases j <;> simp [cross3] <;> ring

/-- Negating both arguments of the dot product changes nothing. -/
theorem dot3_neg_neg (u v : Fin 3 → ℝ) : dot3 (-u) (-v) = dot3 u v := by
  simp only [dot3, Pi.neg_apply]
  ring

/-- The dot product of a difference is the difference of the dot products. -/
theorem dot3_sub (n u v : Fin 3 → ℝ) : dot3 n (u - v) = dot3 n u - dot3 n v := by
  simp only [dot3, Pi.sub_apply]
  ring

/-- The linear map given by dotting against a fixed vector. -/
noncomputable def dot3CLM (n : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ i, n i • (ContinuousLinearMap.proj i)

/-- The continuous linear functional evaluates to the Cartesian dot product. -/
theorem dot3CLM_apply (n v : Fin 3 → ℝ) : dot3CLM n v = dot3 n v := by
  simp only [dot3CLM, dot3, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Fin.sum_univ_three]

set_option maxHeartbeats 500000 in
/-- Multiplying the scalar triple product by the squared norm of the normal vector
distributes over the three planarity relations. -/
theorem sumSq_mul_dot3_cross3 (n a b c : Fin 3 → ℝ) :
    (∑ k, n k ^ 2) * dot3 (cross3 a b) c =
      dot3 n a * (∑ k, n k * cross3 b c k) +
      dot3 n b * (∑ k, n k * cross3 c a k) +
      dot3 n c * (∑ k, n k * cross3 a b k) := by
  simp_rw [Fin.sum_univ_three]
  simp only [cross3_apply_zero, cross3_apply_one, cross3_apply_two, dot3]
  ring

/-- If three vectors are all perpendicular to a nonzero vector, their scalar triple
product with the cross product vanishes. -/
theorem dot3_cross3_eq_zero {n a b c : Fin 3 → ℝ} (hn : n ≠ 0)
    (ha : dot3 n a = 0) (hb : dot3 n b = 0) (hc : dot3 n c = 0) :
    dot3 (cross3 a b) c = 0 := by
  have hpos : (0 : ℝ) < ∑ k, n k ^ 2 := by
    rcases eq_or_lt_of_le (Finset.sum_nonneg fun k _ => sq_nonneg (n k)) with h0 | hpos
    · exfalso
      apply hn
      funext k
      have hk := Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (n j)) |>.mp h0.symm k (Finset.mem_univ k)
      exact pow_eq_zero_iff two_ne_zero |>.mp hk
    · exact hpos
  have hcomb := sumSq_mul_dot3_cross3 n a b c
  rw [ha, hb, hc] at hcomb
  simp only [zero_mul, add_zero] at hcomb
  exact (mul_eq_zero.mp hcomb).resolve_left (ne_of_gt hpos)

/-! ### The Gauss kernel and linking integral -/

/-- Euclidean length of a three-vector written as a coordinate function. -/
noncomputable def euclideanLength (v : Fin 3 → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖

/-- Taking the Euclidean length is continuous in the coordinate topology. -/
@[fun_prop]
theorem continuous_euclideanLength : Continuous euclideanLength :=
  (PiLp.continuous_toLp 2 _).norm

/-- The sup norm used for componentwise estimates is bounded by the
Euclidean length used in the Gauss denominator. -/
theorem norm_le_euclideanLength (v : Fin 3 → ℝ) : ‖v‖ ≤ euclideanLength v := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)) i

/-- Negation preserves Euclidean length. -/
theorem euclideanLength_neg (v : Fin 3 → ℝ) : euclideanLength (-v) = euclideanLength v := by
  simp [euclideanLength]

/-- The Euclidean chord length is independent of the order of its endpoints. -/
theorem euclideanLength_sub_rev (v w : Fin 3 → ℝ) :
    euclideanLength (v - w) = euclideanLength (w - v) := by
  rw [← neg_sub w v, euclideanLength_neg]

/-- Multiplying a vector by a real scalar scales Euclidean length by its
absolute value. -/
theorem euclideanLength_smul (c : ℝ) (v : Fin 3 → ℝ) :
    euclideanLength (c • v) = |c| * euclideanLength v := by
  rw [euclideanLength, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
  rfl

/-- The Gauss linking kernel of two parametrized curves at a pair of parameters. -/
noncomputable def gaussKernel (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (s t : ℝ) : ℝ :=
  dot3 (cross3 (deriv γ₁ s) (deriv γ₂ t)) (γ₁ s - γ₂ t)
    / (4 * π * euclideanLength (γ₁ s - γ₂ t) ^ 3)

/-- The Gauss kernel is symmetric under the simultaneous exchange of curves and
parameters. -/
theorem gaussKernel_swap (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (s t : ℝ) :
    gaussKernel γ₁ γ₂ s t = gaussKernel γ₂ γ₁ t s := by
  simp only [gaussKernel]
  rw [cross3_antisymm (deriv γ₂ t) (deriv γ₁ s), ← neg_sub (γ₂ t) (γ₁ s), dot3_neg_neg,
    euclideanLength_neg]

/-- The parameter square of the closed-curve normalization. -/
def gaussDomain : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) (2 * π) ×ˢ Set.Icc (0 : ℝ) (2 * π)

/-- The product of the two restricted parameter measures. -/
noncomputable def gaussMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) (2 * π))).prod
    (volume.restrict (Set.Icc (0 : ℝ) (2 * π)))

/-- The Gauss linking integral of two closed curves, as the Lebesgue integral of the
kernel over the parameter square `[0, 2π] × [0, 2π]`. -/
noncomputable def gaussLinking (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) : ℝ :=
  ∫ p, gaussKernel γ₁ γ₂ p.1 p.2 ∂gaussMeasure

/-- The Gauss kernel of two disjoint `C¹` curves is continuous in both parameters. -/
theorem continuous_gaussKernel (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (h₁ : ContDiff ℝ 1 γ₁)
    (h₂ : ContDiff ℝ 1 γ₂) (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) :
    Continuous fun p : ℝ × ℝ => gaussKernel γ₁ γ₂ p.1 p.2 := by
  have hd1 : Continuous (deriv γ₁) := ContDiff.continuous_deriv h₁ (by norm_num)
  have hd2 : Continuous (deriv γ₂) := ContDiff.continuous_deriv h₂ (by norm_num)
  have hc1 : Continuous γ₁ := h₁.continuous
  have hc2 : Continuous γ₂ := h₂.continuous
  have hne : ∀ p : ℝ × ℝ, (4 : ℝ) * π * euclideanLength (γ₁ p.1 - γ₂ p.2) ^ 3 ≠ 0 := by
    intro p
    have hst : γ₁ p.1 - γ₂ p.2 ≠ 0 := sub_ne_zero.mpr (hdisj p.1 p.2)
    have hlen : 0 < euclideanLength (γ₁ p.1 - γ₂ p.2) :=
      (norm_pos_iff.mpr hst).trans_le (norm_le_euclideanLength _)
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (pow_ne_zero 3 hlen.ne')
  simp only [gaussKernel, dot3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
  fun_prop

/-- The Gauss kernel of two disjoint `C¹` curves is integrable on the parameter square. -/
theorem integrable_gaussKernel (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (h₁ : ContDiff ℝ 1 γ₁)
    (h₂ : ContDiff ℝ 1 γ₂) (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) :
    Integrable (fun p : ℝ × ℝ => gaussKernel γ₁ γ₂ p.1 p.2) gaussMeasure := by
  have hcont := continuous_gaussKernel γ₁ γ₂ h₁ h₂ hdisj
  have h1 : Integrable (fun p : ℝ × ℝ => gaussKernel γ₁ γ₂ p.1 p.2)
      ((volume.prod (volume : Measure ℝ)).restrict gaussDomain) :=
    hcont.continuousOn.integrableOn_compact
      (IsCompact.prod (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π))
        (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)))
  simp only [gaussDomain] at h1
  rw [← Measure.prod_restrict] at h1
  exact h1

/-- The Gauss linking integral is symmetric in its two curve arguments. -/
theorem gaussLinking_symm (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (h₁ : ContDiff ℝ 1 γ₁)
    (h₂ : ContDiff ℝ 1 γ₂) (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) :
    gaussLinking γ₁ γ₂ = gaussLinking γ₂ γ₁ := by
  have hint := integrable_gaussKernel γ₁ γ₂ h₁ h₂ hdisj
  have hmap : Measure.map Prod.swap gaussMeasure = gaussMeasure :=
    (Measure.measurePreserving_swap
      (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π)))
      (ν := volume.restrict (Set.Icc (0 : ℝ) (2 * π)))).2
  have hc2 : Continuous fun p : ℝ × ℝ => gaussKernel γ₂ γ₁ p.1 p.2 :=
    continuous_gaussKernel γ₂ γ₁ h₂ h₁ fun s t => (hdisj t s).symm
  have hg2 : AEStronglyMeasurable (fun p : ℝ × ℝ => gaussKernel γ₂ γ₁ p.2 p.1)
      (Measure.map Prod.swap gaussMeasure) :=
    (hc2.stronglyMeasurable.comp_measurable measurable_swap).aestronglyMeasurable
  calc gaussLinking γ₁ γ₂
      = ∫ p, gaussKernel γ₁ γ₂ p.1 p.2 ∂gaussMeasure := rfl
    _ = ∫ p, gaussKernel γ₂ γ₁ p.2 p.1 ∂gaussMeasure :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun p => gaussKernel_swap γ₁ γ₂ p.1 p.2)
    _ = ∫ p, gaussKernel γ₂ γ₁ p.1 p.2 ∂gaussMeasure := by
      conv_lhs => rw [← hmap]
      exact integral_map measurable_swap.aemeasurable hg2
    _ = gaussLinking γ₂ γ₁ := rfl

/-! ### Coplanar curves have vanishing linking integral -/

/-- The tangent of a curve contained in an affine plane is perpendicular to the plane
normal. -/
theorem dot3_deriv_eq_zero_of_planar {γ : ℝ → (Fin 3 → ℝ)} {n : Fin 3 → ℝ} {c : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hper : ∀ s, dot3 n (γ s) = c) (s : ℝ) :
    dot3 n (deriv γ s) = 0 := by
  have hcomp : HasFDerivAt (fun u => dot3CLM n (γ u))
      ((dot3CLM n).comp (fderiv ℝ γ s)) s :=
    (dot3CLM n).hasFDerivAt.comp s
      ((hγ.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt)
  have hfun : (fun u => dot3CLM n (γ u)) = fun _ => c := by
    funext u
    rw [dot3CLM_apply, hper u]
  rw [hfun] at hcomp
  have hzero : (0 : ℝ →L[ℝ] ℝ) = (dot3CLM n).comp (fderiv ℝ γ s) :=
    (hasFDerivAt_const c s).unique hcomp
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L (1 : ℝ)) hzero
  simpa [dot3CLM_apply] using h1.symm

/-- Two closed curves lying in a common affine plane have vanishing Gauss linking
integral. This is the analytic core of the classical fact that coplanar curves are
unlinked; no topological theorem is invoked and no disjointness is needed, since the
kernel vanishes identically. -/
theorem gaussLinking_coplanar_eq_zero (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (n : Fin 3 → ℝ)
    (hn : n ≠ 0) (c : ℝ) (hper₁ : ∀ s, dot3 n (γ₁ s) = c) (hper₂ : ∀ t, dot3 n (γ₂ t) = c)
    (hc₁ : ContDiff ℝ 1 γ₁) (hc₂ : ContDiff ℝ 1 γ₂) :
    gaussLinking γ₁ γ₂ = 0 := by
  have hzero : ∀ s t : ℝ, gaussKernel γ₁ γ₂ s t = 0 := by
    intro s t
    have hnum : dot3 (cross3 (deriv γ₁ s) (deriv γ₂ t)) (γ₁ s - γ₂ t) = 0 :=
      dot3_cross3_eq_zero hn
        (dot3_deriv_eq_zero_of_planar hc₁ hper₁ s)
        (dot3_deriv_eq_zero_of_planar hc₂ hper₂ t)
        (by rw [dot3_sub, hper₁ s, hper₂ t]; ring)
    simp [gaussKernel, hnum]
  have hfun : (fun p : ℝ × ℝ => gaussKernel γ₁ γ₂ p.1 p.2) = fun _ => 0 :=
    funext fun p => hzero p.1 p.2
  simp only [gaussLinking, hfun]
  simp

/-! ### The Gauss-based pairwise linking assembly -/

/-- The circulation-weighted sum of pairwise Gauss linking integrals of a finite family of
closed curves; this instantiates the public `linkingPart` with actual Gauss integrals. -/
noncomputable def pairLinkingGauss {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) : ℝ :=
  linkingPart κ (fun i j => gaussLinking (γ i) (γ j))

/-- Unfolding the Gauss-based pairwise linking sum into the explicit off-diagonal double
sum. -/
theorem pairLinkingGauss_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) :
    pairLinkingGauss κ γ = ∑ i, ∑ j, if i = j then 0 else
      κ i * κ j * gaussLinking (γ i) (γ j) := by
  simp [pairLinkingGauss, linkingPart]

/-- The Gauss linking matrix of a pairwise disjoint family of `C¹` curves is
symmetric. -/
theorem gaussLinking_matrix_symm {ι : Type*} (γ : ι → ℝ → (Fin 3 → ℝ))
    (hγ : ∀ i, ContDiff ℝ 1 (γ i))
    (hdisj : ∀ i j, ∀ s t, γ i s ≠ γ j t) (i j : ι) :
    gaussLinking (γ i) (γ j) = gaussLinking (γ j) (γ i) :=
  gaussLinking_symm (γ i) (γ j) (hγ i) (hγ j) (hdisj i j)

/-- The circulation-weighted pairwise Gauss linking sum of a family of `C¹` curves all
contained in one common affine plane vanishes: every pairwise integral already vanishes,
independently of the circulations. -/
theorem pairLinkingGauss_coplanar_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) (n : Fin 3 → ℝ) (hn : n ≠ 0) (c : ℝ)
    (hper : ∀ i s, dot3 n (γ i s) = c) (hc : ∀ i, ContDiff ℝ 1 (γ i)) :
    pairLinkingGauss κ γ = 0 := by
  have hzero : ∀ i j, gaussLinking (γ i) (γ j) = 0 := fun i j =>
    gaussLinking_coplanar_eq_zero (γ i) (γ j) n hn c (hper i) (hper j) (hc i) (hc j)
  simp [pairLinkingGauss, linkingPart, hzero]

/-! ### Invariance under common translations and dilations -/

/-- Scaling the first argument of the dot product factors out. -/
theorem dot3_smul_left (c : ℝ) (u v : Fin 3 → ℝ) : dot3 (c • u) v = c * dot3 u v := by
  simp only [dot3, Pi.smul_apply]
  ring

/-- Scaling the second argument of the dot product factors out. -/
theorem dot3_smul_right (c : ℝ) (u v : Fin 3 → ℝ) : dot3 u (c • v) = c * dot3 u v := by
  simp only [dot3, Pi.smul_apply]
  ring

/-- Scaling both arguments of the cross product scales it by the square. -/
theorem cross3_const_smul (c : ℝ) (u w : Fin 3 → ℝ) :
    cross3 (c • u) (c • w) = c ^ 2 • cross3 u w := by
  funext j
  fin_cases j <;> simp [cross3] <;> ring

/-- Common translations do not change the Gauss linking integral: the linking of two curves
is a quantity of their relative geometry. -/
theorem gaussLinking_trans_eq (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (v : Fin 3 → ℝ)
    (h₁ : ContDiff ℝ 1 γ₁) (h₂ : ContDiff ℝ 1 γ₂) :
    gaussLinking (fun s => γ₁ s + v) (fun s => γ₂ s + v) = gaussLinking γ₁ γ₂ := by
  have hd1 : ∀ x, deriv (fun s => γ₁ s + v) x = deriv γ₁ x := by
    intro x
    have h : HasDerivAt (fun s => γ₁ s + v) (deriv γ₁ x) x :=
      HasDerivAt.add_const v ((h₁.contDiffAt.differentiableAt (by norm_num)).hasDerivAt)
    exact h.deriv
  have hd2 : ∀ x, deriv (fun s => γ₂ s + v) x = deriv γ₂ x := by
    intro x
    have h : HasDerivAt (fun s => γ₂ s + v) (deriv γ₂ x) x :=
      HasDerivAt.add_const v ((h₂.contDiffAt.differentiableAt (by norm_num)).hasDerivAt)
    exact h.deriv
  have hk : ∀ p : ℝ × ℝ, gaussKernel (fun s => γ₁ s + v) (fun s => γ₂ s + v) p.1 p.2
      = gaussKernel γ₁ γ₂ p.1 p.2 := by
    intro p
    simp only [gaussKernel, hd1 p.1, hd2 p.2]
    rw [show γ₁ p.1 + v - (γ₂ p.2 + v) = γ₁ p.1 - γ₂ p.2 from by ring]
  simp only [gaussLinking]
  exact integral_congr_ae (Filter.Eventually.of_forall hk)

/-- Common positive dilations do not change the Gauss linking integral. A common negative
scaling reverses the orientation of space and flips the sign of the integral, which is why
positivity is a hypothesis. -/
theorem gaussLinking_const_smul_eq (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) {c : ℝ} (hc : 0 < c)
    (h₁ : ContDiff ℝ 1 γ₁) (h₂ : ContDiff ℝ 1 γ₂) :
    gaussLinking (fun s => c • γ₁ s) (fun s => c • γ₂ s) = gaussLinking γ₁ γ₂ := by
  have hd1 : ∀ x, deriv (fun s => c • γ₁ s) x = c • deriv γ₁ x := by
    intro x
    have h : HasDerivAt (fun s => c • γ₁ s) (c • deriv γ₁ x) x :=
      HasDerivAt.const_smul c ((h₁.contDiffAt.differentiableAt (by norm_num)).hasDerivAt)
    exact h.deriv
  have hd2 : ∀ x, deriv (fun s => c • γ₂ s) x = c • deriv γ₂ x := by
    intro x
    have h : HasDerivAt (fun s => c • γ₂ s) (c • deriv γ₂ x) x :=
      HasDerivAt.const_smul c ((h₂.contDiffAt.differentiableAt (by norm_num)).hasDerivAt)
    exact h.deriv
  have hk : ∀ p : ℝ × ℝ, gaussKernel (fun s => c • γ₁ s) (fun s => c • γ₂ s) p.1 p.2
      = gaussKernel γ₁ γ₂ p.1 p.2 := by
    intro p
    simp only [gaussKernel, hd1 p.1, hd2 p.2, ← smul_sub, cross3_const_smul, dot3_smul_left,
      dot3_smul_right, euclideanLength_smul, abs_of_pos hc, mul_pow]
    field_simp
  simp only [gaussLinking]
  exact integral_congr_ae (Filter.Eventually.of_forall hk)

/-- The centerline helicity of a geometric bundle: the public algebra instantiated with
actual Gauss linking integrals of the curves; the writhes remain real input data. -/
noncomputable def centerlineHelicityGauss {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) (wr : ι → ℝ) : ℝ :=
  centerlineHelicity κ (fun i j => gaussLinking (γ i) (γ j)) wr

/-- The geometric centerline helicity splits into the pairwise Gauss linking sum and the
self writhe term, exactly as in Eq. (6) of the paper. -/
theorem centerlineHelicityGauss_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) (wr : ι → ℝ) :
    centerlineHelicityGauss κ γ wr = pairLinkingGauss κ γ + writhePart κ wr := by
  simp [centerlineHelicityGauss, pairLinkingGauss, centerlineHelicity]

/-- For a bundle of curves in one common affine plane, the linking contribution to the
centerline helicity vanishes identically: all of the (non-topological) remainder is the
self writhe term. This is the analytic core of the paper's statement that coplanar
vortices carry no mutual linking. -/
theorem centerlineHelicityGauss_coplanar_eq_writhe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) (n : Fin 3 → ℝ) (hn : n ≠ 0) (c : ℝ)
    (hper : ∀ i s, dot3 n (γ i s) = c) (hc : ∀ i, ContDiff ℝ 1 (γ i)) (wr : ι → ℝ) :
    centerlineHelicityGauss κ γ wr = writhePart κ wr := by
  rw [centerlineHelicityGauss_eq,
    pairLinkingGauss_coplanar_eq_zero κ γ n hn c hper hc, zero_add]

/-- Common positive dilation of a geometric bundle leaves its centerline helicity
unchanged, because every pairwise Gauss linking integral is dilation invariant. -/
theorem centerlineHelicityGauss_const_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) {c : ℝ} (hc : 0 < c)
    (hγ : ∀ i, ContDiff ℝ 1 (γ i)) (wr : ι → ℝ) :
    centerlineHelicityGauss κ (fun i s => c • γ i s) wr = centerlineHelicityGauss κ γ wr := by
  have hlk : (fun i j => gaussLinking (fun s => c • γ i s) (fun s => c • γ j s))
      = fun i j => gaussLinking (γ i) (γ j) := by
    funext i j
    exact gaussLinking_const_smul_eq (γ i) (γ j) hc (hγ i) (hγ j)
  simp only [centerlineHelicityGauss, hlk]

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
