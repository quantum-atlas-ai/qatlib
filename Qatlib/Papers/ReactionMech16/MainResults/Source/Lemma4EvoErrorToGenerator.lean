/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4: evolution error controls the generator gap

Source: arXiv:1605.03590v2, Appendix D, Lemma 4 (p.14).

If `‖e^{-iAt} - e^{-iBt}‖₂ ≤ t γ(t)` for a non-decreasing continuous `γ` on
`[0, ∞)`, then `‖A - B‖₂ ≤ γ(t)` for every `t ≥ 0`.

The proof differentiates the matrix exponential at `t = 0`:
`(e^{-iAt} - e^{-iBt}) / t → -i(A - B)`, so the norm of the difference quotient
tends to `‖A - B‖`.  Dividing the hypothesis by `t > 0` and passing to the
right-sided limit gives `‖A - B‖ ≤ γ(0)`, and monotonicity of `γ` upgrades this
to every `t ≥ 0`.

The auxiliary lemmas in this file record the unitarity of `e^{-iHt}` for
Hermitian `H` and the `1`-Lipschitz estimate for the exponential of
anti-Hermitian matrices, which are reused by the Strang-product perturbation
bound in `Theorem1TrotterEnergyError`.

Fixed source: arXiv:1605.03590v2 (2016), Lemma 4, p.14.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped Matrix.Norms.L2Operator ComplexOrder Topology

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- Matrix exponential evolution `e^{-iAt}` used throughout Appendix D. -/
noncomputable def matrixExpEvo {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • A)

/-- The generator `-i t A` of `matrixExpEvo A t` is anti-Hermitian when `A` is
Hermitian. -/
lemma expEvo_antiherm {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (s : ℝ) :
    ((-(Complex.I * (s : ℂ))) • H)ᴴ = -((-(Complex.I * (s : ℂ))) • H) := by
  calc
    ((-(Complex.I * (s : ℂ))) • H)ᴴ = star (-(Complex.I * (s : ℂ))) • Hᴴ := by
      rw [conjTranspose_smul]
    _ = (Complex.I * (s : ℂ)) • H := by
      rw [show Hᴴ = H from hH]
      congr 1
      simp [Complex.conj_I, mul_comm]
    _ = -((-(Complex.I * (s : ℂ))) • H) := by rw [neg_smul, neg_neg]

/-- The exponential of an anti-Hermitian matrix is unitary (with respect to the
L2 operator norm). -/
lemma exp_mem_unitary_of_antiherm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {X : Matrix I I ℂ} (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ unitary (Matrix I I ℂ) := by
  rw [Unitary.mem_iff]
  constructor
  · calc
      star (NormedSpace.exp X) * NormedSpace.exp X
          = (NormedSpace.exp X)ᴴ * NormedSpace.exp X := by
            rw [Matrix.star_eq_conjTranspose]
      _ = NormedSpace.exp Xᴴ * NormedSpace.exp X := by
            rw [← Matrix.exp_conjTranspose]
      _ = NormedSpace.exp (-X) * NormedSpace.exp X := by rw [hX]
      _ = NormedSpace.exp (-X + X) := by
            rw [← Matrix.exp_add_of_commute (-X) X (Commute.refl X).neg_left]
      _ = 1 := by simp
  · calc
      NormedSpace.exp X * star (NormedSpace.exp X)
          = NormedSpace.exp X * (NormedSpace.exp X)ᴴ := by
            rw [Matrix.star_eq_conjTranspose]
      _ = NormedSpace.exp X * NormedSpace.exp Xᴴ := by
            rw [← Matrix.exp_conjTranspose]
      _ = NormedSpace.exp X * NormedSpace.exp (-X) := by rw [hX]
      _ = NormedSpace.exp (X + -X) := by
            rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right]
      _ = 1 := by simp

/-- The exponential of an anti-Hermitian matrix has operator norm one. -/
lemma norm_exp_antiherm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {X : Matrix I I ℂ} (hX : Xᴴ = -X) :
    ‖NormedSpace.exp X‖ = 1 :=
  CStarRing.norm_coe_unitary ⟨NormedSpace.exp X, exp_mem_unitary_of_antiherm hX⟩

/-- For Hermitian `H`, the evolution `e^{-iHt}` has operator norm one. -/
lemma norm_expEvo {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (s : ℝ) :
    ‖matrixExpEvo H s‖ = 1 :=
  norm_exp_antiherm (expEvo_antiherm H hH s)

/-- Real multiples of an anti-Hermitian matrix are anti-Hermitian. -/
lemma norm_exp_smul_antiherm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {X : Matrix I I ℂ} (hX : Xᴴ = -X) (u : ℝ) :
    ‖NormedSpace.exp (u • X)‖ = 1 := by
  apply norm_exp_antiherm
  rw [conjTranspose_smul, hX]
  simp [smul_neg]

/-- The matrix exponential is `1`-Lipschitz on the anti-Hermitian generators:
`‖e^{-iAt} - e^{-iBt}‖ ≤ ‖A - B‖ |t|`. -/
lemma norm_expEvo_sub_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H H' : Matrix I I ℂ) (hH : H.IsHermitian) (hH' : H'.IsHermitian) (s : ℝ) :
    ‖matrixExpEvo H s - matrixExpEvo H' s‖ ≤ ‖H - H'‖ * |s| := by
  let X : Matrix I I ℂ := (-(Complex.I * (s : ℂ))) • H
  let Y : Matrix I I ℂ := (-(Complex.I * (s : ℂ))) • H'
  have hX : Xᴴ = -X := expEvo_antiherm H hH s
  have hY : Yᴴ = -Y := expEvo_antiherm H' hH' s
  let P : ℝ → Matrix I I ℂ := fun u =>
    NormedSpace.exp (u • X) * NormedSpace.exp ((1 - u) • Y)
  have hP0 : P 0 = matrixExpEvo H' s := by
    simp [P, Y, matrixExpEvo]
  have hP1 : P 1 = matrixExpEvo H s := by
    simp [P, X, matrixExpEvo]
  have hderiv : ∀ u : ℝ, HasDerivAt P
      ((NormedSpace.exp (u • X) * X) * NormedSpace.exp ((1 - u) • Y) +
        NormedSpace.exp (u • X) * (-(NormedSpace.exp ((1 - u) • Y) * Y))) u := by
    intro u
    have hf : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
        (NormedSpace.exp (u • X) * X) u := hasDerivAt_exp_smul_const X u
    have hg : HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • Y))
        (-(NormedSpace.exp ((1 - u) • Y) * Y)) u := by
      have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub 1
      have h2 : HasDerivAt (fun v : ℝ => NormedSpace.exp (v • Y))
          (NormedSpace.exp ((1 - u) • Y) * Y) (1 - u) := hasDerivAt_exp_smul_const Y (1 - u)
      convert h2.scomp (x := u) h1 using 1 <;> first | rfl | simp [Function.comp]
    exact hf.mul hg
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      ‖(NormedSpace.exp (u • X) * X) * NormedSpace.exp ((1 - u) • Y) +
        NormedSpace.exp (u • X) * (-(NormedSpace.exp ((1 - u) • Y) * Y))‖
        ≤ ‖X - Y‖ := by
    intro u hu
    have hcomm : Commute (NormedSpace.exp ((1 - u) • Y)) Y :=
      ((Commute.refl Y).smul_left (1 - u)).exp_left
    have hBY : NormedSpace.exp ((1 - u) • Y) * Y = Y * NormedSpace.exp ((1 - u) • Y) := hcomm.eq
    have hAX : ‖NormedSpace.exp (u • X)‖ = 1 := norm_exp_smul_antiherm hX u
    have hAY : ‖NormedSpace.exp ((1 - u) • Y)‖ = 1 := norm_exp_smul_antiherm hY (1 - u)
    have hrewrite :
        (NormedSpace.exp (u • X) * X) * NormedSpace.exp ((1 - u) • Y) +
          NormedSpace.exp (u • X) * (-(NormedSpace.exp ((1 - u) • Y) * Y)) =
        NormedSpace.exp (u • X) * (X - Y) * NormedSpace.exp ((1 - u) • Y) := by
      rw [hBY]
      noncomm_ring
    rw [hrewrite]
    calc
      ‖NormedSpace.exp (u • X) * (X - Y) * NormedSpace.exp ((1 - u) • Y)‖
          ≤ ‖NormedSpace.exp (u • X) * (X - Y)‖ *
              ‖NormedSpace.exp ((1 - u) • Y)‖ := norm_mul_le _ _
      _ ≤ (‖NormedSpace.exp (u • X)‖ * ‖X - Y‖) * 1 := by
            rw [hAY]
            simpa using norm_mul_le (NormedSpace.exp (u • X)) (X - Y)
      _ = ‖X - Y‖ := by rw [hAX]; ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := P) (f' := fun u =>
      (NormedSpace.exp (u • X) * X) * NormedSpace.exp ((1 - u) • Y) +
        NormedSpace.exp (u • X) * (-(NormedSpace.exp ((1 - u) • Y) * Y)))
    (fun u _ => (hderiv u).hasDerivWithinAt) hbound
  rw [hP1, hP0] at hmvt
  have hXY : ‖X - Y‖ = ‖H - H'‖ * |s| := by
    have hsub : X - Y = (-(Complex.I * (s : ℂ))) • (H - H') := by
      simp [X, Y, smul_sub]
    rw [hsub, norm_smul]
    have hc : ‖(-(Complex.I * (s : ℂ)))‖ = |s| := by
      simp
    rw [hc, mul_comm]
  rw [hXY] at hmvt
  exact hmvt

/-- Real derivative of the matrix exponential evolution at time zero:
`d/dt e^{-iAt}|_{t=0} = -i A`. -/
lemma hasDerivAt_expEvo {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    HasDerivAt (fun u : ℝ => matrixExpEvo A u) ((-Complex.I) • A) 0 := by
  have h := hasDerivAt_exp_smul_const ((-Complex.I) • A) (0 : ℝ)
  convert h using 1
  · ext u
    simp only [matrixExpEvo]
    rw [show (-(Complex.I * (u : ℂ))) = (u : ℂ) * (-Complex.I) by ring]
    rw [← smul_assoc, Complex.real_smul]
  · simp

/-- arXiv:1605.03590v2, Lemma 4 (p.14): if two Hermitian Hamiltonians `A` and `B`
generate evolutions that agree to order `t γ(t)`, with `γ` non-decreasing and
continuous on `[0, ∞)`, then `‖A - B‖₂ ≤ γ(t)` for every `t ≥ 0`. -/
theorem lemma4_evo_error_to_generator_gap
    {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (_hA : A.IsHermitian) (_hB : B.IsHermitian)
    (γ : ℝ → ℝ) (hγmono : MonotoneOn γ (Set.Ici 0))
    (hγcont : ContinuousOn γ (Set.Ici 0))
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖matrixExpEvo A t - matrixExpEvo B t‖ ≤ t * γ t) :
    ∀ t : ℝ, 0 ≤ t → ‖A - B‖ ≤ γ t := by
  have hderiv : HasDerivAt (fun u : ℝ => matrixExpEvo A u - matrixExpEvo B u)
      ((-Complex.I) • A - (-Complex.I) • B) 0 :=
    (hasDerivAt_expEvo A).sub (hasDerivAt_expEvo B)
  have hslope := hderiv.tendsto_slope_zero_right (x := 0)
  have hslope' : Tendsto (fun h : ℝ => h⁻¹ • (matrixExpEvo A h - matrixExpEvo B h))
      (𝓝[>] 0) (𝓝 ((-Complex.I) • A - (-Complex.I) • B)) := by
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [matrixExpEvo]
  have hnorm : Tendsto (fun h : ℝ => ‖h⁻¹ • (matrixExpEvo A h - matrixExpEvo B h)‖)
      (𝓝[>] 0) (𝓝 ‖(-Complex.I) • A - (-Complex.I) • B‖) :=
    hslope'.norm
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝 (γ 0)) :=
    (hγcont.continuousWithinAt (by simp : (0:ℝ) ∈ Set.Ici 0)).mono_left
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hev : ∀ᶠ h in 𝓝[>] 0,
      ‖h⁻¹ • (matrixExpEvo A h - matrixExpEvo B h)‖ ≤ γ h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hhpos : 0 < h := hh
    have hb := hbound h hh.le
    calc
      ‖h⁻¹ • (matrixExpEvo A h - matrixExpEvo B h)‖
          = h⁻¹ * ‖matrixExpEvo A h - matrixExpEvo B h‖ := by
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
      _ ≤ h⁻¹ * (h * γ h) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
      _ = γ h := by field_simp
  have hlim := le_of_tendsto_of_tendsto hnorm hγ hev
  have hnormAB : ‖(-Complex.I) • A - (-Complex.I) • B‖ = ‖A - B‖ := by
    have : (-Complex.I) • A - (-Complex.I) • B = (-Complex.I) • (A - B) := by
      rw [smul_sub]
    rw [this, norm_smul]
    simp
  rw [hnormAB] at hlim
  intro t ht
  exact hlim.trans (hγmono (by simp) (by simpa using ht) ht)

end Qatlib.Papers.ReactionMech16.MainResults.Source
