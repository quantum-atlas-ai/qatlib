/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

set_option backward.isDefEq.respectTransparency false

/-!
# WaveEquation17.MainResults.PerturbationCore

Fixed arXiv:1711.05394v4 (Costa--Jordan--Ostrander, *Quantum Algorithm for Simulating
the Wave Equation*, Phys. Rev. A 99, 012323 (2019)).

This module formalises the analytic core of Theorem 2 (source equations (56)--(58),
proof (59)--(81)) in the finite-dimensional lattice representation used throughout the
paper: the continuum fields `φ, ψ₁, ..., ψ_d` are vectors of a complex inner product
space, and the differential operators are bounded self-adjoint endomorphisms.

The source hypotheses are:

* `H0` is the Hermitian wave operator of (60), i.e. the operator appearing in
  `dSλ/dt = -i Hλ Sλ` with `Hλ = H0 + λ HD` (62)--(63);
* `HD` is the Hermitian operator `D` of (61), acting blockwise as `diag(D, -D, ..., -D)`;
* the paper proves that `HD⁺ = diag(D, ..., D)` commutes with `H0` (72)--(73), hence
  `HD` commutes with `H0` as well;
* `Sε` and `S0` are the two solutions with the same initial state (65).

Equation (80) is the statement `perturbation_norm_bound`.  The component estimate (57)
is the corollary `theorem2_component_bound`, and `theorem2_wave_perturbation` records the
paper's commuting-operator form where the size of `HD S0(t)` is conserved by the flow.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate

namespace Qatlib.Papers.WaveEquation17.MainResults

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A bounded complex-linear operator is self-adjoint when it can be moved across the
inner product.  This is the finite-dimensional form of the Hermitian operators in the
source: `H0` is the wave operator of (60), `HD` the operator `D` of (61), and the
Laplacian of Theorem 3 is self-adjoint under Dirichlet or Neumann conditions. -/
def IsSelfAdjointCLM (H : E →L[ℂ] E) : Prop :=
  ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y)

/-- The quadratic form of a self-adjoint operator is real: the imaginary part of
`⟪x, H x⟫` vanishes.  This is the spectral fact used implicitly after (62) to show that
`Hλ` generates a norm-preserving flow. -/
lemma im_inner_self_of_selfAdjoint {H : E →L[ℂ] E} (hH : IsSelfAdjointCLM H) (x : E) :
    (inner ℂ x (H x)).im = 0 := by
  have hconj : starRingEnd ℂ (inner ℂ x (H x)) = inner ℂ x (H x) := by
    rw [inner_conj_symm]
    rw [hH x x]
  exact Complex.conj_eq_iff_im.mp hconj

/-- Applying a self-adjoint operator against `-i` contributes no real part:
`Re ⟪x, -i H x⟫ = 0`.  This is the infinitesimal form of norm conservation for the
Schrödinger-type flow of (63). -/
lemma re_inner_negI_smul_self {H : E →L[ℂ] E} (hH : IsSelfAdjointCLM H) (x : E) :
    (inner ℂ x (-(Complex.I) • H x)).re = 0 := by
  rw [inner_smul_right, neg_mul, Complex.neg_re, Complex.I_mul_re]
  simp [im_inner_self_of_selfAdjoint hH x]

/-- The perturbation operator `H0 + ε HD` is self-adjoint whenever `H0` and `HD` are,
so its quadratic form again has no `-i` real part.  This is the step that makes
`‖Sε(t)‖` time-independent in the proof of Theorem 2. -/
lemma re_inner_negI_add {H0 H1 : E →L[ℂ] E} (hH0 : IsSelfAdjointCLM H0)
    (hH1 : IsSelfAdjointCLM H1) (ε : ℝ) (x : E) :
    (inner ℂ x (-(Complex.I) • (H0 x + (ε : ℂ) • H1 x))).re = 0 := by
  rw [inner_smul_right, inner_add_right, inner_smul_right]
  rw [neg_mul, Complex.neg_re, Complex.mul_re]
  simp [Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    im_inner_self_of_selfAdjoint hH0 x, im_inner_self_of_selfAdjoint hH1 x]

/-- Derivative of the squared norm of a curve in a complex inner product space:
`d/dt ‖S(t)‖² = 2 Re ⟪S(t), S'(t)⟫`.  This is the calculus input for the norm-preservation
argument following (70). -/
lemma hasDerivAt_norm_sq_of_hasDerivAt {S : ℝ → E} {S' : E} {t : ℝ}
    (hS : HasDerivAt S S' t) :
    HasDerivAt (fun τ => ‖S τ‖ ^ 2) (2 * (inner ℂ (S t) S').re) t := by
  have h : HasDerivAt (fun τ => inner ℂ (S τ) (S τ))
      (inner ℂ (S t) S' + inner ℂ S' (S t)) t :=
    HasDerivAt.inner ℂ hS hS
  have hre : HasDerivAt (fun τ => (inner ℂ (S τ) (S τ)).re)
      ((inner ℂ (S t) S' + inner ℂ S' (S t)).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hsq : (fun τ => ‖S τ‖ ^ 2) = fun τ => (inner ℂ (S τ) (S τ)).re := by
    funext τ
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (S τ)).symm
  rw [hsq]
  have hc : inner ℂ S' (S t) = starRingEnd ℂ (inner ℂ (S t) S') := by
    rw [inner_conj_symm]
  have hval : (inner ℂ (S t) S' + inner ℂ S' (S t)).re
      = 2 * (inner ℂ (S t) S').re := by
    rw [Complex.add_re, hc, Complex.conj_re]
    ring
  rwa [hval] at hre

/-- The norm of a solution of `S' = -i H S` with `H` self-adjoint is constant in time.
This is used twice in the source: for `Sε` and `S0` in (71), and for the projected
operator norms in (72)--(75). -/
lemma norm_sq_const_of_deriv_zero (S : ℝ → E) (H : E →L[ℂ] E)
    (hH : IsSelfAdjointCLM H)
    (hS : ∀ t, HasDerivAt S (-(Complex.I) • H (S t)) t) :
    ∀ t, ‖S t‖ ^ 2 = ‖S 0‖ ^ 2 := by
  let g : ℝ → ℝ := fun τ => ‖S τ‖ ^ 2
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h := hasDerivAt_norm_sq_of_hasDerivAt (hS t)
    convert h using 1
    rw [re_inner_negI_smul_self hH]
    ring
  have hconst : ∀ t, g t = g 0 := by
    intro t
    exact is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt)
      (fun x => (hg x).deriv) t 0
  intro t
  exact hconst t

omit [InnerProductSpace ℂ E] in
/-- The norm of a curve is constant whenever its squared norm has zero derivative.
This packages the square-root step used to read (71) as `‖Sε(t)‖ = ‖Sε(0)‖`. -/
lemma norm_eq_of_norm_sq_eq (S : ℝ → E) (h : ∀ t, ‖S t‖ ^ 2 = ‖S 0‖ ^ 2) :
    ∀ t, ‖S t‖ = ‖S 0‖ := by
  intro t
  have hsq := h t
  have := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- Derivative of the overlap `Re ⟪Sε(t), S0(t)⟫` between the perturbed and unperturbed
solutions.  With `Hλ = H0 + λ HD` the two `H0` terms cancel by self-adjointness, leaving
`-ε Im ⟪Sε(t), HD S0(t)⟫`, which is equation (69) of the source. -/
lemma cross_deriv {H0 H1 : E →L[ℂ] E} (hH0 : IsSelfAdjointCLM H0)
    (hH1 : IsSelfAdjointCLM H1) {Sε S0 : ℝ → E} {ε : ℝ}
    (hSε : ∀ t, HasDerivAt Sε (-(Complex.I) • (H0 (Sε t) + (ε : ℂ) • H1 (Sε t))) t)
    (hS0 : ∀ t, HasDerivAt S0 (-(Complex.I) • (H0 (S0 t))) t) (t : ℝ) :
    HasDerivAt (fun τ => (inner ℂ (Sε τ) (S0 τ)).re)
      (-ε * (inner ℂ (Sε t) (H1 (S0 t))).im) t := by
  have h : HasDerivAt (fun τ => inner ℂ (Sε τ) (S0 τ))
      (inner ℂ (Sε t) (-(Complex.I) • (H0 (S0 t))) +
       inner ℂ (-(Complex.I) • (H0 (Sε t) + (ε : ℂ) • H1 (Sε t))) (S0 t)) t :=
    HasDerivAt.inner ℂ (hSε t) (hS0 t)
  have hre : HasDerivAt (fun τ => (inner ℂ (Sε τ) (S0 τ)).re)
      ((inner ℂ (Sε t) (-(Complex.I) • (H0 (S0 t))) +
       inner ℂ (-(Complex.I) • (H0 (Sε t) + (ε : ℂ) • H1 (Sε t))) (S0 t)).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hval : (inner ℂ (Sε t) (-(Complex.I) • (H0 (S0 t))) +
       inner ℂ (-(Complex.I) • (H0 (Sε t) + (ε : ℂ) • H1 (Sε t))) (S0 t)).re
      = -ε * (inner ℂ (Sε t) (H1 (S0 t))).im := by
    simp only [inner_smul_right, inner_smul_left, map_neg]
    simp only [inner_add_left, inner_smul_left]
    rw [hH0 (Sε t) (S0 t), hH1 (Sε t) (S0 t)]
    simp only [Complex.conj_I, Complex.conj_ofReal]
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.neg_im, Complex.add_im, zero_mul, sub_zero, add_zero]
    ring
  rwa [hval] at hre

/-- Source equation (80), the analytic heart of Theorem 2: two solutions of
`S' = -i(H0 + λ H1)S` with the same initial state differ by at most
`√(2 t ε ‖S(0)‖ C)` whenever `‖H1 S0(τ)‖ ≤ C` on `[0,t]`.

The proof is the source's chain (66)--(80): differentiate `‖Sε - S0‖²`, bound the
derivative by `2 ε ‖Sε(0)‖ C` via Cauchy--Schwarz, and integrate over `[0,t]`.
The assumption `Sε(0) = S0(0)` is the initial-condition equality of (65). -/
theorem perturbation_norm_bound {H0 H1 : E →L[ℂ] E}
    (hH0 : IsSelfAdjointCLM H0) (hH1 : IsSelfAdjointCLM H1)
    {Sε S0 : ℝ → E} {ε C t : ℝ}
    (hSε : ∀ τ, HasDerivAt Sε (-(Complex.I) • (H0 (Sε τ) + (ε : ℂ) • H1 (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • (H0 (S0 τ))) τ)
    (hinit : Sε 0 = S0 0)
    (hC : ∀ τ, 0 ≤ τ → ‖H1 (S0 τ)‖ ≤ C)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖Sε t - S0 t‖ ≤ Real.sqrt (2 * t * ε * ‖Sε 0‖ * C) := by
  have hNε : ∀ τ, ‖Sε τ‖ ^ 2 = ‖Sε 0‖ ^ 2 := by
    let g : ℝ → ℝ := fun τ => ‖Sε τ‖ ^ 2
    have hg : ∀ τ, HasDerivAt g 0 τ := by
      intro τ
      have h := hasDerivAt_norm_sq_of_hasDerivAt (hSε τ)
      convert h using 1
      rw [re_inner_negI_add hH0 hH1 ε (Sε τ)]
      ring
    intro τ
    exact is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt)
      (fun x => (hg x).deriv) τ 0
  have hnormε : ∀ τ, ‖Sε τ‖ = ‖Sε 0‖ := norm_eq_of_norm_sq_eq Sε hNε
  let g : ℝ → ℝ := fun τ => ‖Sε τ - S0 τ‖ ^ 2
  have hgeq : g = fun τ =>
      ‖Sε τ‖ ^ 2 + ‖S0 τ‖ ^ 2 - 2 * (inner ℂ (Sε τ) (S0 τ)).re := by
    funext τ
    simp only [g]
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp only [RCLike.re_to_complex]
    ring
  have hgderiv : ∀ τ, HasDerivAt g (-2 * (-ε * (inner ℂ (Sε τ) (H1 (S0 τ))).im)) τ := by
    intro τ
    rw [hgeq]
    have h1 : HasDerivAt (fun τ => ‖Sε τ‖ ^ 2) 0 τ := by
      have h := hasDerivAt_norm_sq_of_hasDerivAt (hSε τ)
      convert h using 1
      rw [re_inner_negI_add hH0 hH1 ε (Sε τ)]
      ring
    have h2 : HasDerivAt (fun τ => ‖S0 τ‖ ^ 2) 0 τ := by
      have h := hasDerivAt_norm_sq_of_hasDerivAt (hS0 τ)
      convert h using 1
      rw [re_inner_negI_smul_self hH0]
      ring
    have h3 := cross_deriv hH0 hH1 hSε hS0 τ
    have h4 : HasDerivAt
        (fun τ => ‖Sε τ‖ ^ 2 + ‖S0 τ‖ ^ 2 - 2 * (inner ℂ (Sε τ) (S0 τ)).re)
        (0 + 0 - 2 * (-ε * (inner ℂ (Sε τ) (H1 (S0 τ))).im)) τ :=
      (h1.add h2).sub (h3.const_mul 2)
    convert h4 using 1
    ring
  have hbound : ∀ τ, 0 ≤ τ → ‖(-2 * (-ε * (inner ℂ (Sε τ) (H1 (S0 τ))).im))‖
      ≤ 2 * ε * ‖Sε 0‖ * C := by
    intro τ hτ
    have hzin : |(inner ℂ (Sε τ) (H1 (S0 τ))).im|
        ≤ ‖inner ℂ (Sε τ) (H1 (S0 τ))‖ :=
      Complex.abs_im_le_norm _
    have hinner : ‖inner ℂ (Sε τ) (H1 (S0 τ))‖ ≤ ‖Sε τ‖ * ‖H1 (S0 τ)‖ :=
      norm_inner_le_norm _ _
    have hH1 : ‖H1 (S0 τ)‖ ≤ C := hC τ hτ
    have hmul : ‖Sε τ‖ * ‖H1 (S0 τ)‖ ≤ ‖Sε 0‖ * C := by
      rw [hnormε τ]
      exact mul_le_mul_of_nonneg_left hH1 (norm_nonneg _)
    have hval : (-2 * (-ε * (inner ℂ (Sε τ) (H1 (S0 τ))).im))
        = 2 * ε * (inner ℂ (Sε τ) (H1 (S0 τ))).im := by ring
    rw [hval, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hε,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hchain : |(inner ℂ (Sε τ) (H1 (S0 τ))).im| ≤ ‖Sε 0‖ * C :=
      le_trans hzin (le_trans hinner hmul)
    nlinarith [hchain, hε, norm_nonneg (Sε 0)]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun τ => -2 * (-ε * (inner ℂ (Sε τ) (H1 (S0 τ))).im))
    (s := Set.Icc (0:ℝ) t) (x := 0) (y := t) (C := 2 * ε * ‖Sε 0‖ * C)
    (fun τ _ => (hgderiv τ).hasDerivWithinAt)
    (fun τ hτ => hbound τ hτ.1)
    (convex_Icc _ _) (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
  have hg0 : g 0 = 0 := by
    simp only [g]
    rw [hinit, sub_self, norm_zero]
    norm_num
  have hgt : 0 ≤ g t := by
    simp only [g]
    positivity
  have hgt_bound : g t ≤ 2 * t * ε * ‖Sε 0‖ * C := by
    have h := hmvt
    rw [hg0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hgt, sub_zero,
      Real.norm_eq_abs, abs_of_nonneg ht] at h
    have hrhs : 2 * ε * ‖Sε 0‖ * C * t = 2 * t * ε * ‖Sε 0‖ * C := by ring
    linarith
  have hsq : ‖Sε t - S0 t‖ ^ 2 ≤ 2 * t * ε * ‖Sε 0‖ * C := hgt_bound
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg (Sε t - S0 t))] at hsqrt

/-- If `H0` commutes with `HD`, then along a solution of the unperturbed equation the
norm `‖HD S0(t)‖` is conserved.  This is the source's observation (72)--(73) that
`HD⁺ S0(t)` is obtained by applying the norm-preserving flow to `HD⁺ S0(0)`. -/
lemma norm_comp_const_of_commute (H0 HD : E →L[ℂ] E) (hH0 : IsSelfAdjointCLM H0)
    (hcomm : ∀ x : E, H0 (HD x) = HD (H0 x))
    (S0 : ℝ → E) (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • H0 (S0 τ)) τ) :
    ∀ τ, ‖HD (S0 τ)‖ = ‖HD (S0 0)‖ := by
  let T : ℝ → E := fun τ => HD (S0 τ)
  have hT : ∀ τ, HasDerivAt T (-(Complex.I) • H0 (T τ)) τ := by
    intro τ
    have hcomp : HasDerivAt (fun τ => HD (S0 τ))
        (HD (-(Complex.I) • H0 (S0 τ))) τ :=
      HasFDerivAt.comp_hasDerivAt (l := fun x : E => HD x)
        (l' := HD.restrictScalars ℝ) τ
        (ContinuousLinearMap.hasFDerivAt (HD.restrictScalars ℝ)) (hS0 τ)
    have hval : HD (-(Complex.I) • H0 (S0 τ)) = -(Complex.I) • H0 (HD (S0 τ)) := by
      rw [map_smul]
      rw [hcomm (S0 τ)]
    rw [hval] at hcomp
    exact hcomp
  have hsq : ∀ τ, ‖T τ‖ ^ 2 = ‖T 0‖ ^ 2 :=
    norm_sq_const_of_deriv_zero T H0 hH0 hT
  exact norm_eq_of_norm_sq_eq T hsq

/-- Theorem 2 of the source, equations (56)--(58): the difference between the solutions
with perturbation `ε` and `0` is controlled by the initial state and the initial size of
`HD S0`.  This is equation (80) with the source's conservation of `‖HD S0(t)‖`.

In the paper's block notation `S = (φ, ψ₁, ..., ψ_d)`, the two norms on the right are
`‖S(0)‖² = ‖φ(0)‖² + ∑ⱼ ‖ψⱼ(0)‖²` and
`‖HD S0(0)‖² = ‖D φ(0)‖² + ∑ⱼ ‖D ψⱼ(0)‖²`, so the displayed bound is exactly (57)
with the paper's two sums.  The component estimate for `φε - φ0` is
`theorem2_component_bound`. -/
theorem theorem2_wave_perturbation {H0 HD : E →L[ℂ] E}
    (hH0 : IsSelfAdjointCLM H0) (hHD : IsSelfAdjointCLM HD)
    (hcomm : ∀ x : E, H0 (HD x) = HD (H0 x))
    {Sε S0 : ℝ → E} {ε t : ℝ}
    (hSε : ∀ τ, HasDerivAt Sε
      (-(Complex.I) • (H0 (Sε τ) + (ε : ℂ) • HD (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • (H0 (S0 τ))) τ)
    (hinit : Sε 0 = S0 0) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖Sε t - S0 t‖ ≤
      Real.sqrt (2 * t * ε * ‖Sε 0‖ * ‖HD (S0 0)‖) := by
  refine perturbation_norm_bound hH0 hHD hSε hS0 hinit ?_ hε ht
  intro τ _
  exact le_of_eq (norm_comp_const_of_commute H0 HD hH0 hcomm S0 hS0 τ)

/-- Component form of Theorem 2: projecting the full state difference onto the `φ`
component (the paper's equation (81)) can only decrease the norm.  With the projection
norm at most one this is exactly `‖φε(t) - φ0(t)‖ ≤ ‖Sε(t) - S0(t)‖`, and the right
side is (57). -/
theorem theorem2_component_bound {H0 HD P : E →L[ℂ] E}
    (hH0 : IsSelfAdjointCLM H0) (hHD : IsSelfAdjointCLM HD)
    (hcomm : ∀ x : E, H0 (HD x) = HD (H0 x))
    (hP : ‖P‖ ≤ 1)
    {Sε S0 : ℝ → E} {ε t : ℝ}
    (hSε : ∀ τ, HasDerivAt Sε
      (-(Complex.I) • (H0 (Sε τ) + (ε : ℂ) • HD (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • (H0 (S0 τ))) τ)
    (hinit : Sε 0 = S0 0) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖P (Sε t) - P (S0 t)‖ ≤
      Real.sqrt (2 * t * ε * ‖Sε 0‖ * ‖HD (S0 0)‖) := by
  have hmain := theorem2_wave_perturbation hH0 hHD hcomm hSε hS0 hinit hε ht
  have hproj : ‖P (Sε t) - P (S0 t)‖ ≤ ‖Sε t - S0 t‖ := by
    rw [← map_sub]
    calc
      ‖P (Sε t - S0 t)‖ ≤ ‖P‖ * ‖Sε t - S0 t‖ := P.le_opNorm _
      _ ≤ 1 * ‖Sε t - S0 t‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ = ‖Sε t - S0 t‖ := one_mul _
  exact le_trans hproj hmain

end Qatlib.Papers.WaveEquation17.MainResults
