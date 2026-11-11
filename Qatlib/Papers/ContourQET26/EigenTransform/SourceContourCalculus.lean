/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option backward.isDefEq.respectTransparency false

/-!
# Quadrature error of the contour integral discretization

Source: Jiang and An, "Contour-integral based quantum eigenvalue transformation: analysis and
applications", fixed arXiv:2601.11959v3 (2026-09-20).

Section 2.1 defines the Cauchy integral `f(A) = (1/2πi) ∮_Γ f(z)(zI - A)⁻¹ dz` (eq. (2.1)) and
its left-endpoint Riemann approximation `f_M(A)` (eq. (2.2)), and Proposition 5 (p. 10) bounds the
quadrature error by `(Bγ² + BK_Γγ + Lγ) l² / (8πM)`.

This file defines the contour model, the two objects `contourIntegral` and `riemannSum`, and
proves Proposition 5 in full.  The proof is the paper's argument on pp. 10-11: the integrand is
Lipschitz with constant `C = (Bγ² + BK_Γγ + Lγ)/2π` (eq. (2.5), via the resolvent identity of
eq. (2.4)), a closed contour rewrites the left-endpoint sum as the trapezoidal sum (telescoping
with `h(l) = h(0)`), and on each segment of length `Δ = l/M` the midpoint identity

`∫ h - (Δ/2)(h(t_k) + h(t_{k+1})) = ∫_{t_k}^{t_k+Δ/2}(h - h(t_k)) + ∫_{t_k+Δ/2}^{t_{k+1}}(h - h(t_{k+1}))`

together with the Lipschitz bound gives the segment error `C Δ²/4` with the paper's sharp
constant; summing over the `M` segments gives `C l²/(4M) = (Bγ² + BK_Γγ + Lγ) l²/(8πM)`.

The hypothesis `hinv` (invertibility of `z(t) I - A` along the contour) is implied by the
paper's resolvent bound together with the Lipschitz parametrization; it is stated explicitly
because `Matrix.inv` is the junk-if-singular ring inverse, for which the norm bound `hγ` alone
would be vacuously satisfiable at singular points.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable local instance {N : Type*} [Fintype N] [DecidableEq N] :
    ENormedAddMonoid (Matrix N N ℂ) := NormedAddGroup.toENormedAddMonoid

namespace Qatlib.Papers.ContourQET26.EigenTransform

/-- Data of a parametrized contour quadrature: the matrix `A`, the scalar function `f`, a unit-speed
parametrization `z` of the contour `Γ` with tangent angle `θ`, and the contour length `l`.
The paper uses the arc-length parametrization `t ∈ [0, l]` (Section 2.1). -/
structure ContourData (N : Type*) [Fintype N] [DecidableEq N] where
  /-- The matrix whose matrix function is being discretized. -/
  A : Matrix N N ℂ
  /-- The scalar function of the matrix function `f(A)`. -/
  f : ℂ → ℂ
  /-- Unit-speed parametrization of the contour `Γ`. -/
  z : ℝ → ℂ
  /-- Tangent angle `θ` of the parametrization, so that `z' = e^{iθ}`. -/
  θ : ℝ → ℝ
  /-- Length of the contour. -/
  l : ℝ

/-- The integrand `h(t) = (1/2πi) f(z(t)) e^{iθ(t)} (z(t) I - A)⁻¹` of the contour integral,
with arc-length parametrization `t ↦ z(t)` (Section 2.1, just before eq. (2.2)). -/
def ContourData.integrand {N : Type*} [Fintype N] [DecidableEq N] (D : ContourData N)
    (t : ℝ) : Matrix N N ℂ :=
  ((2 * (Real.pi : ℂ)) * Complex.I)⁻¹ •
    (D.f (D.z t) * Complex.exp (Complex.I * (D.θ t : ℂ))) • (D.z t • 1 - D.A)⁻¹

/-- The exact Cauchy contour integral `(1/2πi) ∮_Γ f(z) (zI - A)⁻¹ dz`, written in arc-length
parametrization as `∫_0^l h(t) dt` (eq. (2.1)). -/
def ContourData.contourIntegral {N : Type*} [Fintype N] [DecidableEq N] (D : ContourData N) :
    Matrix N N ℂ :=
  ∫ t in (0 : ℝ)..D.l, D.integrand t

/-- The left-endpoint Riemann sum `f_M(A)` of eq. (2.2), with nodes `t_k = k l / M` and weights
`l_k = l / M`: `f_M(A) = ∑_{k=0}^{M-1} (l/M) h(k l / M)`. -/
def ContourData.riemannSum {N : Type*} [Fintype N] [DecidableEq N] (D : ContourData N)
    (M : ℕ) : Matrix N N ℂ :=
  ∑ k ∈ Finset.range M, (D.l / M) • D.integrand (k * (D.l / M))

/-- The phase `e^{iθ}` is Lipschitz in `θ` with constant `1`, via
`exp(i a) - exp(i b) = e^{ib}(e^{i(a-b)} - 1)` and `|e^{ix} - 1| = 2|sin(x/2)|`. -/
private lemma norm_exp_I_mul_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have hsplit : Complex.exp (Complex.I * (a : ℂ))
      = Complex.exp (Complex.I * (b : ℂ)) * Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, Complex.ofReal_sub]
    congr 1
    ring
  have hsin : |Real.sin (((a - b : ℝ)) / 2)| * 2 ≤ |a - b| := by
    have h1 : |Real.sin (((a - b : ℝ)) / 2)| ≤ |(((a - b : ℝ)) / 2)| :=
      Real.abs_sin_le_abs
    have h2 : |(((a - b : ℝ)) / 2)| = |a - b| / 2 := by
      rw [abs_div]
      norm_num
    nlinarith [h1]
  have hfac : Complex.exp (Complex.I * (b : ℂ)) * Complex.exp (Complex.I * ((a - b : ℝ) : ℂ))
      - Complex.exp (Complex.I * (b : ℂ))
      = Complex.exp (Complex.I * (b : ℂ))
        * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by ring
  rw [hsplit, hfac, norm_mul, Complex.norm_exp_I_mul_ofReal,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), one_mul]
  linarith

set_option maxHeartbeats 1200000 in
/-- **Proposition 5 (p. 10), quadrature error bound (2.3).**  Let `Γ` be the unit-speed contour
with length `l`, let `B` bound `|f|` on `Γ`, let `γ` bound `‖(zI-A)⁻¹‖` on `Γ`, let `L` be a
Lipschitz constant of `f` on `Γ`, let `K` bound the tangent variation rate, and suppose the
contour is closed (`h(l) = h(0)`) and the resolvent `z(t) I - A` is invertible along `Γ`.
Then the exact contour integral and the left-endpoint Riemann sum differ in operator norm by at
most `(Bγ² + BK_Γγ + Lγ) l² / (8πM)`.

Note.  The paper's `f(A)` is the contour integral by Cauchy's formula; here `contourIntegral` is
that integral by definition, so the analyticity hypothesis is absorbed into the definition of the
matrix function.  The hypotheses `hz`, `hθ` encode the unit-speed parametrization and the tangent
variation bound `K_Γ`; `hL` is the `L`-Lipschitz continuity of `f` on `Γ`.  The invertibility
hypothesis `hinv` is what makes the resolvent hypothesis `hγ` meaningful for `Matrix.inv` (the
junk value `0` of a singular inverse would satisfy `hγ` vacuously); in the paper it follows from
`Γ` enclosing the spectrum of `A`. -/
theorem proposition5_quadrature_error {N : Type*} [Fintype N] [DecidableEq N]
    (D : ContourData N) (M : ℕ) (B γ K L : ℝ) (hM : 0 < M) (hl : 0 < D.l)
    (hB : ∀ t ∈ Set.Icc 0 D.l, ‖D.f (D.z t)‖ ≤ B)
    (hγ : ∀ t ∈ Set.Icc 0 D.l, ‖(D.z t • (1 : Matrix N N ℂ) - D.A)⁻¹‖ ≤ γ)
    (hKn : 0 ≤ K)
    (hLn : 0 ≤ L)
    (hL : ∀ t₁ ∈ Set.Icc 0 D.l, ∀ t₂ ∈ Set.Icc 0 D.l,
      ‖D.f (D.z t₁) - D.f (D.z t₂)‖ ≤ L * ‖D.z t₁ - D.z t₂‖)
    (hz : ∀ t₁ ∈ Set.Icc 0 D.l, ∀ t₂ ∈ Set.Icc 0 D.l, ‖D.z t₁ - D.z t₂‖ ≤ |t₁ - t₂|)
    (hθ : ∀ t₁ ∈ Set.Icc 0 D.l, ∀ t₂ ∈ Set.Icc 0 D.l, |D.θ t₁ - D.θ t₂| ≤ K * |t₁ - t₂|)
    (hinv : ∀ t ∈ Set.Icc 0 D.l, IsUnit (D.z t • (1 : Matrix N N ℂ) - D.A).det)
    (hclosed : D.integrand D.l = D.integrand 0) :
    ‖D.contourIntegral - D.riemannSum M‖
      ≤ (B * γ ^ 2 + B * K * γ + L * γ) * D.l ^ 2 / (8 * Real.pi * M) := by
  classical
  have h0S : (0 : ℝ) ∈ Set.Icc 0 D.l := Set.left_mem_Icc.mpr hl.le
  have hlS : D.l ∈ Set.Icc 0 D.l := Set.right_mem_Icc.mpr hl.le
  have hBn : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 h0S)
  have hγn : 0 ≤ γ := le_trans (norm_nonneg _) (hγ 0 h0S)
  set C : ℝ := (B * γ ^ 2 + B * K * γ + L * γ) / (2 * Real.pi) with hC
  have hCn : 0 ≤ C := by
    rw [hC]
    apply div_nonneg _ (by positivity)
    have h1 : 0 ≤ B * γ * γ := mul_nonneg (mul_nonneg hBn hγn) hγn
    have h2 : 0 ≤ B * K * γ := mul_nonneg (mul_nonneg hBn hKn) hγn
    have h3 : 0 ≤ L * γ := mul_nonneg hLn hγn
    have hre : B * γ ^ 2 + B * K * γ + L * γ = B * γ * γ + B * K * γ + L * γ := by ring
    rw [hre]
    linarith
  set Δ : ℝ := D.l / (M : ℝ) with hΔ
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hΔpos : 0 < Δ := by rw [hΔ]; positivity
  have hΔnn : 0 ≤ Δ := hΔpos.le
  have hMΔ : (M : ℝ) * Δ = D.l := by
    rw [hΔ]; field_simp
  have hmem : ∀ n : ℕ, n ≤ M → ((n : ℝ) * Δ ∈ Set.Icc 0 D.l) := by
    intro n hn
    have h2 : (n : ℝ) * Δ ≤ (M : ℝ) * Δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hΔnn
    rw [hMΔ] at h2
    exact ⟨by positivity, h2⟩
  -- Step 1: the norm of the scalar prefactor
  have hcnorm : ‖(((2 * (Real.pi : ℂ)) * Complex.I)⁻¹ : ℂ)‖ = 1 / (2 * Real.pi) := by
    have hc0 : (2 * (Real.pi : ℂ)) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hI : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I
    have hp : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi :=
      (RCLike.norm_ofReal (2 * Real.pi)).trans (abs_of_nonneg (by positivity))
    rw [hc0, norm_inv, norm_mul, hp, hI, mul_one, inv_eq_one_div]
  -- Step 2: the resolvent difference bound (eq. (2.4))
  have hRsub : ∀ t₁ ∈ Set.Icc 0 D.l, ∀ t₂ ∈ Set.Icc 0 D.l,
      ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹ - (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹‖
        ≤ γ * γ * ‖D.z t₁ - D.z t₂‖ := by
    intro t₁ ht₁ t₂ ht₂
    have hXu : IsUnit (D.z t₁ • (1 : Matrix N N ℂ) - D.A).det := hinv t₁ ht₁
    have hYu : IsUnit (D.z t₂ • (1 : Matrix N N ℂ) - D.A).det := hinv t₂ ht₂
    have hiff : IsUnit (D.z t₁ • (1 : Matrix N N ℂ) - D.A)
        ↔ IsUnit (D.z t₂ • (1 : Matrix N N ℂ) - D.A) :=
      ⟨fun _ => (Matrix.isUnit_iff_isUnit_det _).mpr hYu,
        fun _ => (Matrix.isUnit_iff_isUnit_det _).mpr hXu⟩
    have hYX : (D.z t₂ • (1 : Matrix N N ℂ) - D.A) - (D.z t₁ • (1 : Matrix N N ℂ) - D.A)
        = (D.z t₂ - D.z t₁) • (1 : Matrix N N ℂ) := by
      have h1 : (D.z t₂ • (1 : Matrix N N ℂ) - D.A) - (D.z t₁ • (1 : Matrix N N ℂ) - D.A)
          = D.z t₂ • (1 : Matrix N N ℂ) - D.z t₁ • (1 : Matrix N N ℂ) := by abel
      rw [h1, ← sub_smul]
    rw [Matrix.inv_sub_inv hiff, hYX, mul_smul_comm, smul_mul_assoc, mul_one, norm_smul]
    have h1 : ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹ * (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹‖
        ≤ γ * γ := by
      calc ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹ * (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹‖
          ≤ ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹‖
              * ‖(D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ γ * γ := mul_le_mul (hγ t₁ ht₁) (hγ t₂ ht₂) (norm_nonneg _) hγn
    have h2 : ‖D.z t₂ - D.z t₁‖ = ‖D.z t₁ - D.z t₂‖ := by rw [norm_sub_rev]
    rw [h2]
    nlinarith [h1, norm_nonneg (D.z t₁ - D.z t₂), hγn]
  -- Step 3: the scalar amplitude `f(z(t)) e^{iθ(t)}`
  have hsnorm : ∀ t ∈ Set.Icc 0 D.l, ‖D.f (D.z t) * Complex.exp (Complex.I * (D.θ t : ℂ))‖ ≤ B := by
    intro t ht
    calc ‖D.f (D.z t) * Complex.exp (Complex.I * (D.θ t : ℂ))‖
        = ‖D.f (D.z t)‖ * ‖Complex.exp (Complex.I * (D.θ t : ℂ))‖ := (norm_mul _ _)
      _ = ‖D.f (D.z t)‖ * 1 := by rw [Complex.norm_exp_I_mul_ofReal]
      _ = ‖D.f (D.z t)‖ := mul_one _
      _ ≤ B := hB t ht
  have hΔs : ∀ t₁ ∈ Set.Icc 0 D.l, ∀ t₂ ∈ Set.Icc 0 D.l,
      ‖D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))
          - D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))‖
        ≤ L * |t₁ - t₂| + B * K * |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂
    have hsplit : D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))
        - D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))
        = (D.f (D.z t₁) - D.f (D.z t₂)) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))
          + D.f (D.z t₂) * (Complex.exp (Complex.I * (D.θ t₁ : ℂ))
              - Complex.exp (Complex.I * (D.θ t₂ : ℂ))) := by ring
    have hE1 := norm_exp_I_mul_sub_le (D.θ t₁) (D.θ t₂)
    have hE2 := hθ t₁ ht₁ t₂ ht₂
    have hθ1 : ‖D.f (D.z t₁) - D.f (D.z t₂)‖ ≤ L * |t₁ - t₂| := by
      have h := hL t₁ ht₁ t₂ ht₂
      have hzz := hz t₁ ht₁ t₂ ht₂
      exact le_trans h (mul_le_mul_of_nonneg_left hzz hLn)
    calc ‖D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))
          - D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))‖
        = ‖(D.f (D.z t₁) - D.f (D.z t₂)) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))
          + D.f (D.z t₂) * (Complex.exp (Complex.I * (D.θ t₁ : ℂ))
              - Complex.exp (Complex.I * (D.θ t₂ : ℂ)))‖ := by rw [hsplit]
      _ ≤ ‖(D.f (D.z t₁) - D.f (D.z t₂)) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))‖
          + ‖D.f (D.z t₂) * (Complex.exp (Complex.I * (D.θ t₁ : ℂ))
              - Complex.exp (Complex.I * (D.θ t₂ : ℂ)))‖ := norm_add_le _ _
      _ = ‖D.f (D.z t₁) - D.f (D.z t₂)‖ * ‖Complex.exp (Complex.I * (D.θ t₁ : ℂ))‖
          + ‖D.f (D.z t₂)‖ * ‖Complex.exp (Complex.I * (D.θ t₁ : ℂ))
              - Complex.exp (Complex.I * (D.θ t₂ : ℂ))‖ := by rw [norm_mul, norm_mul]
      _ ≤ L * |t₁ - t₂| * 1 + B * (K * |t₁ - t₂|) := by
          refine add_le_add (mul_le_mul hθ1 (le_of_eq (Complex.norm_exp_I_mul_ofReal _))
            (norm_nonneg _) (mul_nonneg hLn (abs_nonneg _))) ?_
          exact mul_le_mul (hB t₂ ht₂) (le_trans hE1 hE2) (norm_nonneg _) hBn
      _ = L * |t₁ - t₂| + B * K * |t₁ - t₂| := by rw [mul_one, mul_assoc]
  -- Step 4: the integrand is `C`-Lipschitz on `[0, l]` (eq. (2.5))
  have hlh : ∀ t₁ ∈ Set.Icc 0 D.l, ∀ t₂ ∈ Set.Icc 0 D.l,
      ‖D.integrand t₁ - D.integrand t₂‖ ≤ C * |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂
    simp only [ContourData.integrand]
    rw [← smul_sub, norm_smul]
    have hsplit : (D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ)))
          • (D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹
          - (D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ)))
            • (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹
        = ((D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ)))
              - (D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))))
            • (D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹
          + (D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ)))
            • ((D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹
                - (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹) := by
      rw [sub_smul, smul_sub]
      abel
    have h1 := hΔs t₁ ht₁ t₂ ht₂
    have h2 := hsnorm t₂ ht₂
    have h3 := hRsub t₁ ht₁ t₂ ht₂
    have hzabs := hz t₁ ht₁ t₂ ht₂
    have hR1 : ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹‖ ≤ γ := hγ t₁ ht₁
    have hLnn : 0 ≤ L * |t₁ - t₂| + B * K * |t₁ - t₂| :=
      add_nonneg (mul_nonneg hLn (abs_nonneg _))
        (mul_nonneg (mul_nonneg hBn hKn) (abs_nonneg _))
    have hbounds : ‖D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))
          - D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))‖ * ‖(D.z t₁ • (1 : Matrix N N ℂ)
            - D.A)⁻¹‖ + ‖D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))‖
            * ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹
              - (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹‖
        ≤ (L * |t₁ - t₂| + B * K * |t₁ - t₂|) * γ
            + B * (γ * γ * |t₁ - t₂|) := by
      refine add_le_add (mul_le_mul h1 hR1 (norm_nonneg _) hLnn) ?_
      refine le_trans (mul_le_mul h2 h3 (norm_nonneg _) hBn) ?_
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hzabs (mul_nonneg hγn hγn)) hBn
    have hnorm : ‖((D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ)))
              - (D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))))
            • (D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹
          + (D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ)))
            • ((D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹
                - (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹)‖
        ≤ ‖(D.f (D.z t₁) * Complex.exp (Complex.I * (D.θ t₁ : ℂ))
              - D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ)))‖
            * ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹‖
          + ‖D.f (D.z t₂) * Complex.exp (Complex.I * (D.θ t₂ : ℂ))‖
            * ‖(D.z t₁ • (1 : Matrix N N ℂ) - D.A)⁻¹
                - (D.z t₂ • (1 : Matrix N N ℂ) - D.A)⁻¹‖ :=
      le_trans (norm_add_le _ _) (by rw [norm_smul, norm_smul])
    rw [hsplit, hcnorm]
    refine le_trans (mul_le_mul_of_nonneg_left (hnorm.trans hbounds) (by positivity)) ?_
    rw [hC]
    have hfinal : (1 / (2 * Real.pi)) * ((L * |t₁ - t₂| + B * K * |t₁ - t₂|) * γ
          + B * (γ * γ * |t₁ - t₂|))
        ≤ ((B * γ ^ 2 + B * K * γ + L * γ) / (2 * Real.pi)) * |t₁ - t₂| := by
      have heq : (1 / (2 * Real.pi)) * ((L * |t₁ - t₂| + B * K * |t₁ - t₂|) * γ
            + B * (γ * γ * |t₁ - t₂|))
          = ((B * γ ^ 2 + B * K * γ + L * γ) / (2 * Real.pi)) * |t₁ - t₂| := by
        field_simp
        ring
      rw [heq]
    exact hfinal
  -- Step 5: continuity and integrability
  have hlip : LipschitzOnWith ⟨C, hCn⟩ D.integrand (Set.Icc 0 D.l) := by
    refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
    have h := hlh x hx y hy
    rw [← dist_eq_norm, ← Real.dist_eq] at h
    exact_mod_cast h
  have hcont : ContinuousOn D.integrand (Set.Icc 0 D.l) := LipschitzOnWith.continuousOn hlip
  have hint : ∀ a : ℝ, a ∈ Set.Icc 0 D.l → ∀ b : ℝ, b ∈ Set.Icc 0 D.l → a ≤ b →
      IntervalIntegrable D.integrand MeasureTheory.volume a b := by
    intro a ha b hb hab
    refine ContinuousOn.intervalIntegrable ?_
    refine hcont.mono ?_
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha.1 hb.2
  -- Step 6: elementary integrals
  have hIid : ∀ a b : ℝ, ∫ t in a..b, t = (b ^ 2 - a ^ 2) / 2 := by
    intro a b
    have hder : ∀ x : ℝ, HasDerivAt (fun t => t ^ 2 / 2) x x := fun x => by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have hintid : IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume a b :=
      Continuous.intervalIntegrable continuous_id a b
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x) hintid
    rw [h]
    field_simp
  have hlin1 : ∀ a b : ℝ, a ≤ b → ∫ t in a..b, C * (t - a) = C * (b - a) ^ 2 / 2 := by
    intro a b hab
    have hint1 : IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume a b :=
      Continuous.intervalIntegrable continuous_id a b
    have hint2 : IntervalIntegrable (fun _ : ℝ => a) MeasureTheory.volume a b :=
      Continuous.intervalIntegrable continuous_const a b
    rw [intervalIntegral.integral_const_mul]
    have hexp : ∫ t in a..b, t - a = (b - a) ^ 2 / 2 := by
      rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const,
        smul_eq_mul, hIid a b]
      field_simp
      ring
    rw [hexp]
    ring
  have hlin2 : ∀ a b : ℝ, a ≤ b → ∫ t in a..b, C * (b - t) = C * (b - a) ^ 2 / 2 := by
    intro a b hab
    have hint1 : IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume a b :=
      Continuous.intervalIntegrable continuous_id a b
    have hint2 : IntervalIntegrable (fun _ : ℝ => b) MeasureTheory.volume a b :=
      Continuous.intervalIntegrable continuous_const a b
    rw [intervalIntegral.integral_const_mul]
    have hexp : ∫ t in a..b, b - t = (b - a) ^ 2 / 2 := by
      rw [intervalIntegral.integral_sub hint2 hint1, intervalIntegral.integral_const,
        smul_eq_mul, hIid a b]
      field_simp
      ring
    rw [hexp]
    ring
  -- Step 7: the per-segment trapezoid bound with the sharp constant Δ²/4
  have hseg : ∀ k : ℕ, k ∈ Finset.range M →
      ‖(∫ t in (k : ℝ) * Δ..((k : ℝ) + 1) * Δ, D.integrand t)
          - (Δ / 2) • (D.integrand ((k : ℝ) * Δ) + D.integrand (((k : ℝ) + 1) * Δ))‖
        ≤ C * Δ ^ 2 / 4 := by
    intro k hk
    set a : ℝ := (k : ℝ) * Δ with hka
    set b : ℝ := ((k : ℝ) + 1) * Δ with hkb
    set m : ℝ := a + Δ / 2 with hkm
    have hkM : (k : ℝ) + 1 ≤ (M : ℝ) := by
      have hkm' : k + 1 ≤ M := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      exact_mod_cast hkm'
    have hba : b = a + Δ := by rw [hka, hkb]; ring
    have hma : m - a = Δ / 2 := by rw [hkm]; ring
    have hmb : b - m = Δ / 2 := by rw [hkm, hba]; ring
    have haS : a ∈ Set.Icc 0 D.l := by
      rw [hka]
      have h1 : (k : ℝ) * Δ ≤ ((k : ℝ) + 1) * Δ :=
        mul_le_mul_of_nonneg_right (by linarith) hΔnn
      have h2 : ((k : ℝ) + 1) * Δ ≤ (M : ℝ) * Δ :=
        mul_le_mul_of_nonneg_right hkM hΔnn
      rw [hMΔ] at h2
      exact ⟨by positivity, h1.trans h2⟩
    have hbS : b ∈ Set.Icc 0 D.l := by
      rw [hkb]
      have h2 : ((k : ℝ) + 1) * Δ ≤ (M : ℝ) * Δ :=
        mul_le_mul_of_nonneg_right hkM hΔnn
      rw [hMΔ] at h2
      exact ⟨by positivity, h2⟩
    have hmS : m ∈ Set.Icc 0 D.l := by
      have h2 : a ≤ m := by rw [hkm]; linarith
      have h3 : m ≤ b := by rw [hkm, hba]; linarith
      exact ⟨haS.1.trans h2, h3.trans hbS.2⟩
    have ham : a ≤ m := by rw [hkm]; linarith
    have hmbm : m ≤ b := by rw [hkm, hba]; linarith
    have hint_am : IntervalIntegrable D.integrand MeasureTheory.volume a m := hint a haS m hmS ham
    have hint_mb : IntervalIntegrable D.integrand MeasureTheory.volume m b := hint m hmS b hbS hmbm
    have hconst_am : IntervalIntegrable (fun _ : ℝ => D.integrand a) MeasureTheory.volume a m :=
      Continuous.intervalIntegrable continuous_const a m
    have hconst_mb : IntervalIntegrable (fun _ : ℝ => D.integrand b) MeasureTheory.volume m b :=
      Continuous.intervalIntegrable continuous_const m b
    have hkey : ∀ X Y U V : Matrix N N ℂ, (X - U) + (Y - V) = (X + Y) - (U + V) := by
      intro X Y U V
      abel
    have hid : (∫ t in a..b, D.integrand t) - (Δ / 2) • (D.integrand a + D.integrand b)
        = (∫ t in a..m, D.integrand t - D.integrand a)
          + (∫ t in m..b, D.integrand t - D.integrand b) := by
      rw [intervalIntegral.integral_sub hint_am hconst_am,
          intervalIntegral.integral_sub hint_mb hconst_mb,
          intervalIntegral.integral_const, intervalIntegral.integral_const, hma, hmb,
          hkey _ _ _ _, ← intervalIntegral.integral_add_adjacent_intervals hint_am hint_mb]
      try rw [smul_add]
    have hb1 : ‖∫ t in a..m, D.integrand t - D.integrand a‖ ≤ C * (Δ / 2) ^ 2 / 2 := by
      have hintg : IntervalIntegrable (fun t => C * (t - a)) MeasureTheory.volume a m :=
        Continuous.intervalIntegrable (by fun_prop) a m
      have haeb : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioc a m →
          ‖D.integrand t - D.integrand a‖ ≤ C * (t - a) := by
        refine MeasureTheory.ae_of_all MeasureTheory.volume (fun t ht => ?_)
        rcases ht with ⟨hta, htm⟩
        have htS : t ∈ Set.Icc 0 D.l :=
          ⟨haS.1.trans hta.le, (htm.trans hmbm).trans hbS.2⟩
        have h := hlh t htS a haS
        rw [abs_of_nonneg (show 0 ≤ t - a by linarith)] at h
        exact h
      have h1 : ‖∫ t in a..m, D.integrand t - D.integrand a‖ ≤ ∫ t in a..m, C * (t - a) :=
        intervalIntegral.norm_integral_le_of_norm_le ham haeb hintg
      rw [hlin1 a m ham, hma] at h1
      exact h1
    have hb2 : ‖∫ t in m..b, D.integrand t - D.integrand b‖ ≤ C * (Δ / 2) ^ 2 / 2 := by
      have hintg : IntervalIntegrable (fun t => C * (b - t)) MeasureTheory.volume m b :=
        Continuous.intervalIntegrable (by fun_prop) m b
      have haeb : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioc m b →
          ‖D.integrand t - D.integrand b‖ ≤ C * (b - t) := by
        refine MeasureTheory.ae_of_all MeasureTheory.volume (fun t ht => ?_)
        rcases ht with ⟨htm, htb⟩
        have htS : t ∈ Set.Icc 0 D.l :=
          ⟨hmS.1.trans htm.le, htb.trans hbS.2⟩
        have h := hlh t htS b hbS
        rw [abs_sub_comm, abs_of_nonneg (show 0 ≤ b - t by linarith)] at h
        exact h
      have h1 : ‖∫ t in m..b, D.integrand t - D.integrand b‖ ≤ ∫ t in m..b, C * (b - t) :=
        intervalIntegral.norm_integral_le_of_norm_le hmbm haeb hintg
      rw [hlin2 m b hmbm, hmb] at h1
      exact h1
    rw [hid]
    calc ‖(∫ t in a..m, D.integrand t - D.integrand a)
          + (∫ t in m..b, D.integrand t - D.integrand b)‖
        ≤ ‖∫ t in a..m, D.integrand t - D.integrand a‖
            + ‖∫ t in m..b, D.integrand t - D.integrand b‖ := norm_add_le _ _
      _ ≤ C * (Δ / 2) ^ 2 / 2 + C * (Δ / 2) ^ 2 / 2 := add_le_add hb1 hb2
      _ = C * Δ ^ 2 / 4 := by ring
  -- Step 8: the closed contour makes the left-endpoint sum a trapezoidal sum
  have hshift : ∀ m : ℕ, m ≤ M →
      (∑ k ∈ Finset.range m, D.integrand (((k : ℝ) + 1) * Δ)) + D.integrand 0
        = (∑ k ∈ Finset.range m, D.integrand ((k : ℝ) * Δ)) + D.integrand ((m : ℝ) * Δ) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
        intro hnM
        have hinn : n ≤ M := le_trans (Nat.le_succ n) hnM
        have h := ih hinn
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_succ, ← h]
        abel
  have hMl : D.integrand ((M : ℝ) * Δ) = D.integrand 0 := by
    rw [hMΔ]
    exact hclosed
  have hsum_eq : ∑ k ∈ Finset.range M, D.integrand (((k : ℝ) + 1) * Δ)
      = ∑ k ∈ Finset.range M, D.integrand ((k : ℝ) * Δ) := by
    have h1 : (∑ k ∈ Finset.range M, D.integrand (((k : ℝ) + 1) * Δ)) + D.integrand 0
        = (∑ k ∈ Finset.range M, D.integrand ((k : ℝ) * Δ)) + D.integrand 0 := by
      rw [hshift M le_rfl, hMl]
    exact add_right_cancel h1
  have htele : ∑ k ∈ Finset.range M,
      (Δ / 2) • (D.integrand ((k : ℝ) * Δ) + D.integrand (((k : ℝ) + 1) * Δ))
      = ∑ k ∈ Finset.range M, Δ • D.integrand ((k : ℝ) * Δ) := by
    have h1 : ∑ k ∈ Finset.range M,
        (Δ / 2) • (D.integrand ((k : ℝ) * Δ) + D.integrand (((k : ℝ) + 1) * Δ))
        = (Δ / 2) • ((∑ k ∈ Finset.range M, D.integrand ((k : ℝ) * Δ))
              + ∑ k ∈ Finset.range M, D.integrand (((k : ℝ) + 1) * Δ)) := by
      rw [smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => smul_add _ _ _)
    rw [h1, hsum_eq, smul_add, ← add_smul, add_halves, ← Finset.smul_sum]
  -- Step 9: split the integral and assemble
  have hsplitint : ∀ m : ℕ, m ≤ M →
      ∫ t in 0..(m : ℝ) * Δ, D.integrand t
        = ∑ k ∈ Finset.range m, ∫ t in (k : ℝ) * Δ..((k : ℝ) + 1) * Δ, D.integrand t := by
    intro m
    induction m with
    | zero => rw [Nat.cast_zero, zero_mul, intervalIntegral.integral_same]; simp
    | succ n ih =>
        intro hnM
        have hinn : n ≤ M := le_trans (Nat.le_succ n) hnM
        have h := ih hinn
        have hmemn : ((n : ℝ) * Δ) ∈ Set.Icc 0 D.l := hmem n hinn
        have hmemn1 : (((n : ℝ) + 1) * Δ) ∈ Set.Icc 0 D.l := by
          have h9 := hmem (n + 1) hnM
          rwa [Nat.cast_succ] at h9
        have hint1 : IntervalIntegrable D.integrand MeasureTheory.volume 0 ((n : ℝ) * Δ) :=
          hint 0 h0S ((n : ℝ) * Δ) hmemn (by positivity)
        have hint2 : IntervalIntegrable D.integrand MeasureTheory.volume ((n : ℝ) * Δ)
            (((n : ℝ) + 1) * Δ) :=
          hint ((n : ℝ) * Δ) hmemn (((n : ℝ) + 1) * Δ) hmemn1
            (mul_le_mul_of_nonneg_right (by linarith) hΔnn)
        rw [Finset.sum_range_succ, Nat.cast_succ, ← h]
        exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hbound : ∫ t in 0..D.l, D.integrand t = ∫ t in 0..(M : ℝ) * Δ, D.integrand t := by
    rw [hMΔ]
  have hriem : D.riemannSum M = ∑ k ∈ Finset.range M, Δ • D.integrand ((k : ℝ) * Δ) := by
    rw [ContourData.riemannSum, ← hΔ]
  rw [ContourData.contourIntegral, hbound, hriem, hsplitint M le_rfl, ← htele,
    ← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ Finset.range M, ((∫ t in (k : ℝ) * Δ..((k : ℝ) + 1) * Δ, D.integrand t)
      - (Δ / 2) • (D.integrand ((k : ℝ) * Δ) + D.integrand (((k : ℝ) + 1) * Δ)))‖
      ≤ ∑ k ∈ Finset.range M, ‖(∫ t in (k : ℝ) * Δ..((k : ℝ) + 1) * Δ, D.integrand t)
      - (Δ / 2) • (D.integrand ((k : ℝ) * Δ) + D.integrand (((k : ℝ) + 1) * Δ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range M, C * Δ ^ 2 / 4 := Finset.sum_le_sum hseg
    _ = M * (C * Δ ^ 2 / 4) := by simp [Finset.sum_const]
    _ = (B * γ ^ 2 + B * K * γ + L * γ) * D.l ^ 2 / (8 * Real.pi * M) := by
        rw [hC, hΔ]
        field_simp
        ring

end Qatlib.Papers.ContourQET26.EigenTransform
