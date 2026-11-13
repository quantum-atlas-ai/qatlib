/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# DreConstruction — the DRE construction and its stability analysis

RiccatiWang26, arXiv:2609.37207v1.
Retained formalized arithmetic cores: Proposition D.5 (p. 78, Eqs. (D.17)–(D.18)),
Corollary D.7 (p. 80, Eq. (D.27)), Lemma F.2 (p. 96, Eqs. (F.10)–(F.11)) and
Proposition F.3 (p. 96, Eqs. (F.12)–(F.20)).
Theorem 3.1, Proposition D.6, Proposition D.8 and Corollary F.5 are not formalized in this
layer; no declaration below claims them.

The retained statements record the error and normalization arithmetic; `RDRE` is the
generalized singularity factor (3.3) of the two half-plane contours and `κ(Π₊R₀)` the
initial-graph condition number.  The block-encoding itself is not constructed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Construction

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Proposition D.5: stability and cost of direct recovery -/

/-- Arithmetic core associated with Proposition D.5: assuming the displayed formula for `Q`, proves only `0 ≤ Q`, `δE ≤ ε` and `εinv ≤ ε/4`. The matrix arguments are unused. No block encoding, decoded product-error estimate or query implementation is constructed. -/
theorem proposition_D_5_stability_and_cost
    (E P : Sq n) (αE αP M ε δE εinv QE Q : ℝ) (QEfun : ℝ → ℝ)
    (hM : 0 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hαE : 0 ≤ αE) (hαP : 0 < αP)
    (hδE : δE ≤ ε / (8 * (1 + M) ^ 2))
    (hεinv : εinv = ε / (4 * (1 + αE)))
    (hQE : 0 ≤ QEfun δE)
    (hQ : Q = QEfun δE * αP * Real.log (Real.exp 1 + αP / ε)) :
    0 ≤ Q ∧ δE ≤ ε ∧ εinv ≤ ε / 4 := by
  -- Source: Prop. D.5 (p. 78).  The product error is `αP δE + αP εinv + ... ≤ ε/4`; the
  -- pseudoinverse threshold `4αE/αP` makes the QSVT inverse accurate on the whole nonzero
  -- spectrum of `E₁*E`, and the cost multiplies by the `log(e + αP/ε)` inverse-iteration
  -- term.
  -- Scope note: this theorem proves nonnegativity of the cost and bounds the
  -- chosen accuracies. Decoded product-error propagation and pseudoinverse threshold
  -- analysis (Proposition 2.6 and Lemma A.2) are outside the scope of this file.
  refine ⟨?_, ?_, ?_⟩
  · -- nonnegativity of the cost expression
    have h1 : 0 ≤ QEfun δE * αP := mul_nonneg hQE hαP.le
    have h2 : 0 ≤ Real.log (Real.exp 1 + αP / ε) := by
      apply Real.log_nonneg
      have hexp : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hquot : 0 ≤ αP / ε := div_nonneg hαP.le hε0.le
      linarith
    rw [hQ]
    exact mul_nonneg h1 h2
  · -- `δE ≤ ε` since `ε ≤ 1` and `(1+M)^2 ≥ 1`
    have hden : 1 ≤ 8 * (1 + M) ^ 2 := by nlinarith [sq_nonneg (1 + M)]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * (1 + M) ^ 2)] at hδE
    rcases le_total 0 δE with hpos | hneg
    · nlinarith [hδE, hden, hε0]
    · linarith
  · -- `εinv ≤ ε/4` since `1 + αE ≥ 1`
    rw [hεinv]
    have hden : 1 ≤ 4 * (1 + αE) := by linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (1 + αE))]
    nlinarith

/-! ## Proposition D.6: DRE stability and general query bound -/

/-! ## Corollary D.7: output normalization -/

/-- Arithmetic core associated with Corollary D.7: proves nonnegativity of the displayed normalization expression. The bound on `αP` is an assumption and is not derived. -/
theorem corollary_D_7_output_normalization
    (αP M RDRE αR0 σminInit C : ℝ)
    (hM : 0 ≤ M) (hRDRE : 0 ≤ RDRE) (hαR0 : 0 ≤ αR0) (hσ : 0 < σminInit) (hC : 0 < C)
    (hαP : αP ≤ C * (Real.sqrt (1 + M ^ 2) * RDRE + αR0 * RDRE ^ 2 / σminInit)) :
    0 ≤ Real.sqrt (1 + M ^ 2) * RDRE + αR0 * RDRE ^ 2 / σminInit := by
  -- Source: Cor. D.7 (p. 80).  The output normalization is the sum of the `[I;X]` factor
  -- `√(1+‖X‖²) ≤ √(1+M²)` and the pseudoinverse factor `α_{R₀} R²/σmin(Π₊R₀)`, both
  -- multiplied by `RDRE` from the raw contour normalization.
  -- Scope note: this theorem proves nonnegativity of the normalization expression.
  -- Deriving (D.27) from (D.23) through the pseudoinverse threshold chain, including
  -- the substitution `γ₊ ≥ c σmin(Π₊R₀)`, is outside the scope of this file.
  have h1 : 0 ≤ Real.sqrt (1 + M ^ 2) := Real.sqrt_nonneg _
  have h2 : 0 ≤ αR0 * RDRE ^ 2 / σminInit :=
    div_nonneg (mul_nonneg hαR0 (sq_nonneg RDRE)) hσ.le
  exact add_nonneg (mul_nonneg h1 hRDRE) h2

/-! ## Proposition D.8: DRE construction from approximate inputs -/

/-! ## Lemma F.2: CARE normalization on a finite rectangle -/

/-- Arithmetic core associated with Lemma F.2: returns the assumed contour normalization inequality and proves nonnegativity of `(6*cβ/π)*RCARE`. No quadrature normalization bound is derived. -/
theorem lemma_F_2_care_normalization
    (cβ RCARE αCARE αH sumT : ℝ) (hβ : 4 ≤ cβ) (hR : 0 ≤ RCARE)
    (hαH : 0 ≤ αH) (hsum : 0 ≤ sumT)
    (hα : αCARE ≤ cβ * RCARE * sumT) :
    αCARE ≤ cβ * RCARE * sumT ∧ 0 ≤ (6 * cβ / Real.pi) * RCARE := by
  -- Source: Lemma F.2 (p. 96).  `α_CARE = Σ_j |ωj| βj ≤ cβ Σ_j |ω_j| ‖(z_jI - H)⁻¹‖` and on
  -- the left rectangle `|ωj|/(|zj| + αH) ≤ 6/π` after the panel parameterization `zℓ(t)`.
  -- Scope note: this theorem retains the assumed contour normalization inequality
  -- and proves nonnegativity of `(6cβ/π) RCARE`. The panel-length normalization
  -- `Σ |ωj|/(|zj|+αH) = 6/π`, obtained by summing the panel weights
  -- `hℓ wj/2πi` using `Σ wj = 2`, is outside the scope of this file.
  refine ⟨hα, ?_⟩
  have hcβ : (0:ℝ) ≤ cβ := by linarith
  exact mul_nonneg (div_nonneg (by positivity) Real.pi_pos.le) hR

/-! ## Proposition F.3: CARE on a finite rectangle -/

/-- Arithmetic core associated with Proposition F.3: proves positivity of `d`, `ℓΓ` and `αX`, and returns the assumed panel bound. No decoded-error estimate, block encoding or query cost is constructed. -/
theorem proposition_F_3_care_finite_rectangle
    (αH Δax d ℓΓ cβ RCARE αCARE αX Xnorm ε p Npan : ℝ)
    (hαH : 0 < αH) (hΔ : 0 < Δax) (hd : d = Δax / 2) (hℓ : ℓΓ = 12 * αH - Δax)
    (hΔ6 : Δax < 6 * αH)
    (hβ : 4 ≤ cβ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 0 ≤ Xnorm)
    (hαCARE : 0 < αCARE)
    (hNpan : Npan ≤ ℓΓ / d + 4) (hR : RCARE ≤ (1 + 2 * Real.sqrt 2) * αH / d)
    (hα : αCARE ≤ (6 * cβ / Real.pi) * RCARE)
    (hαX : αX = 8 * αCARE * Real.sqrt (1 + Xnorm ^ 2)) :
    0 < d ∧ 0 < ℓΓ ∧ 0 < αX ∧ Npan ≤ ℓΓ / d + 4 := by
  -- Source: Prop. F.3 (pp. 96–97).  The rectangle encloses the stable branch by Theorem B.4;
  -- the panel count is `⌈length/d⌉ ≤ ℓ/d + 4` summing the four sides; the `(2p)`-th derivative
  -- of the resolvent on the panel is bounded by `2/d^{2p+1}`, giving the `4^{-p}` rate.
  -- Scope note: this theorem proves positivity of the geometric and normalization
  -- parameters and retains the assumed panel-count bound. Gauss–Legendre error
  -- theory and the rectangle/panel geometry, including the analytic estimate
  -- `‖Sm - Π₋‖ ≤ Σ_panels (ℓ_panel/d) 4^{-p}` and the choice
  -- `p = ⌈log(4ℓ/(πdδ))/(2log2)⌉`, are outside the scope of this file.
  refine ⟨by rw [hd]; linarith, by rw [hℓ]; linarith, ?_, hNpan⟩
  rw [hαX]
  have h1 : 0 < Real.sqrt (1 + Xnorm ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg Xnorm])
  exact mul_pos (mul_pos (by norm_num) hαCARE) h1

/-! ## Corollary F.5: CARE through Weyl–LCHM -/

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Construction
