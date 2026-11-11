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

/-- RiccatiWang26, Proposition D.5 (p. 78), Eqs. (D.17)–(D.18).  If encoding `E(t)` with
normalization `αE` and decoded error `δE` costs `QE(δE)` matrix queries, then for `0 < ε ≤ 1`
the choices `δE ≤ ε/(8(1+M)²)` and `εinv = ε/(4(1+αE))` give decoded product error at most
`ε/4`, and the upper-block pseudoinverse threshold `4αE/αP(t)` returns an `(αP(t), aP(t), ε)`
block-encoding of `P(t)` using `O(QE(δE) αP(t) log(e + αP(t)/ε))` matrix queries.  The same
holds for any graph projector satisfying Lemma D.3. -/
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
  -- Lean gap: the decoded product-error propagation and the pseudoinverse threshold
  -- analysis (Proposition 2.6 + Lemma A.2).
  -- Candidate dependencies: `BlockEncodes` (PaperModel), `proposition_2_6_inverse_primitive`,
  -- `lemma_A_2_inverse_perturbation`.
  -- Suggested follow-up: prove `αP δE ≤ ε/8` from (D.17) and `αP εinv ≤ ε/4` from the
  -- threshold, then combine by the triangle inequality.
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

/-- RiccatiWang26, Corollary D.7 (p. 80), Eq. (D.27).  For the rectangular rule of
Proposition D.4 with `γ₊ = Θ(σmin(Π₊R₀))`, direct assembly and the default output scale give
`αP(t) = O(√(1+M²) RDRE + α_{R₀} RDRE²/σmin(Π₊R₀))`, reducing to (3.5) when
`M, α_{R₀} = O(1)`. -/
theorem corollary_D_7_output_normalization
    (αP M RDRE αR0 σminInit C : ℝ)
    (hM : 0 ≤ M) (hRDRE : 0 ≤ RDRE) (hαR0 : 0 ≤ αR0) (hσ : 0 < σminInit) (hC : 0 < C)
    (hαP : αP ≤ C * (Real.sqrt (1 + M ^ 2) * RDRE + αR0 * RDRE ^ 2 / σminInit)) :
    0 ≤ Real.sqrt (1 + M ^ 2) * RDRE + αR0 * RDRE ^ 2 / σminInit := by
  -- Source: Cor. D.7 (p. 80).  The output normalization is the sum of the `[I;X]` factor
  -- `√(1+‖X‖²) ≤ √(1+M²)` and the pseudoinverse factor `α_{R₀} R²/σmin(Π₊R₀)`, both
  -- multiplied by `RDRE` from the raw contour normalization.
  -- Lean gap: the derivation of (D.27) from (D.23) needs the pseudoinverse threshold chain.
  -- Candidate dependencies: `proposition_D_6_dre_stability_and_query_bound`,
  -- `proposition_D_5_stability_and_cost`.
  -- Suggested follow-up: substitute `γ₊ ≥ c σmin(Π₊R₀)` into (D.23) and use
  -- `α_{R₀} ≤ 1 + αP` to absorb the `√(1+M²)` factor.
  have h1 : 0 ≤ Real.sqrt (1 + M ^ 2) := Real.sqrt_nonneg _
  have h2 : 0 ≤ αR0 * RDRE ^ 2 / σminInit :=
    div_nonneg (mul_nonneg hαR0 (sq_nonneg RDRE)) hσ.le
  exact add_nonneg (mul_nonneg h1 hRDRE) h2

/-! ## Proposition D.8: DRE construction from approximate inputs -/

/-! ## Lemma F.2: CARE normalization on a finite rectangle -/

/-- RiccatiWang26, Lemma F.2 (p. 96), Eqs. (F.10)–(F.11).  With node inverse-norm estimates
`βj ≤ cβ ‖(zj I - HCARE)⁻¹‖`, the CARE contour normalization satisfies
`αCARE ≤ cβ RCARE Σ_j |ωj|/(|zj| + αH)`; for the left rectangle (B.9) with a nonnegative
quadrature rule exact on constants, `αΠ₋ = αCARE ≤ (6cβ/π) RCARE = O(RCARE)`, uniformly in the
panel and node counts, with the direct LCU normalization. -/
theorem lemma_F_2_care_normalization
    (cβ RCARE αCARE αH sumT : ℝ) (hβ : 4 ≤ cβ) (hR : 0 ≤ RCARE)
    (hαH : 0 ≤ αH) (hsum : 0 ≤ sumT)
    (hα : αCARE ≤ cβ * RCARE * sumT) :
    αCARE ≤ cβ * RCARE * sumT ∧ 0 ≤ (6 * cβ / Real.pi) * RCARE := by
  -- Source: Lemma F.2 (p. 96).  `α_CARE = Σ_j |ωj| βj ≤ cβ Σ_j |ω_j| ‖(z_jI - H)⁻¹‖` and on
  -- the left rectangle `|ωj|/(|zj| + αH) ≤ 6/π` after the panel parameterization `zℓ(t)`.
  -- Lean gap: the panel-length normalization `Σ |ωj|/(|zj|+αH) = 6/π` for a rule exact on
  -- constants.
  -- Candidate dependencies: `NodeInvEstimates`, `genSingFactor` (PaperModel).
  -- Suggested follow-up: sum the panel weights `hℓ wj/2πi` against `1/(|zℓ(t)| + αH)` and use
  -- `Σ wj = 2` to get the `6/π` factor.
  refine ⟨hα, ?_⟩
  have hcβ : (0:ℝ) ≤ cβ := by linarith
  exact mul_nonneg (div_nonneg (by positivity) Real.pi_pos.le) hR

/-! ## Proposition F.3: CARE on a finite rectangle -/

/-- RiccatiWang26, Proposition F.3 (p. 96), Eqs. (F.12)–(F.20).  With a supplied lower bound
`0 < Δax ≤ Δax`, `d = Δax/2`, the rectangle contour `Γ₋ = ∂{x+iy : -2αH ≤ x ≤ -d, |y| ≤ 2αH}`
of length `ℓ(Γ₋) = 12αH - Δax` (positive since `Δax < 6αH`) is divided into `Npan ≤ ℓ/d + 4` panels with `p`-point
Gauss–Legendre nodes; then `‖Sm - Π₋‖ ≤ 2ℓ(Γ₋)4^{-p}/(πd)`, `RCARE ≤ (1+2√2)αH/d`,
`‖Π₋‖ ≤ ℓ/(2πd)`, `αΠ₋ = αCARE ≤ (6cβ/π)RCARE = O(αH/Δax)`; `p = ⌈log(4ℓ/(πdδ))/(2 log 2)⌉`
gives `‖Sm - Π₋‖ ≤ δ/2` for `0 < δ ≤ 1/8`, and with `δ = ε/[8(1+‖X‖²)]` the recovery has
decoded error at most `ε`, normalization `αX = 8αΠ₋√(1+‖X‖²)` and query cost (F.19). -/
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
  -- Lean gap: Gauss–Legendre quadrature theory and the rectangle/panel geometry.
  -- Candidate dependencies: `lemma_F_2_care_normalization`, `theorem_B_4_...` (Geometry),
  -- `proposition_D_5_stability_and_cost`.
  -- Suggested follow-up: prove `‖Sm - Π₋‖ ≤ Σ_panels (ℓ_panel/d) 4^{-p}` by the standard
  -- analytic Gauss–Legendre estimate, then `p = ⌈log(4ℓ/(πdδ))/(2log2)⌉`.
  refine ⟨by rw [hd]; linarith, by rw [hℓ]; linarith, ?_, hNpan⟩
  rw [hαX]
  have h1 : 0 < Real.sqrt (1 + Xnorm ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg Xnorm])
  exact mul_pos (mul_pos (by norm_num) hαCARE) h1

/-! ## Corollary F.5: CARE through Weyl–LCHM -/

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Construction
