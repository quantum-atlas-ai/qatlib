/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# RrCareDareConstruction — the RR, CARE and DARE constructions

RiccatiWang26, arXiv:2609.37207v1.
Retained formalized arithmetic cores: Proposition E.5 (p. 74, Eqs. (E.21)–(E.22)),
Proposition E.6 (p. 75, Eqs. (E.23)–(E.26)), Corollary E.7 (p. 76, Eq. (E.27)),
Lemma F.6 (p. 101, Eqs. (F.25)–(F.26)) and Proposition F.8 (p. 103, Eqs. (F.34)–(F.37)).
Theorems 3.4, 3.5, 3.7 (RR/CARE/DARE constructions) and Proposition F.7 are not
formalized in this layer; no declaration below claims them.

Each retained theorem records the arithmetic consequences that the subsequent appendices
use.  The quantum circuit content (contour LCU, pseudoinverse recovery, selector
composition) is not constructed at this layer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Construction

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Theorem 3.4: RR construction -/

/-! ## Theorem 3.5: CARE construction -/

/-! ## Theorem 3.7: DARE construction -/

/-! ## Proposition E.5: stability and cost of direct recovery -/

/-- RiccatiWang26, Proposition E.5 (p. 74), Eqs. (E.21)–(E.22).  If an encoding of `E_k` with
known normalization `αEk ≥ 1` and decoded error at most `δ` costs `QEk(δ)` queries per call,
then for `0 < ε ≤ 1` the choices `δ = ε/(8(1+M²))` and `εinv = ε/(4(1+αEk))` give projector and
inverse-implementation errors below the `ε/4` product budget; with inverse threshold
`4αEk/αPk` the result has error at most `ε` and query cost
`O(QEk(δ) αPk log(e + αPk/ε))`. -/
theorem proposition_E_5_rr_stability_and_cost
    (αEk αPk M ε δ εinv Q QEk : ℝ) (QEkfun : ℝ → ℝ)
    (hαEk : 1 ≤ αEk) (hM : 0 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hαP : 0 < αPk)
    (hδ : δ = ε / (8 * (1 + M ^ 2)))
    (hεinv : εinv = ε / (4 * (1 + αEk)))
    (hQ : Q = QEkfun δ * αPk * Real.log (Real.exp 1 + αPk / ε)) :
    δ ≤ ε ∧ εinv ≤ ε / 4 ∧ 0 < Real.exp 1 + αPk / ε := by
  -- Source: Prop. E.5 (p. 74).  Identical to Proposition D.5 with `E_k` in place of `E(t)`:
  -- the product-error budget is `αPk δ + αPk εinv + ... ≤ ε/4` and the threshold
  -- `4αEk/αPk` keeps the QSVT inverse accurate on the nonzero spectrum.
  -- Lean gap: the product-error propagation and pseudoinverse threshold analysis.
  -- Candidate dependencies: `proposition_2_6_inverse_primitive`,
  -- `lemma_A_2_inverse_perturbation`.
  -- Suggested follow-up: prove `αPk δ ≤ ε/8` and `αPk εinv ≤ ε/4`, then sum.
  refine ⟨?_, ?_, ?_⟩
  · rw [hδ]
    have hden : 1 ≤ 8 * (1 + M ^ 2) := by nlinarith [sq_nonneg M]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 8 * (1 + M ^ 2))]
    nlinarith [hε0.le, hden]
  · rw [hεinv]
    have hden : 1 ≤ 4 * (1 + αEk) := by linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (1 + αEk))]
    nlinarith [hε0.le, hden]
  · have h1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : 0 ≤ αPk / ε := div_nonneg hαP.le hε0.le
    linarith

/-! ## Proposition E.6: seed construction and total query bound -/

/-- RiccatiWang26, Proposition E.6 (p. 75), Eqs. (E.23)–(E.26).  There is an absolute `c > 0`
such that the common accuracy (E.23) suffices for the four weighted targets, the initial
pseudoinverse and every fixed sum/product/normalization reduction used to assemble `E_k`.
With threshold `σmin(Π>R₀)/2` direct composition gives the raw normalization (E.24); combined
with direct recovery the query bound is (E.25), and a common node count for each target is
(E.26), which does not multiply the coherent query bound. -/
theorem proposition_E_6_seed_construction
    (M αInit αSmR αSinvR αEq γR σminInit αEr αPk ε η Q RRR rE rT αR0 Qmax : ℝ)
    (hM : 0 ≤ M) (hε : 0 < ε) (hR : 0 ≤ RRR) (hσ : 0 < σminInit)
    (hαInit : 0 ≤ αInit) (hαSmR : 0 ≤ αSmR) (hαSinvR : 0 ≤ αSinvR)
    (hη : η = ε / ((1 + M ^ 2) * (1 + αInit) * (1 + αSmR) * (1 + αSinvR) *
      (1 + σminInit⁻¹) ^ 2))
    (hEr : αEr = αInit + 8 * αSmR * αSinvR / σminInit)
    (hQ : Q = RRR * (αInit / σminInit) * αPk * rE * rT *
      (Real.log (Real.exp 1 + RRR * (1 + αPk) * (1 + σminInit⁻¹) * (1 + Qmax) / η)) ^ 3) :
    0 < η ∧ 0 < 1 + σminInit⁻¹ ∧ αEr = αInit + 8 * αSmR * αSinvR / σminInit := by
  -- Source: Prop. E.6 (p. 75).  `η` is the minimum of the six error budgets; each weighted
  -- target is assembled by a contour LCU at that accuracy, and the raw normalization (E.24)
  -- comes from the direct sum of `α_{Π>}` and the product skeleton.
  -- Lean gap: the six-way error-budget arithmetic, the `σmin(Π>R₀)/2` threshold analysis and
  -- the quadrature node count (E.26).
  -- Candidate dependencies: `proposition_D_8_dre_approximate_inputs`,
  -- `lemma_E_1_forward_propagation`.
  -- Suggested follow-up: prove each of the six contributions `≤ η` by the perturbation bounds
  -- of Proposition A.5, then combine with the recovery cost of Proposition E.5.
  refine ⟨?_, ?_, hEr⟩
  · rw [hη]
    have h2 : (0:ℝ) < 1 + σminInit⁻¹ := by
      have h2' : 0 < σminInit⁻¹ := inv_pos.mpr hσ
      linarith
    have h3 : (0:ℝ) < (1 + M ^ 2) * (1 + αInit) * (1 + αSmR) * (1 + αSinvR) := by
      positivity
    have h4 : (0:ℝ) < (1 + σminInit⁻¹) ^ 2 := pow_pos h2 2
    exact div_pos hε (mul_pos h3 h4)
  · have h2 : (0:ℝ) < 1 + σminInit⁻¹ := by
      have : 0 < σminInit⁻¹ := inv_pos.mpr hσ
      linarith
    linarith

/-! ## Corollary E.7: RR output normalization -/

/-- RiccatiWang26, Corollary E.7 (p. 76), Eq. (E.27).  For the contours and quadrature of
Proposition E.4, a constant-factor initial singular-value estimate and direct sums and products
give `αPk = O(√(1+M²) RRR + αR₀ RRR²/σmin(Π>R₀))`, reducing to (3.14) when `M, αR₀ = O(1)`. -/
theorem corollary_E_7_rr_output_normalization
    (αPk M RRR αR0 σminInit C : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ RRR) (hαR0 : 0 ≤ αR0) (hσ : 0 < σminInit) (hC : 0 < C)
    (hα : αPk ≤ C * (Real.sqrt (1 + M ^ 2) * RRR + αR0 * RRR ^ 2 / σminInit)) :
    0 ≤ Real.sqrt (1 + M ^ 2) * RRR + αR0 * RRR ^ 2 / σminInit := by
  -- Source: Cor. E.7 (p. 76).  Same shape as Corollary D.7: the `[I;P]` factor contributes
  -- `√(1+M²)` and the initial pseudoinverse contributes `αR₀/σmin(Π>R₀)` with two powers of
  -- `RRR` from the contour normalization.
  -- Lean gap: the derivation of (E.27) from (E.24) and the singular-value estimate.
  -- Candidate dependencies: `proposition_E_6_seed_construction`.
  -- Suggested follow-up: substitute the threshold `σmin(Π>R₀)/2` into (E.24) and use
  -- `α_{Π>} ≤ √(1+M²)`.
  have h1 : 0 ≤ Real.sqrt (1 + M ^ 2) := Real.sqrt_nonneg _
  have h2 : 0 ≤ αR0 * RRR ^ 2 / σminInit :=
    div_nonneg (mul_nonneg hαR0 (sq_nonneg RRR)) hσ.le
  exact add_nonneg (mul_nonneg h1 hR) h2

/-! ## Lemma F.6: DARE normalization on the unit circle -/

/-- RiccatiWang26, Lemma F.6 (p. 101), Eqs. (F.25)–(F.26).  With the uniform node constant
`cβ` from (F.6) the DARE contour normalization obeys
`αDARE ≤ cβ RDARE Σ_j |ωj|/(|zj|αL + αM)`.  On the counterclockwise unit circle with the
trapezoidal rule `zj = e^{2πij/m}`, `ωj = zj/m`, the standard pencil (3.24) gives
`αDARE ≤ cβ RDARE/(αM+αL) ≤ cβ RDARE/2` and `αΠ< = αL αDARE ≤ (cβ αL/(αM+αL)) RDARE =
O(RDARE)`, uniformly in `m` and without normalization reduction. -/
theorem lemma_F_6_dare_normalization
    (cβ RDARE αDARE αPi αL αM sumT : ℝ)
    (hβ : 0 ≤ cβ) (hR : 0 ≤ RDARE) (hαL : 0 ≤ αL) (hden : 0 < αM + αL)
    (hα : αDARE ≤ cβ * RDARE * sumT)
    (hsum : cβ * RDARE * sumT ≤ cβ / (αM + αL) * RDARE)
    (hPi : αPi = αL * αDARE) :
    αDARE ≤ cβ * RDARE * sumT ∧ αPi ≤ (cβ * αL / (αM + αL)) * RDARE := by
  -- Source: Lemma F.6 (p. 101).  `α_DARE = Σ_j |ω_j| β_j ≤ cβ Σ_j |ω_j| ‖(z_jL - M)⁻¹‖`; for
  -- the trapezoidal unit circle `Σ_j |ω_j|/(|z_j|α_L + α_M) = 1/(α_M + α_L)` because
  -- `|z_j| = 1` and `Σ_j 1/m = 1`.
  -- Lean gap: the trapezoidal-rule normalization identity and the standard-pencil constants.
  -- Candidate dependencies: `NodeInvEstimates`, `darePencilM`, `darePencilL` (PaperModel).
  -- Suggested follow-up: prove `Σ_{j<m} (1/m)/(α_L + α_M) = 1/(α_M+α_L)` and multiply by
  -- `cβ RDARE`.
  refine ⟨hα, ?_⟩
  rw [hPi]
  calc αL * αDARE ≤ αL * (cβ / (αM + αL) * RDARE) :=
        mul_le_mul_of_nonneg_left (hα.trans hsum) hαL
    _ = (cβ * αL / (αM + αL)) * RDARE := by ring

/-! ## Proposition F.7: DARE on the unit circle -/

/-! ## Proposition F.8: DARE through a Cayley transformation -/

/-- RiccatiWang26, Proposition F.8 (p. 103), Eqs. (F.34)–(F.37).  With `L` invertible,
`SD = L⁻¹M`, `SD + I` invertible, `CD = (SD - I)(SD + I)⁻¹` and `Π< = R₋[1; CD, I]`.  Given an
encoding of `SD` with normalization `αSD`, decoded error `εSD` and cost `QSD`, a constant upper
bound on `‖(SD+I)⁻¹‖`, `εSD‖(SD+I)⁻¹‖ ≤ 1/2` and the inverse access of Proposition 2.6, the
Cayley encoding obeys (F.35) for `ε+ > 0` with `(αSD+1)ε+ ≤ 1`.  Under the selector condition
(F.36) with the padded normalization `2αS₋,r`, direct recovery has decoded error at most `ε`,
output scale and query cost (F.37). -/
theorem proposition_F_8_dare_cayley
    (αSD εSD QSD βp εp αC εC Qc dS αSr εsel εcirc δ ε αX Xnorm QX : ℝ)
    (hβ : 0 < βp) (hβ2 : 2 ≤ βp) (hεp : 0 < εp) (hεSD : 0 ≤ εSD)
    (hαSD : 0 ≤ αSD) (hcond : (αSD + 1) * εp ≤ 1)
    (hαC : αC = 1 + 2 * βp)
    (hεC : εC ≤ 4 * βp ^ 2 * εSD + 2 * εp)
    (hε : 0 < ε) (hX : 0 ≤ Xnorm) (hdS : 0 ≤ dS) (hαSr : 0 < αSr)
    (hαX : αX = 16 * αSr * Real.sqrt (1 + Xnorm ^ 2)) :
    0 < αC ∧ 0 < αX ∧ εC ≤ 4 * βp ^ 2 * εSD + 2 * εp := by
  -- Source: Prop. F.8 (p. 103).  `C_D` is a contraction when `S_D` has spectrum in the left
  -- half plane; the Cayley error `4‖(S_D+I)⁻¹‖²ε_{S_D} + 2ε_+` comes from the two inverse
  -- calls of Proposition 2.6, and the selector (Proposition C.4) approximates the
  -- left-half-plane projector on `CD/αC`.
  -- Lean gap: the Cayley transformation's contraction property and the selector composition.
  -- Candidate dependencies: `proposition_2_6_inverse_primitive`,
  -- `proposition_C_4_branch_block_error`, `lemma_3_8_dare_graph_projector`.
  -- Suggested follow-up: prove `‖CD‖ ≤ 1` from the Cayley formula, then apply the Selector
  -- error decomposition (C.4) with the conditioning (F.36).
  refine ⟨?_, ?_, hεC⟩
  · rw [hαC]; linarith
  · rw [hαX]
    have h2 : 0 < Real.sqrt (1 + Xnorm ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [sq_nonneg Xnorm])
    exact mul_pos (mul_pos (by norm_num) hαSr) h2

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Construction
