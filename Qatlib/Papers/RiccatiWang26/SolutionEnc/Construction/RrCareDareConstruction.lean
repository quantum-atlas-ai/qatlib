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

/-- Arithmetic core associated with Proposition E.5: bounds the two chosen accuracies and proves positivity of the logarithm argument. The query formula is assumed; no encoding or query bound is derived. -/
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
  -- Scope note: this theorem bounds the chosen accuracies and proves positivity of
  -- the logarithm's argument. Product-error propagation and pseudoinverse threshold
  -- analysis (Proposition 2.6 and Lemma A.2) are outside the scope of this file.
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

/-- Arithmetic core associated with Proposition E.6: proves positivity of `η` and `1 + σminInit⁻¹` and returns the assumed normalization identity. No seed implementation or total query bound is constructed. -/
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
  -- Scope note: this theorem proves positivity of `η` and `1 + σminInit⁻¹` and records
  -- the assumed raw normalization. The six error-budget estimates, the
  -- `σmin(Π>R₀)/2` threshold analysis and quadrature node count (E.26) are outside
  -- the scope of this file.
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

/-- Arithmetic core associated with Corollary E.7: proves only nonnegativity of the displayed normalization expression. The output-normalization bound is assumed. -/
theorem corollary_E_7_rr_output_normalization
    (αPk M RRR αR0 σminInit C : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ RRR) (hαR0 : 0 ≤ αR0) (hσ : 0 < σminInit) (hC : 0 < C)
    (hα : αPk ≤ C * (Real.sqrt (1 + M ^ 2) * RRR + αR0 * RRR ^ 2 / σminInit)) :
    0 ≤ Real.sqrt (1 + M ^ 2) * RRR + αR0 * RRR ^ 2 / σminInit := by
  -- Source: Cor. E.7 (p. 76).  Same shape as Corollary D.7: the `[I;P]` factor contributes
  -- `√(1+M²)` and the initial pseudoinverse contributes `αR₀/σmin(Π>R₀)` with two powers of
  -- `RRR` from the contour normalization.
  -- Scope note: this theorem proves nonnegativity of the normalization expression.
  -- Deriving (E.27) from (E.24) using the singular-value estimate, the threshold
  -- `σmin(Π>R₀)/2` and the bound `α_{Π>} ≤ √(1+M²)` is outside the scope of this file.
  have h1 : 0 ≤ Real.sqrt (1 + M ^ 2) := Real.sqrt_nonneg _
  have h2 : 0 ≤ αR0 * RRR ^ 2 / σminInit :=
    div_nonneg (mul_nonneg hαR0 (sq_nonneg RRR)) hσ.le
  exact add_nonneg (mul_nonneg h1 hR) h2

/-! ## Lemma F.6: DARE normalization on the unit circle -/

/-- Conditional normalization arithmetic associated with Lemma F.6: propagates the assumed contour and quadrature estimates through `αPi = αL * αDARE`. No trapezoidal implementation or query cost is constructed. -/
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
  -- Scope note: the trapezoidal normalization estimate and standard-pencil constants
  -- are supplied as hypotheses. The theorem propagates the estimate through
  -- `αΠ< = αL αDARE`; deriving the identity
  -- `Σ_{j<m} (1/m)/(α_L + α_M) = 1/(α_M+α_L)` is outside the scope of this file.
  refine ⟨hα, ?_⟩
  rw [hPi]
  calc αL * αDARE ≤ αL * (cβ / (αM + αL) * RDARE) :=
        mul_le_mul_of_nonneg_left (hα.trans hsum) hαL
    _ = (cβ * αL / (αM + αL)) * RDARE := by ring

/-! ## Proposition F.7: DARE on the unit circle -/

/-! ## Proposition F.8: DARE through a Cayley transformation -/

/-- Arithmetic core associated with Proposition F.8: proves positivity of `αC` and `αX` and returns the assumed Cayley error bound. No selector implementation, decoded-error construction or query cost is derived. -/
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
  -- Scope note: this theorem proves positivity of the chosen normalizations and
  -- retains the assumed Cayley error bound. The contraction argument and selector
  -- error decomposition (C.4) under (F.36) are outside the scope of this file.
  refine ⟨?_, ?_, hεC⟩
  · rw [hαC]; linarith
  · rw [hαX]
    have h2 : 0 < Real.sqrt (1 + Xnorm ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [sq_nonneg Xnorm])
    exact mul_pos (mul_pos (by norm_num) hαSr) h2

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Construction
