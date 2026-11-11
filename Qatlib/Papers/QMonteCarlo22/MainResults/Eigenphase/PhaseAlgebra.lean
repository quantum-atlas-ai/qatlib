/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option backward.isDefEq.respectTransparency false

/-!
# Eigenphase algebra for QMonteCarlo22 (arXiv:2208.07544v1, §3.2)

Fixed arXiv version: `2208.07544v1` (Kothari--O'Donnell, *Mean estimation when you
have the source code; or, quantum Monte Carlo methods*, 16 Aug 2022).
Source locations: Notation 3.4 and Propositions 3.6, 3.8 (pp. 12--14).

This module fixes the paper's haversine notation, the diagonal form of the phase
estimation unitary in its eigenbasis, and proves:

* Proposition 3.6: the Bhattacharyya coefficient of the two `J_U` laws is at least
  the modulus of the inner product of the starting states, and hence the squared
  Hellinger distance is at most `2 (1 - |⟨σ|τ⟩|)`.
* Proposition 3.8: for either exponent sign, the squared norm of the filtered
  state equals the `hav` (resp. reciprocal `hav`) expectation over `Θ_U`.
* Lemma 3.22: the one-dimensional numerical inequality used in §3.5.

The eigenbasis model is exactly Notation 3.4: `U = ∑_j e^{i θ_j} |u_j⟩⟨u_j|`,
so on coefficients `ψ_j = σ̂_j` the operators `(1-U)/2` and `((1-U)/2)^{-1}` act
diagonally with coefficients `(1 - e^{i θ_j})/2` and `2/(1 - e^{i θ_j})`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

namespace Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase

/-- Notation 3.7 (p. 14): the haversine of an angle,
`hav θ = sin²(θ/2) = (1 - cos θ)/2 ∈ [0,1]`. -/
noncomputable def hav (θ : ℝ) : ℝ := Real.sin (θ / 2) ^ 2

/-- Notation 3.7: the haversine is nonnegative. -/
theorem hav_nonneg (θ : ℝ) : 0 ≤ hav θ := by
  unfold hav; positivity

/-- Notation 3.7: the haversine is at most one. -/
theorem hav_le_one (θ : ℝ) : hav θ ≤ 1 := by
  unfold hav
  have h1 := Real.sin_le_one (θ / 2)
  have h2 := Real.neg_one_le_sin (θ / 2)
  nlinarith [sq_nonneg (Real.sin (θ / 2))]

/-- Notation 3.7: `hav θ = (1 - cos θ)/2`. -/
theorem hav_eq_half_one_sub_cos (θ : ℝ) : hav θ = (1 - Real.cos θ) / 2 := by
  unfold hav
  have hcos := Real.cos_two_mul' (θ / 2)
  have hsq := Real.sin_sq_add_cos_sq (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hcos
  nlinarith

/-- The diagonal phase coefficient `e^{i θ}` of the unitary in its eigenbasis. -/
noncomputable def phaseCoeff (θ : ℝ) : ℂ := Complex.exp (Complex.I * θ)

/-- The coefficient of `(1 - U)/2` in the eigenbasis. -/
noncomputable def filterCoeff (θ : ℝ) : ℂ := (1 - phaseCoeff θ) / 2

/-- The coefficient of `((1 - U)/2)^{-1}` in the eigenbasis. -/
noncomputable def invFilterCoeff (θ : ℝ) : ℂ := 2 / (1 - phaseCoeff θ)

/-- The squared modulus of `1 - e^{iθ}` is `4 hav θ`. -/
theorem normSq_one_sub_phaseCoeff (θ : ℝ) :
    Complex.normSq (1 - phaseCoeff θ) = 4 * hav θ := by
  unfold phaseCoeff
  have hre : (Complex.exp (Complex.I * θ)).re = Real.cos θ := by
    simpa [mul_comm] using Complex.exp_ofReal_mul_I_re θ
  have him : (Complex.exp (Complex.I * θ)).im = Real.sin θ := by
    simpa [mul_comm] using Complex.exp_ofReal_mul_I_im θ
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
  rw [hav_eq_half_one_sub_cos]
  have htrig := Real.sin_sq_add_cos_sq θ
  nlinarith

/-- The squared modulus of the filter coefficient is the haversine. -/
theorem normSq_filterCoeff (θ : ℝ) : ‖filterCoeff θ‖ ^ 2 = hav θ := by
  rw [Complex.sq_norm]
  unfold filterCoeff
  rw [Complex.normSq_div, normSq_one_sub_phaseCoeff]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by
    rw [Complex.normSq_apply]; norm_num
  rw [h2]
  ring

/-- When `hav θ ≠ 0`, the inverse filter coefficient has squared modulus
`(hav θ)^{-1}`. -/
theorem normSq_invFilterCoeff {θ : ℝ} (h : hav θ ≠ 0) :
    ‖invFilterCoeff θ‖ ^ 2 = (hav θ)⁻¹ := by
  rw [Complex.sq_norm]
  unfold invFilterCoeff
  rw [Complex.normSq_div, normSq_one_sub_phaseCoeff]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by
    rw [Complex.normSq_apply]; norm_num
  rw [h2]
  have h4 : (4 : ℝ) * hav θ ≠ 0 := by
    intro hz
    exact h (by nlinarith [hav_nonneg θ])
  field_simp [h4]

/-- Proposition 3.6 (p. 13): for normalized states `ψ, φ`, the Bhattacharyya
coefficient `BC(q,r) = ∑ᵢ √(qᵢ rᵢ)` of the `J_U` laws is at least
`|⟨ψ|φ⟩|`; i.e. the overlap modulus is no larger than the Bhattacharyya
coefficient. This is the paper's Inequality (20), first half. -/
theorem prop3_6 {I : Type*} [Fintype I] [DecidableEq I]
    (ψ φ : QState I) (_hψ : Normalized ψ) (_hφ : Normalized φ) :
    ‖Inner ψ φ‖ ≤ ∑ i, Real.sqrt (BornProb ψ i * BornProb φ i) := by
  have hF : ‖Inner ψ φ‖ ≤ ∑ i, ‖ψ i‖ * ‖φ i‖ := by
    rw [inner_apply]
    calc
      ‖∑ i, (starRingEnd ℂ) (ψ i) * φ i‖
          ≤ ∑ i, ‖(starRingEnd ℂ) (ψ i) * φ i‖ := norm_sum_le _ _
      _ = ∑ i, ‖ψ i‖ * ‖φ i‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul]
        simp
  have hBC : (∑ i, Real.sqrt (BornProb ψ i * BornProb φ i)) =
      ∑ i, ‖ψ i‖ * ‖φ i‖ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [BornProb, BornProb, ← mul_pow]
    exact Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [hBC]
  exact hF

/-- Squared Hellinger distance of two finite probability laws, with the paper's
normalization `H(q,r)² = ∑ᵢ (√qᵢ - √rᵢ)² = 2(1 - BC(q,r))`. -/
noncomputable def hellingerSq {I : Type*} [Fintype I] (q r : I → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (q i) - Real.sqrt (r i)) ^ 2

/-- Proposition 3.6 (p. 13), second half: `H(q,r)² ≤ 2(1 - |⟨ψ|φ⟩|)`
whenever `q, r` are the `J_U` Born laws of two normalized states, the latter
being probability laws (`∑ q = ∑ r = 1`). -/
theorem prop3_6_hellinger {I : Type*} [Fintype I] [DecidableEq I]
    (ψ φ : QState I) (hψ : Normalized ψ) (hφ : Normalized φ) :
    hellingerSq (BornProb ψ) (BornProb φ) ≤ 2 * (1 - ‖Inner ψ φ‖) := by
  have hqsum : ∑ i, BornProb ψ i = 1 := hψ
  have hrsum : ∑ i, BornProb φ i = 1 := hφ
  have hq0 : ∀ i, 0 ≤ BornProb ψ i := fun i => by unfold BornProb; positivity
  have hr0 : ∀ i, 0 ≤ BornProb φ i := fun i => by unfold BornProb; positivity
  have hterm : ∀ i, (Real.sqrt (BornProb ψ i) - Real.sqrt (BornProb φ i)) ^ 2 =
      BornProb ψ i + BornProb φ i -
        2 * (Real.sqrt (BornProb ψ i) * Real.sqrt (BornProb φ i)) := by
    intro i
    have h1 := Real.sq_sqrt (hq0 i)
    have h2 := Real.sq_sqrt (hr0 i)
    nlinarith [h1, h2]
  have hexp : hellingerSq (BornProb ψ) (BornProb φ) =
      2 - 2 * ∑ i, Real.sqrt (BornProb ψ i * BornProb φ i) := by
    unfold hellingerSq
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hqsum, hrsum]
    rw [show (∑ i, 2 * (Real.sqrt (BornProb ψ i) * Real.sqrt (BornProb φ i))) =
        2 * ∑ i, Real.sqrt (BornProb ψ i * BornProb φ i) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.sqrt_mul (hq0 i)]]
    ring
  rw [hexp]
  have hBC := prop3_6 ψ φ hψ hφ
  nlinarith

/-- Lemma 3.22 (p. 17): for real `h, λ` with `h > 0`,
`(1 - h⁻¹)² ≤ (1 - λ)² + (λ h - h⁻¹)²`.
The paper's proof notes the difference of the two sides is
`λ² (1 - h)² + 2 h (λ - h⁻¹)² ≥ 0`. -/
theorem lemma3_22 (h lam : ℝ) (hh : 0 < h) :
    (1 - h⁻¹) ^ 2 ≤ (1 - lam) ^ 2 + (lam * h - h⁻¹) ^ 2 := by
  have hhne : h ≠ 0 := ne_of_gt hh
  have key : (1 - lam) ^ 2 + (lam * h - h⁻¹) ^ 2 - (1 - h⁻¹) ^ 2 =
      lam ^ 2 * (1 - h) ^ 2 + 2 * h * (lam - h⁻¹) ^ 2 := by
    field_simp [hhne]
    ring
  nlinarith [sq_nonneg (lam * (1 - h)), sq_nonneg (lam - h⁻¹), hh.le,
    mul_nonneg (show (0:ℝ) ≤ 2 * h by positivity) (sq_nonneg (lam - h⁻¹))]

end Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase
