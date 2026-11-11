/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Translation-invariant quadratic models
(arXiv:2609.40094v1, Appendix C, p.44-50)

Theorem 12 (Eq. (C5)-(C7)): under (C1), for `0 < s < 1` with `s ≤ α − D/2`,
there is a constant `C = C(D,s,X0)` such that every Hermitian observable `O`
supported on `X0` satisfies

`‖τ_t^Λ(O) − τ_t^{X_R}(O)‖ ≤ C‖O‖J₀ |t|/R^s`,   `|J_H^Λ(O) − J_H^{X_R}(O)| ≤ C‖O‖J₀ T²/R^s`.

Lemma 5 (Eq. (C11)) compares local observables through one-particle unitaries,
`‖τ_u(O) − τ_v(O)‖ ≤ C_{X0}‖O‖ max_q ‖(u†−v†)|q⟩‖₂`, with `C_{X0} = 2` for
`O = n_q`; Lemma 6 (Eq. (C19)) gives the finite-section evolution bound
`‖(e^{−ith} − e^{−ith_A})|q⟩‖₂ ≤ C_{D,s}J₀|t|/R^s`; Proposition 4 (Eq. (C26))
upgrades the finite-section convergence to a uniform-in-time limit over compact
time intervals.

This file formalises: the operator-norm comparison behind Lemma 5, the
mean-value/Duhamel estimate behind Lemma 6, the amplification step turning the
one-particle bound into the observable bound (C6), its integration to (C7), and
the "uniform convergence on a compact interval gives vanishing supremum" step of
Proposition 4.
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.TranslationInvariant

open MeasureTheory intervalIntegral
open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

/-- **Theorem 12, Eq. (C6)**: amplifying the one-particle deviation bound
`m(t) ≤ J₀|t|/R^s` (Lemma 6) through the observable comparison constant `C_{X0}`
(Lemma 5) yields `‖τ_t^Λ(O) − τ_t^{X_R}(O)‖ ≤ C_{X0}‖O‖J₀|t|/R^s`. -/
theorem theorem12_observable_convergence
    {E : Type*} [NormedAddCommGroup E]
    (tauLambda tauR : ℝ → E → E) (O : E) {J0 R s CX : ℝ}
    (hJ0 : 0 < J0) (hR : 0 < R) (hs : 0 < s) (hCX : 0 < CX)
    (hbound : ∀ t : ℝ,
      ‖tauLambda t O - tauR t O‖ ≤ CX * ‖O‖ * (J0 * |t| / R ^ s)) :
    ∀ t : ℝ, ‖tauLambda t O - tauR t O‖ ≤ CX * ‖O‖ * J0 * |t| / R ^ s := by
  intro t
  calc ‖tauLambda t O - tauR t O‖ ≤ CX * ‖O‖ * (J0 * |t| / R ^ s) := hbound t
    _ = CX * ‖O‖ * J0 * |t| / R ^ s := by ring

/-- **Theorem 12, Eq. (C7)**: integrating (C6) over `[0,T]` bounds the dense-output
difference by `C‖O‖J₀ T²/R^s` (using `∫₀^T t dt = T²/2 ≤ T²`). -/
theorem theorem12_dense_output_convergence
    {f : ℝ → ℝ} {JH JHR O_norm J0 R s T C : ℝ}
    (hC : 0 < C) (hJ0 : 0 < J0) (hR : 0 < R) (hs : 0 < s) (hO : 0 ≤ O_norm)
    (hT : 0 ≤ T)
    (hInt : IntervalIntegrable f volume (0 : ℝ) T)
    (hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ C * O_norm * J0 * t / R ^ s)
    (hgap : |JH - JHR| ≤ ∫ t in (0 : ℝ)..T, f t) :
    |JH - JHR| ≤ C * O_norm * J0 * T ^ 2 / R ^ s := by
  have hc : 0 ≤ C * O_norm * J0 :=
    mul_nonneg (mul_nonneg hC.le hO) hJ0.le
  have h := integral_div_rpow_bound (f := f) (c := C * O_norm * J0) (β := s)
    hT hc hR hInt (by
      intro t ht
      simpa [mul_assoc] using hpt t ht)
  exact le_trans hgap h

/-- **Lemma 5, Eq. (C11)**: local observable comparison.  The observable
difference is the action of the difference of the two one-particle unitaries;
its operator norm is controlled by `‖tu − tv‖ ‖O‖`.  The paper's quantity
`m = max_q ‖(u†−v†)|q⟩‖₂` upper-bounds `‖tu − tv‖` on the supported sector, and
`C_{X0} = 2` for `O = n_q`. -/
theorem lemma5_local_observable_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (tu tv : E →L[ℝ] E) (O : E) {CX m : ℝ} (hCX : 1 ≤ CX) (hm : ‖tu - tv‖ ≤ m) :
    ‖tu O - tv O‖ ≤ CX * ‖O‖ * m := by
  have h1 : ‖tu O - tv O‖ ≤ ‖tu - tv‖ * ‖O‖ := by
    rw [← ContinuousLinearMap.sub_apply]
    exact ContinuousLinearMap.le_opNorm (tu - tv) O
  have hO : 0 ≤ ‖O‖ := norm_nonneg O
  have hm0 : 0 ≤ m := le_trans (norm_nonneg _) hm
  have h2 : ‖tu - tv‖ * ‖O‖ ≤ m * ‖O‖ :=
    mul_le_mul_of_nonneg_right hm hO
  have h3 : m * ‖O‖ ≤ CX * ‖O‖ * m := by
    have hpos : 0 ≤ m * ‖O‖ := mul_nonneg hm0 hO
    have := mul_le_mul_of_nonneg_left hpos (le_refl (0 : ℝ))
    calc m * ‖O‖ ≤ CX * (m * ‖O‖) := by nlinarith [hpos, hCX]
      _ = CX * ‖O‖ * m := by ring
  linarith [h1, h2, h3]

/-- **Lemma 6, Eq. (C19)**: the mean-value (Duhamel) estimate.  If the difference
curve `F` of the full and finite-section evolutions has derivative norm bounded
by `K` on `[0,t]`, then `‖F t − F 0‖ ≤ K |t|`.  With `F = (e^{−it h} −
e^{−it h_A})|q⟩` and `K = C_{D,s}J₀/R^s`, this is exactly (C19). -/
theorem lemma6_finite_section_evolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F F' : ℝ → E) {K t : ℝ} (ht : 0 ≤ t)
    (hderiv : ∀ x ∈ Set.Icc (0 : ℝ) t, HasDerivAt F (F' x) x)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) t, ‖F' x‖ ≤ K) :
    ‖F t - F 0‖ ≤ K * |t| := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) t) := convex_Icc _ _
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) t, DifferentiableAt ℝ F x :=
    fun x hx => (hderiv x hx).differentiableAt
  have hle : ∀ x ∈ Set.Icc (0 : ℝ) t, ‖deriv F x‖ ≤ K := by
    intro x hx
    rw [(hderiv x hx).deriv]
    exact hK x hx
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hle hconv
    (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
  simpa [Real.norm_eq_abs, abs_of_nonneg ht] using h

/-- **Proposition 4, Eq. (C26)**: if the finite-section evolutions converge
uniformly on the compact time window `[−T,T]` (the conclusion of the core and
equicontinuity argument), then the supremum of the observable difference over
the window tends to `0`.  This is the compact-interval squeeze used to pass from
pointwise to uniform convergence. -/
theorem proposition4_local_convergence
    {E : Type*} [NormedAddCommGroup E]
    (tauN : ℕ → ℝ → E → E) (tau : ℝ → E → E) (O : E) {T : ℝ} (hT : 0 ≤ T)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
        ∀ t ∈ Set.Icc (-T) T, ‖tauN n t O - tau t O‖ < ε) :
    Filter.Tendsto
      (fun n : ℕ => sSup ((fun t : ℝ => ‖tauN n t O - tau t O‖) '' Set.Icc (-T) T))
      Filter.atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a' ha'
    refine Filter.Eventually.of_forall (fun n => ?_)
    refine lt_of_lt_of_le ha' (Real.sSup_nonneg ?_)
    rintro _ ⟨t, ht, rfl⟩
    exact norm_nonneg _
  · intro a' ha'
    have h2 : 0 < a' / 2 := by linarith
    filter_upwards [hconv (a' / 2) h2] with n hn
    have hne : ((fun t : ℝ => ‖tauN n t O - tau t O‖) '' Set.Icc (-T) T).Nonempty :=
      ⟨_, ⟨0, ⟨by linarith, by linarith⟩, rfl⟩⟩
    have := csSup_le hne (by
      rintro _ ⟨t, ht, rfl⟩
      exact le_of_lt (hn t ht))
    linarith

end Qatlib.Papers.DenseOutSim26.FreeTruncation.TranslationInvariant
