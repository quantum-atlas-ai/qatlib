/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.RegularityConditions
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.OneSidedDerivLimit
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.HigherOrder.Asymptotics
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.SectorCancellation
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.WindowSplitting
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Higher-order poles on crossing windows

This module evaluates inverse-power contour integrals by endpoint primitives and proves their
vanishing on closed curves avoiding the pole. It then treats a distance-truncated crossing
window: flatness and a power-matching condition on the one-sided tangents cancel the singular
endpoint terms, supporting the residue analysis for [WangEtAl2026].

## Main statements

* `integral_pow_inv_mul_deriv_eq_zero_of_closed`: vanishing for closed avoiding curves.
* `perWindow_higherOrder_truncated_integral_tendsto`: the local truncated-integral limit.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- An inverse-power pole times the curve derivative is interval integrable along a continuous
curve avoiding the pole when its derivative is interval integrable. -/
private theorem intervalIntegrable_pow_inv_mul_deriv {γ : ℝ → ℂ} {s : ℂ} {l u : ℝ}
    (c : ℂ) (k : ℕ) (hlu : l ≤ u) (hγ_cont : ContinuousOn γ (Icc l u))
    (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume l u) :
    IntervalIntegrable (fun t => c / (γ t - s) ^ k * deriv γ t)
      MeasureTheory.volume l u := by
  refine hderiv_int.continuousOn_mul ?_
  rw [uIcc_of_le hlu]
  exact continuousOn_const.div ((hγ_cont.sub continuousOn_const).pow k)
    fun t ht => pow_ne_zero k (sub_ne_zero.mpr (h_ne t ht))

/-- For `k ≥ 2`, the inverse-power contour integral along an avoiding curve equals the
difference of its primitive at the endpoints, with differentiability allowed to fail on a
countable set. -/
theorem integral_pow_inv_mul_deriv_eq_sub {γ : ℝ → ℂ} {s : ℂ} {k : ℕ} (hk : 2 ≤ k) (c : ℂ)
    {l u : ℝ} (hlu : l ≤ u) {P : Set ℝ} (hP : P.Countable) (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (h_diff : ∀ t ∈ Ioo l u \ P, DifferentiableAt ℝ γ t) (hγ_cont : ContinuousOn γ (Icc l u))
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume l u) :
    ∫ t in l..u, c / (γ t - s) ^ k * deriv γ t =
      c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ u - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ l - s) ^ (k - 1))⁻¹) := by
  have h_G_deriv : ∀ t ∈ Ioo l u \ P,
      HasDerivAt (fun v => c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ v - s) ^ (k - 1))⁻¹))
        (c / (γ t - s) ^ k * deriv γ t) t := by
    intro t ht
    have h_F := (hasDerivAt_antiderivative_pow_inv hk
      (h_ne t (Ioo_subset_Icc_self ht.1))).const_mul c
    have h_chain := h_F.comp t (h_diff t ht).hasDerivAt
    rwa [show c * (1 / (γ t - s) ^ k) * deriv γ t =
        c / (γ t - s) ^ k * deriv γ t from by ring] at h_chain
  have h_G_cont : ContinuousOn
      (fun v => c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ v - s) ^ (k - 1))⁻¹)) (Icc l u) := fun t ht =>
    (((hasDerivAt_antiderivative_pow_inv hk (h_ne t ht)).continuousAt).const_mul
      c).comp_continuousWithinAt (hγ_cont t ht)
  exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le _ _ hlu hP h_G_cont
    h_G_deriv (intervalIntegrable_pow_inv_mul_deriv c k hlu hγ_cont h_ne hderiv_int)

/-- For ordered endpoints, the integral of an inverse-power pole of order at least two along a
closed piecewise C¹ curve avoiding the pole is zero. -/
private theorem integral_pow_inv_mul_deriv_eq_zero_of_closed_of_le {γ : ℝ → ℂ} {s : ℂ} {k : ℕ}
    (hk : 2 ≤ k) (c : ℂ) {a b : ℝ} (hab : a ≤ b) (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) (h_ne : ∀ t ∈ Icc a b, γ t ≠ s) :
    ∫ t in a..b, c / (γ t - s) ^ k * deriv γ t = 0 := by
  obtain ⟨P, hP, hdiff⟩ := hγ.exists_countable_differentiableAt
  rw [min_eq_left hab, max_eq_right hab] at hdiff
  have hcont : ContinuousOn γ (Icc a b) := by
    rw [← Set.uIcc_of_le hab]; exact hγ.continuousOn
  rw [integral_pow_inv_mul_deriv_eq_sub hk c hab hP h_ne hdiff hcont
    hγ.intervalIntegrable_deriv, hclosed, sub_self]

/-- The integral of an inverse-power pole of order at least two along a closed piecewise C¹
curve avoiding the pole is zero. -/
theorem integral_pow_inv_mul_deriv_eq_zero_of_closed {γ : ℝ → ℂ} {s : ℂ} {k : ℕ}
    (hk : 2 ≤ k) (c : ℂ) {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (h_ne : ∀ t ∈ uIcc a b, γ t ≠ s) :
    ∫ t in a..b, c / (γ t - s) ^ k * deriv γ t = 0 := by
  rcases le_total a b with hab | hba
  · exact integral_pow_inv_mul_deriv_eq_zero_of_closed_of_le hk c hab hγ hclosed
      fun t ht => h_ne t (by rwa [Set.uIcc_of_le hab])
  · rw [intervalIntegral.integral_symm b a,
      integral_pow_inv_mul_deriv_eq_zero_of_closed_of_le hk c hba hγ.symm hclosed.symm
        (fun t ht => h_ne t (by rw [Set.uIcc_comm, Set.uIcc_of_le hba]; exact ht)),
      neg_zero]

/-- Evaluates an inverse-power contour integral on a subinterval of a crossing window that
excludes its unique crossing parameter by the endpoint primitive difference. -/
private lemma integral_pow_inv_mul_deriv_eq_sub_of_subinterval {γ : ℝ → ℂ} {s : ℂ} {t_i r : ℝ}
    {k : ℕ} (hk : 2 ≤ k) (c : ℂ) {P : Set ℝ} (hP : P.Countable)
    (hγ_cont : ContinuousOn γ (Icc (t_i - r) (t_i + r)))
    (hγ_diffP : ∀ t ∈ Ioo (t_i - r) (t_i + r) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume (t_i - r) (t_i + r))
    (h_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ t = s → t = t_i)
    {l u : ℝ} (hlu : l ≤ u) (hl : t_i - r ≤ l) (hu : u ≤ t_i + r) (h_excl : t_i ∉ Icc l u) :
    ∫ t in l..u, c / (γ t - s) ^ k * deriv γ t =
      c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ u - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ l - s) ^ (k - 1))⁻¹) := by
  have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq =>
    h_excl (h_unique t ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_eq ▸ ht)
  exact integral_pow_inv_mul_deriv_eq_sub hk c hlu hP h_ne
    (fun t ht => hγ_diffP t ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, ht.2⟩)
    (hγ_cont.mono (Icc_subset_Icc hl hu))
    (hderiv_int.mono_set (by
      rw [uIcc_of_le hlu, uIcc_of_le (by linarith : t_i - r ≤ t_i + r)]
      exact Icc_subset_Icc hl hu))

/-- For an isolated flat crossing of order `n`, the distance-truncated integral of a pole of
order `2 ≤ k ≤ n` tends to the endpoint primitive difference when the normalized one-sided
tangents satisfy the stated power-matching condition. -/
theorem perWindow_higherOrder_truncated_integral_tendsto {γ : ℝ → ℂ} {s : ℂ} {t_i r : ℝ}
    {L_R L_L : ℂ} {n k : ℕ} {P : Set ℝ} (hr_pos : 0 < r) (h_at : γ t_i = s)
    (hγ_cont : ContinuousOn γ (Icc (t_i - r) (t_i + r))) (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t_i) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t_i) (𝓝 L_L)) (hP : P.Countable)
    (hγ_diffP : ∀ t ∈ Ioo (t_i - r) (t_i + r) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume (t_i - r) (t_i + r))
    (h_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ t = s → t = t_i)
    (h_flat : FlatOfOrder γ t_i n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h_B : (L_R / (‖L_R‖ : ℂ)) ^ (k - 1) = ((-L_L) / (‖L_L‖ : ℂ)) ^ (k - 1)) (c : ℂ) :
    Tendsto (fun ε : ℝ => ∫ t in (t_i - r)..(t_i + r),
        if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹))) := by
  classical
  have hγ_at : ContinuousAt γ t_i :=
    hγ_cont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have h_deriv_R : HasDerivWithinAt γ L_R (Ioi t_i) t_i :=
    TauCeti.hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero hγ_at.continuousWithinAt hL_R
      h_tendsto_R
  have h_deriv_L : HasDerivWithinAt γ L_L (Iio t_i) t_i :=
    TauCeti.hasDerivWithinAt_Iio_of_tendsto_deriv_of_ne_zero hγ_at.continuousWithinAt hL_L
      h_tendsto_L
  obtain ⟨τL, τR, h_toL, h_toR, h_radL, h_radR, h_memL, h_memR, h_split⟩ :=
    exists_exit_times_truncated_integral_split (by linarith) (by linarith) h_at hγ_cont hL_R hL_L
      h_tendsto_R h_tendsto_L h_unique (fun z => c / (z - s) ^ k)
      (fun ε hε a b ha hab hb => intervalIntegrable_pow_inv_mul_deriv_truncated c k
        (hγ_cont.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))
        (hderiv_int.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (by linarith : t_i - r ≤ t_i + r)]
          exact Icc_subset_Icc ha hb)) hε)
  have h_cancel := antiderivative_diff_across_crossing_tendsto_zero h_flat hL_L hL_R
    h_deriv_R h_deriv_L h_at hk hkn h_B h_toR h_radR h_toL h_radL
  have h_cancel_cx : Tendsto (fun ε =>
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τL ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τR ε) - s) ^ (k - 1))⁻¹))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr h_cancel
  have h_ev : (fun ε : ℝ => ∫ t in (t_i - r)..(t_i + r),
      if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
          c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹)) +
        c * ((-(↑(k - 1) : ℂ)⁻¹ * ((γ (τL ε) - s) ^ (k - 1))⁻¹) -
          (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τR ε) - s) ^ (k - 1))⁻¹)) := by
    filter_upwards [h_split, h_memL, h_memR] with ε hsplit hτL hτR
    rw [hsplit,
      integral_pow_inv_mul_deriv_eq_sub_of_subinterval hk c hP hγ_cont hγ_diffP hderiv_int h_unique
        hτL.1.le le_rfl (by linarith [hτL.2]) (fun h => absurd h.2 (by linarith [hτL.2])),
      integral_pow_inv_mul_deriv_eq_sub_of_subinterval hk c hP hγ_cont hγ_diffP hderiv_int h_unique
        hτR.2.le (by linarith [hτR.1]) le_rfl (fun h => absurd h.1 (by linarith [hτR.1]))]
    ring
  refine Tendsto.congr' h_ev.symm ?_
  have h_lim : Tendsto (fun ε =>
      (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹)) +
      c * ((-(↑(k - 1) : ℂ)⁻¹ * ((γ (τL ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (τR ε) - s) ^ (k - 1))⁻¹)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i + r) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_i - r) - s) ^ (k - 1))⁻¹)) + c * 0)) :=
    tendsto_const_nhds.add (h_cancel_cx.const_mul c)
  simpa using h_lim

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
