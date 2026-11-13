/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.TangentForcing
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.HigherOrder.Asymptotics

/-!
# Cancellation across flat contour crossings

Proves cancellation of higher-pole primitive differences across a flat crossing. Matching powers
of normalized one-sided tangents yield a vanishing difference along approaches with equal
radius.

`antiderivative_diff_across_crossing_tendsto_zero` is a local estimate used in the contour
analysis associated with [WangEtAl2026].

## Main statements

* `smul_pow_eq_of_div_norm_pow_eq`: Equality of powers of normalized tangent directions persists
  after both directions are scaled to the same real radius.
* `antiderivative_diff_across_crossing_tendsto_zero`: At an order-`n` flat crossing with nonzero
  one-sided derivatives, matching tangent powers make the difference of the order-`k` pole
  primitives tend to zero along equal-radius approaches, for `2 ≤ k ≤ n`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- Equality of powers of normalized tangent directions persists after both directions are
scaled to the same real radius. -/
theorem smul_pow_eq_of_div_norm_pow_eq (L_minus L_plus : ℂ) (k : ℕ)
    (h_B : (L_plus / (‖L_plus‖ : ℂ)) ^ (k - 1) = ((-L_minus) / (‖L_minus‖ : ℂ)) ^ (k - 1)) (ε : ℝ) :
    (((ε / ‖L_plus‖ : ℝ) • L_plus : ℂ)) ^ (k - 1) =
    (((ε / ‖L_minus‖ : ℝ) • (-L_minus) : ℂ)) ^ (k - 1) := by
  have h_smul : ∀ (r : ℝ) (v : ℂ), ((ε / r : ℝ) • v : ℂ) = (ε : ℂ) * (v / (r : ℂ)) := by
    intro r v
    rw [Complex.real_smul]
    push_cast
    rw [div_mul_eq_mul_div, mul_div_assoc]
  rw [h_smul ‖L_plus‖ L_plus, h_smul ‖L_minus‖ (-L_minus), mul_pow, mul_pow, h_B]

/-- At an order-`n` flat crossing with nonzero one-sided derivatives, matching tangent powers
make the difference of the order-`k` pole primitives tend to zero along equal-radius
approaches, for `2 ≤ k ≤ n`. -/
theorem antiderivative_diff_across_crossing_tendsto_zero
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L_minus L_plus : ℂ} {n k : ℕ} (h_flat : FlatOfOrder γ t₀ n)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L_plus (Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L_minus (Iio t₀) t₀)
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (h_B : (L_plus / (‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (‖L_minus‖ : ℂ)) ^ (k - 1)) {t_eps_plus t_eps_minus : ℝ → ℝ}
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] (0 : ℝ)) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] (0 : ℝ)) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_minus ε) - s‖ = ε) :
    Tendsto (fun ε =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  subst h_s
  have hn1 : 1 ≤ n := by omega
  have h_right := antiderivative_diff_at_tangent_target_tendsto_zero_right hL_plus
    h_deriv_right rfl (h_flat.tangentDeviation_isLittleO_right hn1 hL_plus h_deriv_right) hk hkn
  have h_left := antiderivative_diff_at_tangent_target_tendsto_zero_left hL_minus
    h_deriv_left rfl (h_flat.tangentDeviation_isLittleO_left hn1 hL_minus h_deriv_left) hk hkn
  have h_sum := (h_right.comp h_plus_to).add (h_left.comp h_minus_to)
  rw [add_zero] at h_sum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [h_plus_radius, h_minus_radius] with ε hpr hmr
  simp only [Function.comp_apply]
  have h_targets :
      -(↑(k - 1) : ℂ)⁻¹ *
        (((γ t₀ + (‖γ (t_eps_minus ε) - γ t₀‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - γ t₀)
          ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ *
        (((γ t₀ + (‖γ (t_eps_plus ε) - γ t₀‖ / ‖L_plus‖ : ℝ) • L_plus) - γ t₀)
          ^ (k - 1))⁻¹ := by
    rw [hmr, norm_neg, hpr]
    congr 2
    rw [add_sub_cancel_left, add_sub_cancel_left]
    exact (smul_pow_eq_of_div_norm_pow_eq L_minus L_plus k h_B ε).symm
  rw [h_targets, norm_sub_rev (-(↑(k - 1) : ℂ)⁻¹ *
    ((γ (t_eps_plus ε) - γ t₀) ^ (k - 1))⁻¹), add_comm]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
