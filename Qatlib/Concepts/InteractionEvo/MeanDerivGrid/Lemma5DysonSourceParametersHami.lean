/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonSourceParametersStat
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonTruncationHami

/-!
# Sufficient parameters for Dyson grid approximation

`lemma5DysonSourceParameters` proves the Dyson approximation bound from an explicit grid-size
condition involving the derivative norm integral and a separate factorial tail bound. The
Hamiltonian is continuously differentiable, Hermitian, uniformly bounded, and restricted to a
short time interval. These estimates support the interaction-picture simulation analysis of
[LowWiebe2018].

## Main statements

* `lemma5DysonSourceParameters`: the source-parameter form of the truncation and discretization
  estimate.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Proves `Lemma5DysonSourceParameters`, giving error at most ε for the truncated Dyson grid
sum under the stated grid-size and tail conditions; see [Low and Wiebe, Lemma
5][LowWiebe2018]. -/
theorem lemma5DysonSourceParameters : Lemma5DysonSourceParameters := by
  intro I _ _ H Hd t Λ ε K M hH hHd hderiv ht hM hε hbound hlog hgrid htail
  apply lemma5DysonTruncation I H Hd t Λ ε K M hH hHd hderiv ht hM hε hbound hlog
  · let D : ℝ := ∫ u in (0 : ℝ)..t, ‖Hd u‖
    have hD : 0 ≤ D := intervalIntegral.integral_nonneg ht.le (fun _ _ => norm_nonneg _)
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    have he : Real.exp (Λ*t) ≤ 2 := by
      have hh := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
      exact hh
    have hb : 16*(t*D+Λ^2*t^2) ≤ (M : ℝ)*ε := by
      rw [div_le_iff₀ hε] at hgrid
      have hint : (∫ u in (0 : ℝ)..t, ‖Hd u‖+Λ^2) = D+t*Λ^2 := by
        rw [intervalIntegral.integral_add (hHd.norm.intervalIntegrable 0 t) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp [D, smul_eq_mul]
      rw [hint] at hgrid
      have hid : 16*t^2*((1/t)*(D+t*Λ^2)) = 16*(t*D+Λ^2*t^2) := by
        field_simp [ht.ne']
      rwa [hid] at hgrid
    change Real.exp (Λ*t)*Λ^2*t^2/(2*M)+(t/M)*D ≤ ε/2
    calc
      _ ≤ Λ^2*t^2/M+(t/M)*D := by
        apply add_le_add ?_ le_rfl
        have hnum := mul_le_mul_of_nonneg_right he (mul_nonneg (sq_nonneg Λ) (sq_nonneg t))
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*M)).mpr
        field_simp [hMr.ne']
        nlinarith
      _ = (Λ^2*t^2+t*D)/M := by ring
      _ ≤ ε/2 := by
        apply (div_le_iff₀ hMr).mpr
        nlinarith [mul_nonneg ht.le hD, mul_nonneg (sq_nonneg Λ) (sq_nonneg t)]
  · exact htail

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
