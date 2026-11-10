/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.ComputedGrid.Lemma5DysonComputedParametersStat
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.ComputedGrid
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem lemma5DysonComputedParameters : Lemma5DysonComputedParameters := by
  intro I _ _ H Hd t Λ χ k hH hHd hderiv ht hΛ hχ hbound hlog hmean
  obtain ⟨h1,hK,_hcut,_hlen,hreads,hsame,hproducts⟩ :=
    computedDysonGridRun_structure I H t Λ χ k
  refine ⟨h1,hK,hreads,hproducts,?_⟩
  let M := computedDysonGridSize t Λ χ k
  have hM : 0<M := by change 1 ≤ M at h1; omega
  have hMr : (0:ℝ)<M := Nat.cast_pos.mpr hM
  let ε : ℝ := (1/2:ℝ)^k
  have hε : 0<ε := by dsimp [ε]; positivity
  have hpow : (2:ℝ)^k*ε=1 := by
    dsimp [ε]
    rw [div_pow,one_pow]
    field_simp
  have hceil : 16*t^2*(χ+Λ^2)*(2:ℝ)^k ≤ (M:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hgrid : 16*t^2*(χ+Λ^2) ≤ (M:ℝ)*ε := by
    calc
      _ = 16*t^2*(χ+Λ^2)*((2:ℝ)^k*ε) := by rw [hpow,mul_one]
      _ = (16*t^2*(χ+Λ^2)*(2:ℝ)^k)*ε := by ring
      _  ≤  _ := mul_le_mul_of_nonneg_right hceil hε.le
  have he : Real.exp (Λ*t) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  have hdisc : Real.exp (Λ*t)*Λ^2*t^2/(2*M)+
      (t/M)*(∫u in (0:ℝ)..t,‖Hd u‖) ≤ ε/16 := by
    calc
      _  ≤  Λ^2*t^2/M+(t/M)*(χ*t) := by
        apply add_le_add ?_ (mul_le_mul_of_nonneg_left hmean (by positivity))
        have hnum := mul_le_mul_of_nonneg_right he (mul_nonneg (sq_nonneg Λ) (sq_nonneg t))
        apply (div_le_iff₀ (by positivity : (0:ℝ)<2*M)).mpr
        field_simp [hMr.ne']
        nlinarith
      _ = t^2*(χ+Λ^2)/M := by ring
      _  ≤  _ := by
        apply (div_le_iff₀ hMr).mpr
        nlinarith
  have htail := computedDysonCutoff_tail_and_rate.1 k (Λ*t) (mul_nonneg hΛ ht) hlog
  have hjoint := dyson_truncated_grid_joint_error I H Hd t Λ M (computedDysonCutoff k)
    hH ht hΛ hM hbound hHd hderiv hlog
  rw [hsame]
  change ‖dysonGridTruncatedSum H t M (computedDysonCutoff k)-
    orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤ ε
  exact hjoint.trans (by dsimp only [ε] at hdisc ⊢; nlinarith [hε])

end Qatlib.Concepts.InteractionEvo.ComputedGrid
