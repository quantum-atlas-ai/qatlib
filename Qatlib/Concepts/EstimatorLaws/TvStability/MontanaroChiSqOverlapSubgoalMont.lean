/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChiSqOverlapSubgoalStat
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroScheduleDefs
open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

private theorem inverse_sqrt_tangent (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (3*v-u)/(2*v*Real.sqrt v) ≤ 1/Real.sqrt u := by
  have ha := Real.sqrt_pos.2 hu
  have hb := Real.sqrt_pos.2 hv
  apply (div_le_div_iff₀ (by positivity) ha).2
  have hp := mul_nonneg (sq_nonneg (Real.sqrt u - Real.sqrt v))
    (show 0 ≤ Real.sqrt u + 2*Real.sqrt v by positivity)
  rw [← Real.sq_sqrt (le_of_lt hu), ← Real.sq_sqrt (le_of_lt hv)]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg u), Real.sqrt_sq (Real.sqrt_nonneg v)]
  nlinarith

theorem montanaroChiSqOverlapSubgoal : MontanaroChiSqOverlapSubgoal := by
  intro X _ _ ν π hπ hν
  let g := fun x => ν.prob x / π.prob x
  let T := ∑ x, ν.prob x * g x
  have hg (x : X) : 0 < g x := div_pos (hν x) (hπ x)
  have hne : (Finset.univ : Finset X).Nonempty := by
    by_contra h
    have hs := ν.sum_one
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hs
    norm_num at hs
  have hT : 0 < T := Finset.sum_pos (fun x _ => mul_pos (hν x) (hg x)) hne
  have hχ : chiSqDist ν π + 1 = T := by
    simp only [chiSqDist, sub_add_cancel, T]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [g]
    ring
  rw [hχ]
  have he : (∑ x, ν.prob x * ((3*T-g x)/(2*T*Real.sqrt T))) = 1/Real.sqrt T := by
    simp only [← mul_div_assoc, mul_sub]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, ν.sum_one, one_mul]
    change (3*T-T)/(2*T*Real.sqrt T) = _
    field_simp [ne_of_gt hT, ne_of_gt (Real.sqrt_pos.2 hT)]
    ring
  rw [← he]
  apply Finset.sum_le_sum
  intro x _
  have hs : 1/Real.sqrt (g x) = Real.sqrt (π.prob x / ν.prob x) := by
    have hi : π.prob x / ν.prob x = (g x)⁻¹ := by dsimp [g]; rw [inv_div]
    rw [hi, Real.sqrt_inv]
    simp only [one_div]
  rw [← hs]
  exact mul_le_mul_of_nonneg_left (inverse_sqrt_tangent (g x) T (hg x) hT) (ν.nonneg x)

end Qatlib.Concepts.EstimatorLaws.TvStability
