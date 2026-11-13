/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveInteractionGateRateStat

/-!
# Summed gate costs for dyadic interaction times

This module bounds nonnegative dyadic interaction times and their sum, then proves
`effectiveInteractionGateRate`. A per-time cost hypothesis yields a total bound with at most
twice the full-duration leading cost and one additive unit per dyadic time. This accounting
supports the interaction picture simulation framework of [LowWiebe2018].

## Main statements

* `effectiveInteractionGateRate`: sum the dyadic gate-cost bounds.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.InteractionEvo.EffCosts
open scoped BigOperators

/-- A dyadic interaction time is nonnegative when the rational base duration is nonnegative. -/
private theorem dyadicTime_nonneg (tau : ℚ) (nd j : ℕ) (ht : 0 ≤ tau) :
    0 ≤ (effectiveIPDyadicTime tau nd j : ℝ) := by
  unfold effectiveIPDyadicTime
  split_ifs <;> push_cast <;> positivity

/-- For `j ≤ nd` and nonnegative `tau`, the dyadic interaction time is at most `tau`. -/
private theorem dyadicTime_le (tau : ℚ) (nd j : ℕ) (ht : 0 ≤ tau) (hj : j ≤ nd) :
    (effectiveIPDyadicTime tau nd j : ℝ) ≤ (tau : ℝ) := by
  unfold effectiveIPDyadicTime
  split_ifs with h
  · exact le_rfl
  · push_cast
    have hp : (2 : ℝ)^j ≤ 2^nd := pow_le_pow_right₀ (by norm_num) hj
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^nd)).mpr
    exact mul_le_mul_of_nonneg_left hp (by exact_mod_cast ht)

/-- The sum of dyadic interaction times indexed by zero through `nd` is at most twice the
nonnegative base duration. -/
private theorem dyadicTime_sum (tau : ℚ) (nd : ℕ) (ht : 0 ≤ tau) :
    (∑ j ∈ Finset.range (nd+1), (effectiveIPDyadicTime tau nd j : ℝ)) ≤ 2*(tau : ℝ) := by
  have hsum : ∑ j ∈ Finset.range nd, (2 : ℝ)^j = 2^nd-1 := by
    induction nd with
    | zero => simp
    | succ nd ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [Finset.sum_range_succ]
  have he (j : ℕ) (hj : j ∈ Finset.range nd) :
      (effectiveIPDyadicTime tau nd j : ℝ) = (tau : ℝ)*2^j/2^nd := by
    simp [effectiveIPDyadicTime, Nat.ne_of_lt (Finset.mem_range.mp hj)]
  rw [Finset.sum_congr rfl he]
  simp only [effectiveIPDyadicTime, ite_true]
  rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
  have hp : (0 : ℝ) < 2^nd := by positivity
  have heq : (tau : ℝ)*(2^nd-1)/2^nd+(tau : ℝ) = 2*(tau : ℝ)-(tau : ℝ)/2^nd := by
    field_simp
    ring
  rw [heq]
  have := div_nonneg (show (0 : ℝ) ≤ tau by exact_mod_cast ht) hp.le
  linarith

/-- The per-time gate-cost hypothesis implies the aggregate bound with leading term `2 CA tau (1
+ log(1 + tau / delta))^gamma` and additive term `nd + 1`. This is a cost summation used in
the setting of [LowWiebe2018]. -/
theorem effectiveInteractionGateRate : EffectiveInteractionGateRate := by
  intro gamma hg tau delta nd CA cost ht hd hCA hc
  push_cast at hc
  let B : ℝ := (1+Real.log (1+(tau : ℝ)/(delta : ℝ)))^gamma
  have htr : (0 : ℝ) ≤ tau := by exact_mod_cast ht
  have hdr : (0 : ℝ) < delta := by exact_mod_cast hd
  have hB : 0 ≤ B := by
    apply Real.rpow_nonneg
    have := Real.log_nonneg (show 1 ≤ 1+(tau : ℝ)/(delta : ℝ) by linarith [div_nonneg htr hdr.le])
    linarith
  have hterm (j : ℕ) (hj : j ∈ Finset.range (nd+1)) :
      (cost j : ℝ) ≤ CA*(effectiveIPDyadicTime tau nd j : ℝ)*B+1 := by
    have hjn : j ≤ nd := by have := Finset.mem_range.mp hj; omega
    have hnn := dyadicTime_nonneg tau nd j ht
    have hle := dyadicTime_le tau nd j ht hjn
    have hlog : Real.log (1+abs (effectiveIPDyadicTime tau nd j : ℝ)/(delta : ℝ)) ≤
        Real.log (1+(tau : ℝ)/(delta : ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg hnn]
      gcongr
    have hbase : 0 ≤ 1+Real.log (1+abs (effectiveIPDyadicTime tau nd j : ℝ)/(delta : ℝ)) := by
      have :=
          Real.log_nonneg
          (show 1 ≤ 1+abs (effectiveIPDyadicTime tau nd j : ℝ)/(delta : ℝ) by linarith [div_nonneg (abs_nonneg (effectiveIPDyadicTime tau nd j : ℝ)) hdr.le])
      linarith
    have hp :=
        Real.rpow_le_rpow hbase
        (by linarith : 1+Real.log (1+abs (effectiveIPDyadicTime tau nd j : ℝ)/(delta : ℝ)) ≤ 1+Real.log (1+(tau : ℝ)/(delta : ℝ))) hg.le
    have hh := hc j hjn
    simp only [abs_of_nonneg hnn] at hh hp
    apply hh.trans
    simpa only [B, add_comm] using!
      add_le_add_right (mul_le_mul_of_nonneg_left hp (mul_nonneg hCA hnn)) 1
  have hs := Finset.sum_le_sum hterm
  calc
    _ ≤ ∑ j ∈ Finset.range (nd+1), (CA*(effectiveIPDyadicTime tau nd j : ℝ)*B+1) := hs
    _ = CA*(∑ j ∈ Finset.range (nd+1), (effectiveIPDyadicTime tau nd j : ℝ))*B+(nd+1) := by
      simp [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ CA*(2*(tau : ℝ))*B+(nd+1) := by gcongr; exact dyadicTime_sum tau nd ht
    _ = _ := by dsimp [B]; ring

end Qatlib.Concepts.InteractionEvo.EffCosts
