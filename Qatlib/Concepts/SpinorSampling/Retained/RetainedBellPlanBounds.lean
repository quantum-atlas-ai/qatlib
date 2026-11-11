/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellPlanConfidence
import Qatlib.Concepts.SpinorSampling.Matching.CorrelationPlanBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Plan Bounds

Retained Bell Plan Bounds constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open Matched

-- Minimality, in addition to the previously proved square lower bound, is
-- needed to absorb the dense branch's M-sized integer-rounding payment.
/-- Complete original `ceil_sqrt_q_le_integer` guarantee for `RetainedBellPlanBounds`; all source hypotheses and output obligations are retained. -/
theorem ceil_sqrt_q_le_integer (q : ℚ) (M : ℕ) (hq : q≤(M : ℚ)^2) :
    ceilSqrtQ q≤M := by
  have hc : ceilNatQ q≤M^2 := by
    unfold ceilNatQ
    rw [ceil_int_eq,Int.toNat_le,Int.ceil_le]
    exact_mod_cast hq
  have hr : Nat.sqrt (ceilNatQ q)≤M := by
    have hs := (Nat.sqrt_le' (ceilNatQ q)).trans hc
    nlinarith
  dsimp only [ceilSqrtQ]
  split_ifs with h
  · have hlt : Nat.sqrt (ceilNatQ q)<M := by
      by_contra hnot
      have heq : Nat.sqrt (ceilNatQ q)=M := by omega
      rw [heq] at h
      exact (not_lt_of_ge hq) h
    omega
  · exact hr

/-- Complete original `bell_rejected_records_strength` guarantee for `RetainedBellPlanBounds`; all source hypotheses and output obligations are retained. -/
theorem bell_rejected_records_strength (M : ℕ) (hM : 0<M) (p ε δ : ℚ)
    (hreject : M<bellRecordsQ M p ε δ) : (M : ℚ)<bellStrengthQ p ε δ := by
  have hs : (M : ℚ)^2<(M : ℚ)*bellStrengthQ p ε δ := by
    by_contra h
    exact (not_le_of_gt hreject)
      (ceil_sqrt_q_le_integer _ M (le_of_not_gt h))
  have hm : (0 : ℚ)<M := by exact_mod_cast hM
  apply (mul_lt_mul_iff_right₀ hm).mp
  simpa only [pow_two] using hs

/-- Complete original `bell_sparse_copies_upper` guarantee for `RetainedBellPlanBounds`; all source hypotheses and output obligations are retained. -/
theorem bell_sparse_copies_upper (M : ℕ) (p ε δ : ℚ) (hp : 0≤p) (hε : 0<ε) :
    ((2*bellRecordsQ M p ε δ : ℕ) : ℝ)≤
      2*Real.sqrt ((M : ℝ)*(bellStrengthQ p ε δ : ℝ))+2 := by
  have hq : (0 : ℚ)≤(M : ℚ)*bellStrengthQ p ε δ := by
    unfold bellStrengthQ
    positivity
  have h := ceil_sqrt_q_upper _ hq
  have hR : (bellRecordsQ M p ε δ : ℝ)≤
      Real.sqrt ((M : ℝ)*(bellStrengthQ p ε δ : ℝ))+1 := by
    simpa only [bellRecordsQ,Rat.cast_mul,Rat.cast_natCast] using h
  push_cast
  linarith

/-- Complete original `bell_dense_copies_upper` guarantee for `RetainedBellPlanBounds`; all source hypotheses and output obligations are retained. -/
theorem bell_dense_copies_upper (M : ℕ) (hM : 0<M) (p ε δ : ℚ)
    (hp : 0≤p) (hε : 0<ε) (hreject : M<bellRecordsQ M p ε δ) :
    ((2*M*bellBlocksQ M p ε δ : ℕ) : ℝ)<4*(bellStrengthQ p ε δ : ℝ) := by
  have hq : (0 : ℚ)≤bellStrengthQ p ε δ/(M : ℚ) := by
    unfold bellStrengthQ
    positivity
  have hceil : (bellBlocksQ M p ε δ : ℝ)<
      (bellStrengthQ p ε δ : ℝ)/(M : ℝ)+1 := by
    simpa only [bellBlocksQ,Rat.cast_div,Rat.cast_natCast] using (ceil_nat_bounds _ hq).2
  have hMreal : (0 : ℝ)<M := by exact_mod_cast hM
  have hpaid : ((2*M*bellBlocksQ M p ε δ : ℕ) : ℝ)<
      2*(bellStrengthQ p ε δ : ℝ)+2*(M : ℝ) := by
    calc
      _ = (2*(M : ℝ))*(bellBlocksQ M p ε δ : ℝ) := by push_cast; ring
      _ < (2*(M : ℝ))*((bellStrengthQ p ε δ : ℝ)/(M : ℝ)+1) :=
        mul_lt_mul_of_pos_left hceil (by positivity)
      _ = _ := by field_simp
  have hsize : (M : ℝ)<(bellStrengthQ p ε δ : ℝ) := by
    exact_mod_cast bell_rejected_records_strength M hM p ε δ hreject
  linarith

-- An all-branch bound on the actual schedule. In particular, the dense
-- rounding term is absorbed; it is not left as a gratuitous O(M) cost.
/-- Complete original `bell_plan_copies_upper` guarantee for `RetainedBellPlanBounds`; all source hypotheses and output obligations are retained. -/
theorem bell_plan_copies_upper (side M : ℕ) (hM : 0<M) (p ε δ : ℚ)
    (hp : 0≤p) (hε : 0<ε) :
    ((bellPlanQ side M p ε δ).copies : ℝ)≤
      4*(bellStrengthQ p ε δ : ℝ)+
        2*Real.sqrt ((M : ℝ)*(bellStrengthQ p ε δ : ℝ))+2 := by
  have ha : (0 : ℝ)≤(bellStrengthQ p ε δ : ℝ) := by
    apply Rat.cast_nonneg.mpr
    unfold bellStrengthQ
    positivity
  have hs := Real.sqrt_nonneg ((M : ℝ)*(bellStrengthQ p ε δ : ℝ))
  by_cases hside : side≤2
  · simp only [bellPlanQ,ite_eq_left hside,Nat.cast_zero]
    positivity
  · by_cases hmid : p≤2*ε
    · simp only [bellPlanQ,ite_eq_right hside,ite_eq_left hmid,Nat.cast_zero]
      positivity
    · by_cases hn : bellRecordsQ M p ε δ≤M
      · have h := bell_sparse_copies_upper M p ε δ hp hε
        simp only [bellPlanQ,ite_eq_right hside,ite_eq_right hmid,ite_eq_left hn]
        linarith
      · have h := bell_dense_copies_upper M hM p ε δ hp hε (lt_of_not_ge hn)
        simp only [bellPlanQ,ite_eq_right hside,ite_eq_right hmid,ite_eq_right hn]
        linarith

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.ceil_sqrt_q_le_integer
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_rejected_records_strength
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_sparse_copies_upper
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_dense_copies_upper
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_plan_copies_upper
