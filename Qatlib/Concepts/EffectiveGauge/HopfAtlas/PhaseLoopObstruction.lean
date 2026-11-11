/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PathSpace
import Mathlib.Topology.Order.IntermediateValue

/-!
# Phase Loop Obstruction

Hopf Atlas constructions for Effective Gauge.
Proves `phase_eq_implies_period_integer`, `no_closed_phase_lift`.
-/


set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `phase_eq_implies_period_integer` guarantee for the `PhaseLoopObstruction` construction; the complete source hypotheses are retained. -/
theorem phase_eq_implies_period_integer (a b : ℝ) (h : phase a=phase b) :
    ∃ n : ℤ, a-b=(n : ℝ)*physicalPeriod := by
  have hc : Real.cos a=Real.cos b := by
    simpa [phase,iAxis] using congrArg QuaternionAlgebra.re h
  have hs : Real.sin a=Real.sin b := by
    simpa [phase,iAxis] using congrArg QuaternionAlgebra.imI h
  have hh : Real.cos (a-b)=1 := by
    rw [Real.cos_sub,hc,hs]
    nlinarith [Real.sin_sq_add_cos_sq b]
  obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff (a-b)).mp hh
  exact ⟨n,by simpa only [physicalPeriod] using hn.symm⟩

/-- A continuous real lift of one full phase loop cannot have equal
 endpoint values. This is the circle obstruction, not a differentiability claim. -/
theorem no_closed_phase_lift (f : ℝ → ℝ) (hf : Continuous f)
    (hp : ∀ t, phase (f t)=phase t) (he : f physicalPeriod=f 0) : False := by
  let d := fun t : ℝ => (f t-t)/physicalPeriod
  have hd : Continuous d := (hf.sub continuous_id).div_const physicalPeriod
  have hi (t : ℝ) : ∃ n : ℤ, d t=(n : ℝ) := by
    obtain ⟨n,hn⟩ := phase_eq_implies_period_integer (f t) t (hp t)
    refine ⟨n,?_⟩
    dsimp only [d]
    rw [hn]
    field_simp [physicalPeriod_pos.ne']
  obtain ⟨n,hn⟩ := hi 0
  have hend : d physicalPeriod=d 0-1 := by
    change (f physicalPeriod-physicalPeriod)/physicalPeriod=(f 0-0)/physicalPeriod-1
    rw [he,sub_zero,sub_div,div_self physicalPeriod_pos.ne']
  have htarget : (n : ℝ)-1/2∈Icc (d physicalPeriod) (d 0) := by
    rw [hend,hn]
    constructor <;> linarith
  obtain ⟨t,_,ht⟩ := intermediate_value_Icc' physicalPeriod_pos.le hd.continuousOn htarget
  obtain ⟨m,hm⟩ := hi t
  have hr : (2 : ℝ)*(m : ℝ)=2*(n : ℝ)-1 := by linarith
  have hz : (2 : ℤ)*m=2*n-1 := by exact_mod_cast hr
  omega

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
