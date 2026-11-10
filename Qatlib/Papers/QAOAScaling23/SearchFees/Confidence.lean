/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.Failure
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
namespace Qatlib.Papers.QAOAScaling23.SearchFees

theorem geometric_growth_lower (n:ℕ) : 1+(n:ℝ)/5≤(6/5:ℝ)^n := by
  induction n with
  | zero=>norm_num
  | succ n ih=>
    rw [pow_succ']
    have hn:(0:ℝ)≤n:=Nat.cast_nonneg n
    calc
      _ ≤ (6/5:ℝ)*(1+(n:ℝ)/5) := by push_cast;nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left ih (by norm_num)

theorem geometric_at_cap (M:ℕ) (hM:0<M) : geometricWindow M (5*M)=M := by
  have hm:(0:ℝ)<M:=by exact_mod_cast hM
  have hm1:(1:ℝ)≤M:=by exact_mod_cast hM
  have hg:(M:ℝ)≤(6/5:ℝ)^(5*M) := by
    have h:=geometric_growth_lower (5*M)
    push_cast at h
    linarith
  have hcap:1≤(M:ℝ)*(1/(M:ℝ)) := by rw [mul_one_div,div_self hm.ne']
  have hpow:1≤(6/5:ℝ)^(5*M)*(1/(M:ℝ)) := hcap.trans (mul_le_mul_of_nonneg_right hg (by positivity))
  have hwin:=geometric_window_mature (by positivity : (0:ℝ)<1/(M:ℝ))
    ((div_le_one hm).mpr hm1) M (5*M) hcap hpow
  have hlo:(M:ℝ)≤geometricWindow M (5*M) := by
    have h:1≤(geometricWindow M (5*M):ℝ)/(M:ℝ) := by simpa only [div_eq_mul_inv,one_mul] using hwin
    exact (one_le_div hm).mp h
  have hhi:geometricWindow M (5*M)≤M := by
    unfold geometricWindow
    exact max_le (by omega) (min_le_left _ _)
  exact le_antisymm hhi (by exact_mod_cast hlo)
variable {I:Type} [Fintype I] [DecidableEq I]

theorem lowQ_source_confidence (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M L:ℕ) (θ:ℝ)
    (h0:0<θ) (h1:θ<Real.pi/2) (hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (hQ:(Real.sin θ)^2≤1/2) (hcap:1≤(M:ℝ)*Real.sin θ) :
    (failure U hU seed S valid (interleavePlain (geometricSearchSchedule M (5*M+L)))).toReal≤(25/32:ℝ)^L := by
  have hM:0<M := by
    by_contra h
    have he:M=0:=by omega
    subst M
    norm_num at hcap
  have hwin:1≤(geometricWindow M (5*M):ℝ)*Real.sin (2*θ) := by
    rw [geometric_at_cap M hM]
    exact lowQ_source_cap M θ h0 h1 hQ hcap
  simpa only [Nat.add_sub_cancel_left] using
      lowQ_failure_cutoff U hU seed S valid hvalid M (5*M+L) (5*M) θ h0 h1 hmass hwin

theorem source_confidence (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M L:ℕ) (θ:ℝ)
    (h0:0<θ) (h1:θ<Real.pi/2) (hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (hcap:1≤(M:ℝ)*Real.sin θ) :
    (failure U hU seed S valid (interleavePlain (geometricSearchSchedule M (5*M+L)))).toReal≤(25/32:ℝ)^L := by
  by_cases hQ:(Real.sin θ)^2≤1/2
  · exact lowQ_source_confidence U hU seed S valid hvalid M L θ h0 h1 hmass hQ hcap
  · have hh:(1/2:ℝ)≤MeasureProb (preparedAAState U seed) S := by rw [hmass];linarith
    have h:=highQ_failure U hU seed S valid hvalid hh M (5*M+L)
    have hr:=ENNReal.toReal_mono (by finiteness : ((1/2:ℝ≥0∞)^(5*M+L))≠⊤) h
    simp only [ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] at hr
    refine hr.trans ?_
    have hpow:(1/2:ℝ)^(5*M+L)≤(1/2:ℝ)^L := by
      rw [pow_add]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)).trans_eq (one_mul _)
    exact hpow.trans (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤25/32) L)
end Qatlib.Papers.QAOAScaling23.SearchFees
