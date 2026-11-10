/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.InterleaveComparison
import Qatlib.Papers.QAOAScaling23.SearchFees.AngleSplit
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
variable {I:Type} [Fintype I] [DecidableEq I]

theorem geometric_schedule_positive (M T:ℕ) : ∀m∈geometricSearchSchedule M T,0<m := by
  intro m hm
  obtain ⟨i,hi⟩:=List.mem_ofFn.mp hm
  rw [← hi]
  exact geometric_window_pos M i.val

theorem original_resource_400 (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M T:ℕ) (θ:ℝ)
    (h0:0<θ) (h1:θ<Real.pi/2) (hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (hcap:1≤(M:ℝ)*Real.sin (2*θ)) (f:Fee) (hf:f≠.stages) :
    expected U hU seed S valid f (geometricSearchSchedule M T)≤ENNReal.ofReal (400/Real.sin (2*θ)) := by
  have hb:=geometric_search_intrinsic_expected_resource_budget U hU seed S valid M T θ hvalid h0 h1 hmass hcap
  have hs:0<Real.sin (2*θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h100:ENNReal.ofReal (100/Real.sin (2*θ))≤ENNReal.ofReal (400/Real.sin (2*θ)) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by norm_num : (100:ℝ)≤400) hs.le)
  have h300:ENNReal.ofReal (300/Real.sin (2*θ))≤ENNReal.ofReal (400/Real.sin (2*θ)) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by norm_num : (300:ℝ)≤400) hs.le)
  cases f with
  | phase=>exact hb.1.trans h100
  | bits=>exact hb.2.1.trans h300
  | validation=>exact hb.2.2.1.trans h100
  | prepare=>exact hb.2.2.2.1.trans h300
  | gates=>exact hb.2.2.2.2
  | stages=>exact (hf rfl).elim

theorem lowQ_interleaved_budget (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M T:ℕ) (θ:ℝ)
    (h0:0<θ) (h1:θ<Real.pi/2) (hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (hQ:(Real.sin θ)^2≤1/2) (hcap:1≤(M:ℝ)*Real.sin θ) (f:Fee) (hf:f≠.stages) :
    expected U hU seed S valid f (interleavePlain (geometricSearchSchedule M T))≤ENNReal.ofReal (1000/Real.sin θ) := by
  have hc:=lowQ_source_cap M θ h0 h1 hQ hcap
  have hs:0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hs2:0<Real.sin (2*θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hb:=geometric_search_intrinsic_expected_resource_budget U hU seed S valid M T θ hvalid h0 h1 hmass hc
  calc
    _ ≤ expected U hU seed S valid f (geometricSearchSchedule M T)+expected U hU seed S valid .stages (geometricSearchSchedule M T) :=
      interleave_expected_le_original U hU seed S valid f _
    _ ≤ ENNReal.ofReal (400/Real.sin (2*θ))+2*ENNReal.ofReal (300/Real.sin (2*θ)) :=
      add_le_add (original_resource_400 U hU seed S valid hvalid M T θ h0 h1 hmass hc f hf)
        ((stages_le_twice_prepare U hU seed S valid _ (geometric_schedule_positive M T)).trans
          (mul_le_mul_right hb.2.2.2.1 2))
    _ = ENNReal.ofReal (1000/Real.sin (2*θ)) := by
      rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal ((div_le_div_iff₀ hs2 hs).mpr (by
      have h:=lowQ_double_sine θ h0 h1 hQ
      nlinarith))
end Qatlib.Papers.QAOAScaling23.SearchFees
