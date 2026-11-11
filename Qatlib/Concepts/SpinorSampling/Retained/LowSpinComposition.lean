/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinPlan
import Qatlib.Concepts.SpinorSampling.Retained.LowSpinLossBridge

set_option backward.isDefEq.respectTransparency false

/-!
# Low Spin Composition

Low Spin Composition constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators
open Matched

/-- Construction for bell Velocity Loss in the low spin composition model. -/
def bellVelocityLoss {d : ℕ} (A γ : ℝ) (v b : Fin d → ℝ) : ℝ :=
  (∑ j : Fin d,intervalClip 0 (A^2) (v j))+
    intervalClip 0 (2*(d : ℝ)*γ) (4*γ*(∑ j : Fin d,b j))

-- Deterministic error propagation for the actual two clipped terms.
-- The statistical endpoint must derive these component events from the
-- literal schedules; they are not extra certificates given to the algorithm.
/-- Complete original `bell_velocity_loss_error` guarantee for `LowSpinComposition`; all source hypotheses and output obligations are retained. -/
theorem bell_velocity_loss_error {d : ℕ} (A γ εv εb : ℝ)
    (v V b μ : Fin d → ℝ) (hγ : 0≤γ)
    (hV : ∀ j,0≤V j ∧ V j≤A^2)
    (hR : 0≤4*γ*(∑ j : Fin d,μ j) ∧ 4*γ*(∑ j : Fin d,μ j)≤2*(d : ℝ)*γ)
    (hv : ∀ j, |v j-V j|≤εv) (hb : ∀ j, |b j-μ j|≤εb) :
    |bellVelocityLoss A γ v b-((∑ j : Fin d,V j)+4*γ*(∑ j : Fin d,μ j))|≤
      (d : ℝ)*εv+4*γ*(d : ℝ)*εb := by
  have hvs : |(∑ j : Fin d,intervalClip 0 (A^2) (v j))-(∑ j : Fin d,V j)|≤
      (d : ℝ)*εv := by
    simpa only [Fintype.card_fin] using finite_sum_error_bound _ V εv
      (fun j => (interval_clip_contract 0 (A^2) (v j) (V j) (hV j).1 (hV j).2).trans (hv j))
  have hbs : |(∑ j : Fin d,b j)-(∑ j : Fin d,μ j)|≤(d : ℝ)*εb := by
    simpa only [Fintype.card_fin] using finite_sum_error_bound b μ εb hb
  have hscale : |4*γ*(∑ j : Fin d,b j)-4*γ*(∑ j : Fin d,μ j)|≤
      4*γ*(d : ℝ)*εb := by
    calc
      _ = 4*γ*|(∑ j : Fin d,b j)-(∑ j : Fin d,μ j)| := by
        rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤4*γ)]
      _ ≤ 4*γ*((d : ℝ)*εb) := mul_le_mul_of_nonneg_left hbs (by positivity)
      _ = _ := by ring
  have hspin := (interval_clip_contract 0 (2*(d : ℝ)*γ)
    (4*γ*(∑ j : Fin d,b j)) (4*γ*(∑ j : Fin d,μ j)) hR.1 hR.2).trans hscale
  have heq : bellVelocityLoss A γ v b-((∑ j : Fin d,V j)+4*γ*(∑ j : Fin d,μ j))=
      ((∑ j : Fin d,intervalClip 0 (A^2) (v j))-(∑ j : Fin d,V j))+
        (intervalClip 0 (2*(d : ℝ)*γ) (4*γ*(∑ j : Fin d,b j))-
          4*γ*(∑ j : Fin d,μ j)) := by unfold bellVelocityLoss; ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hvs hspin)

variable {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}

/-- Complete original `low_spin_velocity_value_cast` guarantee for `LowSpinComposition`; all source hypotheses and output obligations are retained. -/
theorem low_spin_velocity_value_cast (p : HighConfidencePlanQ) (u : Fin d → S → ℚ)
    (α β U : ℚ) (z : Fin d → VelocityData S p.current p.crossRecords p.norm) :
    (lowSpinVelocityValueQ p u α β U z : ℝ)=
      ∑ j : Fin d,intervalClip 0 (((α : ℝ)+(β : ℝ)*(U : ℝ))^2)
        (velocityRawOutputQ p.current p.crossRecords p.norm (Fintype.card S) (u j) α β (z j) : ℝ) := by
  simp only [lowSpinVelocityValueQ,Rat.cast_sum,interval_clip_cast,Rat.cast_zero,
    Rat.cast_pow,Rat.cast_add,Rat.cast_mul]

omit [Fintype S] in
/-- Complete original `low_spin_bell_value_cast_some` guarantee for `LowSpinComposition`; all source hypotheses and output obligations are retained. -/
theorem low_spin_bell_value_cast_some (e : Fin d → Equiv.Perm S) (q : BellPlanQ) (γ : ℚ)
    (ω : LowSpinBellData S d e (some q)) :
    (lowSpinBellValueQ e γ (some q) ω : ℝ)=
      intervalClip 0 (2*(d : ℝ)*(γ : ℝ))
        (4*(γ : ℝ)*(∑ j : Fin d,((executePlannedBellQ q (e j) (ω j)).value : ℝ))) := by
  simp only [lowSpinBellValueQ,interval_clip_cast,Rat.cast_zero,Rat.cast_mul,
    Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_sum]

/-- Complete original `low_spin_output_cast_some` guarantee for `LowSpinComposition`; all source hypotheses and output obligations are retained. -/
theorem low_spin_output_cast_some (pV : HighConfidencePlanQ) (q : BellPlanQ)
    (copies targetQueries : ℕ) (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S)
    (α β U γ : ℚ) (z : LowSpinData S d e ⟨pV,some q,copies,targetQueries⟩) :
    (lowSpinOutputQ ⟨pV,some q,copies,targetQueries⟩ u e α β U γ z : ℝ)=
      bellVelocityLoss ((α : ℝ)+(β : ℝ)*(U : ℝ)) (γ : ℝ)
        (fun j => (velocityRawOutputQ pV.current pV.crossRecords pV.norm
          (Fintype.card S) (u j) α β (z.1 j) : ℝ))
        (fun j => ((executePlannedBellQ q (e j) (z.2 j)).value : ℝ)) := by
  simp only [lowSpinOutputQ,Rat.cast_add,low_spin_velocity_value_cast,
    low_spin_bell_value_cast_some,bellVelocityLoss]

/-- Complete original `low_spin_output_cast_none` guarantee for `LowSpinComposition`; all source hypotheses and output obligations are retained. -/
theorem low_spin_output_cast_none (pV : HighConfidencePlanQ) (copies targetQueries : ℕ)
    (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S) (α β U γ : ℚ)
    (z : LowSpinData S d e ⟨pV,none,copies,targetQueries⟩) :
    (lowSpinOutputQ ⟨pV,none,copies,targetQueries⟩ u e α β U γ z : ℝ)=
      ∑ j : Fin d,intervalClip 0 (((α : ℝ)+(β : ℝ)*(U : ℝ))^2)
        (velocityRawOutputQ pV.current pV.crossRecords pV.norm (Fintype.card S) (u j) α β (z.1 j) : ℝ) := by
  simp only [lowSpinOutputQ,lowSpinBellValueQ,add_zero,low_spin_velocity_value_cast]

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_velocity_loss_error
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_velocity_value_cast
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_bell_value_cast_some
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_output_cast_some
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_output_cast_none
