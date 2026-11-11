/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.HighConfidenceVelocity

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# High Confidence Plan

High Confidence Plan constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched

/-- Data and invariants for High Confidence Plan Q in the high confidence plan model. -/
structure HighConfidencePlanQ where
  current : CorrelationPlanQ
  crossRecords : ℕ
  norm : TargetNormPlanQ
  spin : Option CorrelationPlanQ
  copies : ℕ
  targetQueries : ℕ
  deriving Repr

-- Coefficients are the finite rational coefficients already produced by the
/-- existing parameter entry. No state-dependent value is read by this plan. -/
def highConfidencePlanQ (d M : ℕ) (rootM α β U γ η δ : ℚ) : HighConfidencePlanQ :=
  let ε := η/(8*(d : ℚ))
  let ρ := δ/(4*(d : ℚ))
  let current := correlationPlanQ M rootM (ε/α^2) ρ
  let cross := linearCountQ (2*α*β*U) ε ρ
  let norm := targetNormPlanQ M (β*U) ε ρ
  let spin := if γ=0 then none else
    some (correlationPlanQ M rootM (η/(24*(d : ℚ)*γ)) (δ/(12*(d : ℚ))))
  { current := current
    crossRecords := cross
    norm := norm
    spin := spin
    copies := d*(current.copies+cross)+(match spin with | none => 0 | some p => 3*d*p.copies)
    targetQueries := d*min cross M+d*norm.queries }

-- None contains no spin records. The harmless zero plan only gives that
/-- empty data a uniform type; it is not executed as an extra sampling stage. -/
def HighConfidencePlanQ.spinSchedule (p : HighConfidencePlanQ) : CorrelationPlanQ :=
  p.spin.getD ⟨.zero,0,0,0,1,1/2⟩

/-- Construction for grid High Confidence Plan Q in the high confidence plan model. -/
def gridHighConfidencePlanQ (d r : ℕ) (α β U γ η δ : ℚ) : HighConfidencePlanQ :=
  highConfidencePlanQ d (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ) α β U γ η δ

noncomputable section

/-- Complete original `high_plan_current_fields` guarantee for `HighConfidencePlan`; all source hypotheses and output obligations are retained. -/
theorem high_plan_current_fields (d M : ℕ) (rootM α β U γ η δ : ℚ) :
    (highConfidencePlanQ d M rootM α β U γ η δ).current=
      correlationPlanQ M rootM ((η/(8*(d : ℚ)))/α^2) (δ/(4*(d : ℚ))) ∧
    (highConfidencePlanQ d M rootM α β U γ η δ).crossRecords=
      linearCountQ (2*α*β*U) (η/(8*(d : ℚ))) (δ/(4*(d : ℚ))) ∧
    (highConfidencePlanQ d M rootM α β U γ η δ).norm=
      targetNormPlanQ M (β*U) (η/(8*(d : ℚ))) (δ/(4*(d : ℚ))) := by
  exact ⟨rfl,rfl,rfl⟩

/-- Complete original `high_plan_spin_fields` guarantee for `HighConfidencePlan`; all source hypotheses and output obligations are retained. -/
theorem high_plan_spin_fields (d M : ℕ) (rootM α β U γ η δ : ℚ) (hγ : γ≠0) :
    (highConfidencePlanQ d M rootM α β U γ η δ).spinSchedule=
      correlationPlanQ M rootM (η/(24*(d : ℚ)*γ)) (δ/(12*(d : ℚ))) := by
  simp only [highConfidencePlanQ,ite_eq_right hγ,HighConfidencePlanQ.spinSchedule,Option.getD_some]

/-- Complete original `high_plan_zero_spin` guarantee for `HighConfidencePlan`; all source hypotheses and output obligations are retained. -/
theorem high_plan_zero_spin (d M : ℕ) (rootM α β U η δ : ℚ) :
    (highConfidencePlanQ d M rootM α β U 0 η δ).spin=none ∧
    (highConfidencePlanQ d M rootM α β U 0 η δ).spinSchedule.mode=.zero ∧
    (highConfidencePlanQ d M rootM α β U 0 η δ).spinSchedule.records=0 ∧
    (highConfidencePlanQ d M rootM α β U 0 η δ).spinSchedule.blocks=0 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Complete original `high_plan_accounts` guarantee for `HighConfidencePlan`; all source hypotheses and output obligations are retained. -/
theorem high_plan_accounts (d M : ℕ) (rootM α β U γ η δ : ℚ) :
    let p := highConfidencePlanQ d M rootM α β U γ η δ
    p.copies=d*(p.current.copies+p.crossRecords)+3*d*p.spinSchedule.copies ∧
    p.targetQueries=d*min p.crossRecords M+d*p.norm.queries := by
  dsimp only [highConfidencePlanQ]
  split_ifs <;> simp [HighConfidencePlanQ.spinSchedule]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_plan_current_fields
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_plan_spin_fields
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_plan_zero_spin
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_plan_accounts
