/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning

/-!
# Forgetting classical instrument records

`forgetRecord` coarsens outcomes indexed by a record and a Boolean flag to the flag alone.
Branch outputs and probabilities are obtained by summing over records, as in the instrument
formalism of [Watrous2018].

If every accepting branch of positive probability has the same conditional state, that state is
preserved when the record is forgotten, provided the total acceptance probability is positive.

## Main statements

* `branch`: the coarsened branch output is the sum over records.
* `probability`: outcome probabilities add under record erasure.
* `constant_conditional`: a common accepting conditional state survives record erasure.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument
open Matrix
open scoped ComplexOrder

variable {R : Type} [Fintype R] {D E : ℕ}

/-- Forgets the record component of an instrument outcome while retaining its Boolean flag. -/
noncomputable def forgetRecord (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (R × Bool) D E) : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument Bool D E :=
  J.coarsen Prod.snd

/-- Each branch after forgetting the record is the sum of the original branches with the same
Boolean flag. -/
theorem branch (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (R × Bool) D E) (ρ : Qatlib.Foundations.PureStateMath.Operator D) (b : Bool) :
    (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord J).branch b ρ=∑ r : R, J.branch (r,b) ρ := by
  classical
  simp [Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord,Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.coarsen,LinearMap.sum_apply,Finset.sum_filter,Fintype.sum_prod_type]

/-- The probability of a retained Boolean outcome is the sum of the probabilities over its
record values. -/
theorem probability (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (R × Bool) D E) (ρ : Qatlib.Foundations.PureStateMath.Operator D) (b : Bool) :
    Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord J) ρ b=∑ r : R, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J ρ (r,b) := by
  rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb,Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.branch,Matrix.trace_sum,Complex.re_sum]
  rfl

/-- For a positive semidefinite input, forgetting the record preserves a common conditional
state of all positive-probability accepting branches, provided acceptance has positive total
probability. -/
theorem constant_conditional (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (R × Bool) D E) (ρ : Qatlib.Foundations.PureStateMath.Operator D) (hρ : ρ.PosSemidef)
    (σ : Qatlib.Foundations.PureStateMath.Operator E)
    (hσ : ∀ r : R, ∀ h : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J ρ (r,true), J.conditionalState ρ (r,true) h=σ)
    (hs : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord J) ρ true) :
    (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord J).conditionalState ρ true hs=σ := by
  have hb (r : R) : J.branch (r,true) ρ=((Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J ρ (r,true) : ℝ) : ℂ) • σ := by
    by_cases hp : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J ρ (r,true)
    · rw [← (Qatlib.Concepts.QuditTeleport.TeleportCore.Instrument.conditionalState_reconstruction J ρ (r,true) hp).1,hσ r hp]
    · have hz : Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J ρ (r,true)=0 :=
        le_antisymm (le_of_not_gt hp) (Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg J hρ (r,true))
      rw [(Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_eq_zero_iff J hρ (r,true)).mp hz,hz]
      simp
  have he : (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord J).branch true ρ=
      ((Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord J) ρ true : ℝ) : ℂ) • σ := by
    rw [Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.branch]
    simp_rw [hb]
    rw [← Finset.sum_smul,← Complex.ofReal_sum,← Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.probability]
  have hn :
      ((Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord J) ρ true : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.conditionalState,he,smul_smul,inv_mul_cancel₀ hn,one_smul]

end Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument
