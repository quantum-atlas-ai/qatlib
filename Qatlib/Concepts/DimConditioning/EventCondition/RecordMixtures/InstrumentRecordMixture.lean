/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.RecordMixtures
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning

/-!
# Instrument record representatives and reconstruction

This module defines `representative` by using the conditional state at positive record
probability and a target operator otherwise. It proves density preservation of these
representatives and reconstructs every branch by multiplying by its probability.

`forget_error` transfers conditional trace distance bounds on good records to the output with
the record forgotten. The underlying instrument formalism is described in [Watrous2018].

## Main statements

* `reconstruction`: probability times representative recovers each branch.
* `forget_error`: good record error plus bad record mass bounds the forgotten output error.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture
open Matrix
open scoped ComplexOrder

variable {R : Type} [Fintype R] [DecidableEq R] {N D : ℕ}

/-- Use the record conditional state when its probability is positive and the supplied target
operator otherwise. -/
noncomputable def representative (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument R N D) (ρ : Qatlib.Foundations.PureStateMath.Operator N) (target : Qatlib.Foundations.PureStateMath.Operator D) (r : R) : Qatlib.Foundations.PureStateMath.Operator D :=
  if h : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ r then I.conditionalState ρ r h else target

omit [DecidableEq R] in

/-- For density input, multiplying a record representative by its probability recovers that
record branch output. -/
theorem reconstruction (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument R N D) (ρ : Qatlib.Foundations.PureStateMath.Operator N) (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ)
    (target : Qatlib.Foundations.PureStateMath.Operator D) (r : R) :
    ((Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ r : ℝ) : ℂ) • Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative I ρ target r=I.branch r ρ := by
  unfold Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative
  split_ifs with h
  · exact (Qatlib.Concepts.QuditTeleport.TeleportCore.Instrument.conditionalState_reconstruction I ρ r h).1
  · have hz : Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ r=0 := le_antisymm (not_lt.mp h) (Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg I hρ.1 r)
    rw [hz,Complex.ofReal_zero,zero_smul,(Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_eq_zero_iff I hρ.1 r).mp hz]

omit [DecidableEq R] in

/-- Every record representative is a density operator when both the input and fallback target
are density operators. -/
theorem representative_density (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument R N D) (ρ : Qatlib.Foundations.PureStateMath.Operator N) (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ)
    (target : Qatlib.Foundations.PureStateMath.Operator D) (ht : Qatlib.Foundations.PureStateMath.IsDensityOperator target) (r : R) :
    Qatlib.Foundations.PureStateMath.IsDensityOperator (Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative I ρ target r) := by
  unfold Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative
  split_ifs with h
  · exact I.isDensityOperator_conditionalState hρ r h
  · exact ht

/-- Good record conditional trace distance at most `η` and bad record probability at most `ζ`
imply forgotten output trace distance at most `η + ζ` from the target. -/
theorem forget_error (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument R N D) (ρ : Qatlib.Foundations.PureStateMath.Operator N) (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ)
    (target : Qatlib.Foundations.PureStateMath.Operator D) (ht : Qatlib.Foundations.PureStateMath.IsDensityOperator target) (good : Finset R) (η ζ : ℝ) (hη : 0 ≤ η)
    (hgood : ∀ r ∈ good, ∀ h : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ r,
      Matrix.traceNorm (I.conditionalState ρ r h-target)/2 ≤ η)
    (hbad : (∑ r : R, if r ∈ good then 0 else Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ r) ≤ ζ) :
    Matrix.traceNorm (I.forget.map ρ-target)/2 ≤ η+ζ := by
  have he : I.forget.map ρ=∑ r : R, ((Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ r : ℝ) : ℂ) • Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative I ρ target r := by
    rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.forget_apply]
    exact Finset.sum_congr rfl
        (fun r _ => (Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.reconstruction I ρ hρ target r).symm)
  rw [he]
  apply Qatlib.Concepts.MixedFidelity.FidelityMetric.RecordMixtureTraceError.bad_record_budget _ (fun r => Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg I hρ.1 r)
    (Qatlib.Concepts.AdaptiveCP.BranchTrace.sum_instrumentProb_isDensityOperator I hρ) _ (fun r => Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative_density I ρ hρ target ht r)
    target ht good η ζ hη _ hbad
  intro r hr
  unfold Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative
  split_ifs with hp
  · exact hgood r hr hp
  · simpa only [sub_self,Matrix.traceNorm_zero,zero_div] using hη

end Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture
