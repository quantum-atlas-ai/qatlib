/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DimConditioning.EventCondition.RecordMixtures.AcceptedRecordWeights
import Qatlib.Concepts.DimConditioning.EventCondition.RecordMixtures.InstrumentRecordMixture
import Qatlib.Concepts.DimConditioning.EventCondition.RecordMixtures.RecordForgottenInstrument
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordMixture
open Matrix Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture
open Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument
open scoped ComplexOrder

variable {R : Type} [Fintype R] [DecidableEq R] {N D : ℕ}

omit [DecidableEq R] in

theorem conditional_mixture (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (R × Bool) N D) (ρ : Qatlib.Foundations.PureStateMath.Operator N)
    (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ) (target : Qatlib.Foundations.PureStateMath.Operator D)
    (hs : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I) ρ true) :
    (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I).conditionalState ρ true hs=
      ∑ r : R, (((Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,true)/(∑ a : R, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (a,true))) : ℝ) : ℂ) •
        Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative I ρ target (r,true) := by
  rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.conditionalState,Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.probability,Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.branch]
  simp_rw [← Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.reconstruction I ρ hρ target]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [smul_smul,Complex.ofReal_div,div_eq_mul_inv,mul_comm]

theorem conditional_error (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (R × Bool) N D) (ρ : Qatlib.Foundations.PureStateMath.Operator N)
    (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ) (target : Qatlib.Foundations.PureStateMath.Operator D) (ht : Qatlib.Foundations.PureStateMath.IsDensityOperator target)
    (good : Finset R) (η : ℝ) (hη : 0 ≤ η)
    (hgood : ∀ r ∈ good, ∀ hp : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,true),
      Matrix.traceNorm (I.conditionalState ρ (r,true) hp-target)/2 ≤ η)
    (hs : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I) ρ true) :
    Matrix.traceNorm ((Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I).conditionalState ρ true hs-target)/2 ≤
      η+(∑ r : R, if r ∈ good then 0 else Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,true)/(∑ a : R, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (a,true))) := by
  have hS : 0 < ∑ a : R, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (a,true) := by
    simpa only [Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.probability] using hs
  rw [Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordMixture.conditional_mixture I ρ hρ target hs]
  apply Qatlib.Concepts.MixedFidelity.FidelityMetric.RecordMixtureTraceError.bad_record_budget _
    (fun r => div_nonneg (Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg I hρ.1 (r,true)) hS.le) _ _
    (fun r => Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative_density I ρ hρ target ht (r,true)) target ht good η _ hη _ le_rfl
  · rw [← Finset.sum_div,div_self hS.ne']
  · intro r hr
    unfold Qatlib.Concepts.DimConditioning.EventCondition.InstrumentRecordMixture.representative
    split_ifs with hp
    · exact hgood r hr hp
    · simpa only [sub_self,Matrix.traceNorm_zero,zero_div] using hη

theorem output_bound (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (R × Bool) N D) (ρ : Qatlib.Foundations.PureStateMath.Operator N)
    (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ) (target : Qatlib.Foundations.PureStateMath.Operator D) (ht : Qatlib.Foundations.PureStateMath.IsDensityOperator target)
    (good : Finset R) (η ζ δ : ℝ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ) (hsmall : ζ+δ < 1)
    (hgood : ∀ r ∈ good, ∀ hp : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,true),
      Matrix.traceNorm (I.conditionalState ρ (r,true) hp-target)/2 ≤ η)
    (hbad : (∑ r : R, if r ∈ good then 0 else Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,true)+Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,false)) ≤ ζ)
    (hfail : ∀ r ∈ good, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,false) ≤
      δ*(Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,true)+Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I ρ (r,false))) :
    ∃ hs : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I) ρ true,
      1-ζ-δ ≤ Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I) ρ true ∧
        Matrix.traceNorm ((Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I).conditionalState ρ true hs-target)/2 ≤ η+ζ/(1-ζ-δ) := by
  have hq := fun z => Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg I hρ.1 z
  have hsum := Qatlib.Concepts.AdaptiveCP.BranchTrace.sum_instrumentProb_isDensityOperator I hρ
  obtain ⟨hS,_,hpost⟩ :=
      Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordWeights.posterior_budget _ hq hsum good ζ δ hζ hδ hsmall hbad hfail
  have hs :
      0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb
      (Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.forgetRecord I) ρ true := by simpa only [Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.probability] using hS
  refine ⟨hs,?_,(Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordMixture.conditional_error I ρ hρ target ht good η hη hgood hs).trans (add_le_add le_rfl hpost)⟩
  simpa only [Qatlib.Concepts.DimConditioning.EventCondition.RecordForgottenInstrument.probability] using
    (Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordWeights.acceptance _ hq hsum good ζ δ hδ hbad hfail).1

end Qatlib.Concepts.DimConditioning.EventCondition.AcceptedRecordMixture
