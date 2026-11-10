/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.RegisterMeasurementDefs
import Qatlib.Concepts.InstrumentCore.PovmBridge.MeasurementNetwork
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.InstrumentCore.PovmBridge

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open Matrix Qatlib.Concepts.InstrumentCore.PovmBridge
open scoped BigOperators ComplexOrder

theorem relabel_projector {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (S : Finset I) :
    relabelGate e (Projector S) = Projector (S.map e.toEmbedding) := by
  ext i j
  simp [relabelGate, Projector, Matrix.diagonal_apply, e.symm.injective.eq_iff,
    Finset.mem_map_equiv]

theorem relabel_projective_branch {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (S : Finset I) (o : Bool) (ψ : QState I) :
    ProjectiveBranch (Projector (S.map e.toEmbedding)) o (relabelState e ψ) =
      relabelState e (ProjectiveBranch (Projector S) o ψ) := by
  have he : (if o then Projector (S.map e.toEmbedding) else 1 - Projector (S.map e.toEmbedding)) =
      relabelGate e (if o then Projector S else 1 - Projector S) := by
    cases o
    · simp only [Bool.false_eq_true, if_false]
      rw [← relabel_projector e S]
      change 1 - Matrix.reindex e e (Projector S) = Matrix.reindex e e (1 - Projector S)
      ext i j
      simp [Matrix.reindex_apply, Matrix.one_apply, e.symm.injective.eq_iff]
    · simp only [if_true, relabel_projector]
  unfold ProjectiveBranch
  rw [he, applyGate_relabelGate]

theorem relabel_outerProduct {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (ψ : QState I) :
    relabelGate e (outerProduct ψ) = outerProduct (relabelState e ψ) := rfl

theorem measureProb_relabel_univ {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (ψ : QState I) :
    MeasureProb (relabelState e ψ) Finset.univ = MeasureProb ψ Finset.univ := by
  simpa only [Finset.map_univ_equiv] using measureProb_relabelState e ψ Finset.univ

theorem basis_event_pure_branch {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (S : Finset (Fin D))
    (ψ : QState (Fin D)) (o : Bool) :
    (basisEventInstrument U hU S).branch o (outerProduct ψ) =
      outerProduct (ProjectiveBranch (Projector S) o (ApplyGate U ψ)) := by
  change (Instrument.ofPOVM (eventPOVM S)).branch o (conjBranch U (outerProduct ψ)) = _
  rw [conjBranch_outerProduct, povm_projective_pure_branch (eventPOVM S) (U *ᵥ ψ) o
    (binaryProjectivePOVM_projection (eventProjector S) (projector_mul_self S) o)]
  cases o <;> rfl

theorem basis_event_mixed_branch {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (S : Finset (Fin D))
    (ρ : Operator D) (o : Bool) :
    (basisEventInstrument U hU S).branch o ρ =
      (if o then Projector S else 1 - Projector S) * (U * ρ * Uᴴ) *
        (if o then Projector S else 1 - Projector S)ᴴ := by
  change (Instrument.ofPOVM (eventPOVM S)).branch o (conjBranch U ρ) = _
  have hp : ((eventPOVM S).mats o).mat * ((eventPOVM S).mats o).mat =
      ((eventPOVM S).mats o).mat :=
    binaryProjectivePOVM_projection (eventProjector S) (projector_mul_self S) o
  rw [Instrument.ofPOVM_branch, hermitian_projection_half _ hp]
  have he : ((eventPOVM S).mats o).mat =
      (if o then Projector S else 1 - Projector S) := by cases o <;> rfl
  rw [he, conjBranch_apply]
  cases o <;> simp only [Bool.false_eq_true, if_false, if_true,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, projector_conjTranspose]

theorem encoded_event_pure_branch {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) (ψ : QState I) (o : Bool) :
    (encodedEventInstrument e U hU S).branch o (relabelGate e (outerProduct ψ)) =
      relabelGate e (outerProduct (ProjectiveBranch (Projector S) o (ApplyGate U ψ))) := by
  rw [relabel_outerProduct, encodedEventInstrument, basis_event_pure_branch,
    applyGate_relabelGate, relabel_projective_branch, ← relabel_outerProduct]

theorem encoded_event_mass {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) (ψ : QState I) (o : Bool) :
    instrumentProb (encodedEventInstrument e U hU S) (relabelGate e (outerProduct ψ)) o =
      ProjectiveBranchMass (Projector S) o (ApplyGate U ψ) := by
  unfold instrumentProb
  rw [encoded_event_pure_branch, relabel_outerProduct, trace_outerProduct]
  change MeasureProb (relabelState e _) Finset.univ = _
  exact measureProb_relabel_univ e _

theorem encoded_event_conditional {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) (ψ : QState I) (o : Bool)
    (hp : 0 < instrumentProb (encodedEventInstrument e U hU S)
      (relabelGate e (outerProduct ψ)) o) :
    ∃ φ, ProjectiveConditionalState (Projector S) o (ApplyGate U ψ) = some φ ∧
      (encodedEventInstrument e U hU S).conditionalState
        (relabelGate e (outerProduct ψ)) o hp = relabelGate e (outerProduct φ) := by
  have hm := encoded_event_mass e U hU S ψ o
  have hpos : 0 < MeasureProb (ProjectiveBranch (Projector S) o (ApplyGate U ψ))
      Finset.univ := by simpa only [hm, ProjectiveBranchMass] using hp
  refine ⟨PostMeasure (ProjectiveBranch (Projector S) o (ApplyGate U ψ)) Finset.univ, ?_, ?_⟩
  · exact if_pos hpos
  · rw [Instrument.conditionalState, encoded_event_pure_branch,
      outerProduct_postMeasure_univ _ hpos, hm]
    rfl

theorem encoded_event_zero {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) (ψ : QState I) (o : Bool)
    (hz : ProjectiveBranchMass (Projector S) o (ApplyGate U ψ) = 0) :
    ProjectiveConditionalState (Projector S) o (ApplyGate U ψ) = none ∧
      (encodedEventInstrument e U hU S).branch o (relabelGate e (outerProduct ψ)) = 0 := by
  constructor
  · unfold ProjectiveConditionalState ConditionalState
    apply if_neg
    change ¬ 0 < ProjectiveBranchMass (Projector S) o (ApplyGate U ψ)
    rw [hz]
    exact lt_irrefl 0
  · apply (instrumentProb_eq_zero_iff _ ?_ o).mp
    · rwa [encoded_event_mass]
    · rw [relabel_outerProduct]
      exact outerProduct_posSemidef _

theorem relabel_density {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef ∧ Matrix.trace ρ = 1) :
    IsDensityOperator (relabelGate e ρ) := by
  refine ⟨hρ.1.submatrix e.symm, ?_⟩
  change Matrix.trace (ρ.submatrix e.symm e.symm) = 1
  rw [Matrix.trace_submatrix, hρ.2]

theorem relabel_event_effect {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (S : Finset I) (o : Bool) :
    (if o then Projector (S.map e.toEmbedding) else 1 - Projector (S.map e.toEmbedding)) =
      relabelGate e (if o then Projector S else 1 - Projector S) := by
  cases o
  · simp only [Bool.false_eq_true, if_false]
    rw [← relabel_projector e S]
    ext i j
    simp [relabelGate, Matrix.one_apply, e.symm.injective.eq_iff]
  · simp only [if_true, relabel_projector]

theorem relabel_adjoint {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) :
    (relabelGate e A)ᴴ = relabelGate e Aᴴ := rfl

theorem encoded_event_mixed_branch {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) (ρ : Matrix I I ℂ) (o : Bool) :
    (encodedEventInstrument e U hU S).branch o (relabelGate e ρ) =
      relabelGate e ((if o then Projector S else 1 - Projector S) * (U * ρ * Uᴴ) *
        (if o then Projector S else 1 - Projector S)ᴴ) := by
  rw [encodedEventInstrument, basis_event_mixed_branch, relabel_event_effect,
    relabel_adjoint, relabel_adjoint]
  simp only [← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul]

theorem encoded_event_born {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (e : I ≃ Fin D) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (S : Finset I) (ψ : QState I) :
    instrumentProb (encodedEventInstrument e U hU S) (relabelGate e (outerProduct ψ)) true =
      MeasureProb (ApplyGate U ψ) S := by
  rw [encoded_event_mass]
  exact sum_normSq_collapse (ApplyGate U ψ) S

theorem qudit_decoded_row (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (o : Fin n × Fin n) (k : Fin n) :
    quditDecodedState n ψ ((quditRegisterEquiv n) (o,k)) =
      (quditBranchKraus n o *ᵥ ψ) k := rfl

theorem qudit_collapsed_row (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (o a : Fin n × Fin n) (k : Fin n) :
    Collapse (quditDecodedState n ψ) (quditOutcomeEvent n o)
      ((quditRegisterEquiv n) (a,k)) =
        if a = o then (quditBranchKraus n o *ᵥ ψ) k else 0 := by
  by_cases ha : a = o
  · subst a
    simp [collapse_apply, quditOutcomeEvent, qudit_decoded_row]
  · simp [collapse_apply, quditOutcomeEvent, ha]

theorem qudit_coarse_branch (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (o : Fin n × Fin n) :
    (quditCoarseInstrument n o).branch true (outerProduct (quditDecodedState n ψ)) =
      outerProduct (Collapse (quditDecodedState n ψ) (quditOutcomeEvent n o)) := by
  rw [quditCoarseInstrument, basis_event_pure_branch]
  simp only [ProjectiveBranch, if_true, ApplyGate, Matrix.one_mulVec]
  rfl

theorem qudit_coarse_bob (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (o : Fin n × Fin n) :
    Matrix.traceLeft (Matrix.reindex (quditRegisterEquiv n).symm (quditRegisterEquiv n).symm
      ((quditCoarseInstrument n o).branch true (outerProduct (quditDecodedState n ψ)))) =
        outerProduct (quditBranchKraus n o *ᵥ ψ) := by
  rw [qudit_coarse_branch]
  ext k l
  change (∑ a : Fin n × Fin n,
    Collapse (quditDecodedState n ψ) (quditOutcomeEvent n o) ((quditRegisterEquiv n) (a,k)) *
      (starRingEnd ℂ) (Collapse (quditDecodedState n ψ) (quditOutcomeEvent n o)
        ((quditRegisterEquiv n) (a,l)))) = _
  simp [qudit_collapsed_row, outerProduct_apply]

theorem qudit_coarse_mass (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (o : Fin n × Fin n) :
    instrumentProb (quditCoarseInstrument n o) (outerProduct (quditDecodedState n ψ)) true =
      MeasureProb (quditBranchKraus n o *ᵥ ψ) Finset.univ := by
  have ht := congrArg (fun A => (Matrix.trace A).re) (qudit_coarse_bob n ψ o)
  (try dsimp only at ht)
  rw [Matrix.traceLeft_trace, Matrix.reindex_apply, Matrix.trace_submatrix,
      trace_outerProduct] at ht
  exact ht

theorem qudit_corrected_vector (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (o : Fin n × Fin n) :
    quditCorrection n o *ᵥ (quditBranchKraus n o *ᵥ ψ) = (1 / (n : ℂ)) • ψ := by
  rw [Matrix.mulVec_mulVec, quditCorrection_cancel, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem qudit_kraus_mass (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (hψ : Normalized ψ) (o : Fin n × Fin n) :
    MeasureProb (quditBranchKraus n o *ᵥ ψ) Finset.univ = 1 / (n : ℝ)^2 := by
  have hm : MeasureProb ((quditX n ((ZMod.finEquiv n) o.2) *
      quditZ n (-((ZMod.finEquiv n) o.1))) *ᵥ ψ) Finset.univ = 1 :=
    measureProb_univ (normalized_applyGate (mul_mem (quditX_unitary n _)
      (quditZ_unitary n _)) hψ)
  rw [quditBranchKraus_formula, Matrix.smul_mulVec, measureProb_smul, hm, mul_one]
  simp

theorem qudit_decoded_normalized (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (hψ : Normalized ψ) : Normalized (quditDecodedState n ψ) := by
  unfold Normalized
  calc
    _ = ∑ r : QuditTriple n, ‖quditDecodedState n ψ ((quditRegisterEquiv n) r)‖^2 :=
      ((quditRegisterEquiv n).sum_comp _).symm
    _ = ∑ o : Fin n × Fin n, MeasureProb (quditBranchKraus n o *ᵥ ψ) Finset.univ := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ _o : Fin n × Fin n, 1 / (n : ℝ)^2 :=
      Finset.sum_congr rfl (fun o _ => qudit_kraus_mass n ψ hψ o)
    _ = 1 := by
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
      simp [Fintype.card_prod, Fintype.card_fin]
      field_simp

theorem qudit_coarse_conditional_corrected (n : ℕ) [NeZero n] (ψ : QState (Fin n))
    (hψ : Normalized ψ) (o : Fin n × Fin n)
    (hp : 0 < instrumentProb (quditCoarseInstrument n o) (outerProduct (quditDecodedState n ψ)) true) :
    quditCorrection n o *
      Matrix.traceLeft (Matrix.reindex (quditRegisterEquiv n).symm (quditRegisterEquiv n).symm
        ((quditCoarseInstrument n o).conditionalState
          (outerProduct (quditDecodedState n ψ)) true hp)) *
      (quditCorrection n o)ᴴ = outerProduct ψ := by
  have hm : instrumentProb (quditCoarseInstrument n o) (outerProduct (quditDecodedState n ψ)) true =
      1 / (n : ℝ)^2 := by rw [qudit_coarse_mass, qudit_kraus_mass n ψ hψ o]
  have hs (c : ℂ) (A : Operator (n*n*n)) :
      Matrix.reindex (quditRegisterEquiv n).symm (quditRegisterEquiv n).symm (c • A) =
        c • Matrix.reindex (quditRegisterEquiv n).symm (quditRegisterEquiv n).symm A := rfl
  rw [Instrument.conditionalState, hs, Matrix.traceLeft_smul,
    qudit_coarse_bob, Matrix.mul_smul, Matrix.smul_mul,
    conjugate_outerProduct, qudit_corrected_vector, hm]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, outerProduct_apply, Pi.smul_apply,
    map_mul, map_div₀, map_one, Complex.conj_natCast, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]
  field_simp

end Qatlib.Concepts.TensorRegisters.RegisterModel
