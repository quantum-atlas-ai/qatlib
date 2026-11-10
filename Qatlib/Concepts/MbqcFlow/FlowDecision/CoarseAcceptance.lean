/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentSeq.SeqAssoc.InstrumentCoarseGrainLaws
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder

def coarseAcceptLabel (i : Fin 3) : Bool := if i = 2 then true else false

noncomputable def coarseAcceptanceInstrument : Instrument Bool 3 3 :=
  (projectiveInstrument : Instrument (Fin 3) 3 3).coarsen coarseAcceptLabel

noncomputable def coarseAcceptanceInput : Operator 3 :=
  Matrix.diagonal (fun _ => (1 / 3 : ℂ))

theorem coarseAcceptanceInput_posSemidef : coarseAcceptanceInput.PosSemidef := by
  unfold coarseAcceptanceInput
  refine Matrix.PosSemidef.diagonal ?_
  intro i
  show (0 : ℂ) ≤ (1 / 3 : ℂ)
  rw [RCLike.nonneg_iff]
  norm_num

theorem coarseAcceptanceInput_density : IsDensityOperator coarseAcceptanceInput := by
  refine ⟨coarseAcceptanceInput_posSemidef, ?_⟩
  unfold coarseAcceptanceInput
  rw [Matrix.trace_diagonal]
  norm_num [Fin.sum_univ_three]

theorem not_isPureDensityOperator_coarseAcceptanceInput :
    ¬ IsPureDensityOperator coarseAcceptanceInput := by
  rintro ⟨-, hsq⟩
  have h00 := congrFun (congrFun hsq (0 : Fin 3)) (0 : Fin 3)
  simp only [coarseAcceptanceInput, Matrix.diagonal_mul, Matrix.diagonal_apply] at h00
  norm_num at h00

theorem coarseAccept_fiber_false :
    (Finset.univ.filter fun i : Fin 3 => coarseAcceptLabel i = false) = {0, 1} := by
  ext i
  fin_cases i <;> simp [coarseAcceptLabel]

theorem coarseAccept_fiber_true :
    (Finset.univ.filter fun i : Fin 3 => coarseAcceptLabel i = true) = {2} := by
  ext i
  fin_cases i <;> simp [coarseAcceptLabel]

theorem instrumentProb_coarseAcceptance_false :
    instrumentProb coarseAcceptanceInstrument coarseAcceptanceInput false = 2 / 3 := by
  rw [coarseAcceptanceInstrument, instrumentProb_coarsen, coarseAccept_fiber_false]
  simp_rw [instrumentProb_projective]
  rw [coarseAcceptanceInput]
  norm_num [Matrix.diagonal_apply, Finset.sum_insert, Finset.sum_singleton]

theorem instrumentProb_coarseAcceptance_true :
    instrumentProb coarseAcceptanceInstrument coarseAcceptanceInput true = 1 / 3 := by
  rw [coarseAcceptanceInstrument, instrumentProb_coarsen, coarseAccept_fiber_true]
  simp_rw [instrumentProb_projective]
  rw [coarseAcceptanceInput]
  norm_num [Matrix.diagonal_apply, Finset.sum_insert, Finset.sum_singleton]

theorem coarseAcceptanceInstrument_branch_false :
    coarseAcceptanceInstrument.branch false coarseAcceptanceInput
      = Matrix.diagonal (fun j : Fin 3 => if j = 2 then 0 else (1 / 3 : ℂ)) := by
  rw [coarseAcceptanceInstrument]
  simp only [Instrument.coarsen]
  rw [coarseAccept_fiber_false]
  ext j j'
  simp only [LinearMap.sum_apply, projectiveInstrument, conjBranch_projector_apply,
    coarseAcceptanceInput, Matrix.diagonal_apply]
  fin_cases j <;> fin_cases j' <;> simp [Finset.sum_insert, Finset.sum_singleton]

theorem coarseAcceptanceInstrument_branch_true :
    coarseAcceptanceInstrument.branch true coarseAcceptanceInput
      = Matrix.diagonal (fun j : Fin 3 => if j = 2 then (1 / 3 : ℂ) else 0) := by
  rw [coarseAcceptanceInstrument]
  simp only [Instrument.coarsen]
  rw [coarseAccept_fiber_true]
  ext j j'
  simp only [LinearMap.sum_apply, projectiveInstrument, conjBranch_projector_apply,
    coarseAcceptanceInput, Matrix.diagonal_apply]
  fin_cases j <;> fin_cases j' <;> simp

theorem instrumentProb_coarseAcceptance_conditional_zero (h : 0 <
    instrumentProb coarseAcceptanceInstrument coarseAcceptanceInput false) :
    instrumentProb projectiveInstrument
      (coarseAcceptanceInstrument.conditionalState coarseAcceptanceInput false h) 0
      = 1 / 2 := by
  have hd0 : (coarseAcceptanceInstrument.conditionalState coarseAcceptanceInput false h) 0 0
      = (1 / 2 : ℂ) := by
    rw [Instrument.conditionalState, instrumentProb_coarseAcceptance_false,
      coarseAcceptanceInstrument_branch_false, Matrix.smul_apply,
      Matrix.diagonal_apply_eq]
    simp
    norm_num
  rw [instrumentProb_projective, hd0]
  norm_num

theorem coarseAcceptance_correct :
    IsDensityOperator coarseAcceptanceInput ∧
    ¬ IsPureDensityOperator coarseAcceptanceInput ∧
    instrumentProb coarseAcceptanceInstrument coarseAcceptanceInput false = 2 / 3 ∧
    instrumentProb coarseAcceptanceInstrument coarseAcceptanceInput true = 1 / 3 ∧
    (∀ h : 0 < instrumentProb coarseAcceptanceInstrument coarseAcceptanceInput false,
      coarseAcceptanceInstrument.conditionalState coarseAcceptanceInput false h =
        Matrix.diagonal (fun i : Fin 3 => if i = 2 then 0 else (1 / 2 : ℂ))) ∧
    instrumentProb (coarseAcceptanceInstrument.seq projectiveInstrument)
      coarseAcceptanceInput (false, (0 : Fin 3)) = 1 / 3 ∧
    (coarseAcceptanceInstrument.coarsen (fun _ => (0 : Fin 3))).branch 0
      coarseAcceptanceInput =
        coarseAcceptanceInstrument.forget.map coarseAcceptanceInput ∧
    (coarseAcceptanceInstrument.coarsen (fun _ => (0 : Fin 3))).branch 1
      coarseAcceptanceInput = 0 := by
  refine ⟨coarseAcceptanceInput_density,
    not_isPureDensityOperator_coarseAcceptanceInput,
    instrumentProb_coarseAcceptance_false, instrumentProb_coarseAcceptance_true,
    ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Instrument.conditionalState, instrumentProb_coarseAcceptance_false,
      coarseAcceptanceInstrument_branch_false]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> split_ifs <;>
      simp only [smul_eq_mul] <;> norm_num
  · have hpos : 0 < instrumentProb coarseAcceptanceInstrument coarseAcceptanceInput
        false := by
      rw [instrumentProb_coarseAcceptance_false]
      norm_num
    rw [instrumentProb_seq_conditional coarseAcceptanceInstrument projectiveInstrument
      coarseAcceptanceInput coarseAcceptanceInput_posSemidef false (0 : Fin 3) hpos,
      instrumentProb_coarseAcceptance_false,
      instrumentProb_coarseAcceptance_conditional_zero hpos]
    norm_num
  · rw [coarseAcceptanceInstrument, Instrument.forget_coarsen_apply,
      Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.forget_apply,
      (Qatlib.Concepts.InstrumentSeq.SeqAssoc.Instrument.coarsen_composition_laws projectiveInstrument coarseAcceptLabel
        (fun _ => (0 : Fin 3)) (0 : Fin 3) coarseAcceptanceInput).1]
    simp [Instrument.coarsen]
  · rw [coarseAcceptanceInstrument,
      (Qatlib.Concepts.InstrumentSeq.SeqAssoc.Instrument.coarsen_composition_laws projectiveInstrument coarseAcceptLabel
        (fun _ => (0 : Fin 3)) (1 : Fin 3) coarseAcceptanceInput).1]
    simp [Instrument.coarsen]

end Qatlib.Concepts.MbqcFlow.FlowDecision
