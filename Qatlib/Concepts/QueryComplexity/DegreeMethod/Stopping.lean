/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.StoppingDefs
import Qatlib.Concepts.MixedInstrument.ClockBridge.StoppingJoint
import Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference
import Qatlib.Concepts.StoppingCore.BranchCostCore.BranchCostExecution
import Qatlib.Concepts.FairRandomBits.GeometricRetry
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNative
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.MixedInstrument.ClockBridge

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped BigOperators Classical
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

variable {S O : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype O] [DecidableEq O] {X : Type} [Fintype X] {D E : ℕ}

theorem clause14_never_semantics (P : JointProgram S O X D E) (cfg : O ⊕ S) :
    jointNeverMass P cfg = nonterminationMass P.next cfg :=
  jointNeverMass_eq P cfg

omit [Fintype S] [DecidableEq S] [Nonempty S] in

theorem clause14_zero_cost_loop_violates_positive_cost (O : Type) (s : S) :
    ¬ PositiveReceiptCost (O := O) (zeroCostLoop (O := O) s) := by
  intro h
  have hne : (zeroCostLoop (O := O) s) s ((.inr s : O ⊕ S), 0) ≠ 0 := by
    simp [zeroCostLoop, PMF.pure_apply]
  have h1 := h s (.inr s : O ⊕ S) 0 hne
  omega

omit [Fintype S] [DecidableEq S] [Nonempty S] [Fintype O] [DecidableEq O] in

theorem clause14_zero_cost_loop_never_halts (n : ℕ) (s : S) :
    branchCostRun (zeroCostLoop (O := O) s) n ((.inr s : O ⊕ S))
      ((.inr s : O ⊕ S), 0) = 1 := by
  induction n with
  | zero => simp [branchCostRun, CostedLaw.ret, PMF.pure_apply]
  | succ n ih =>
    rw [branchCostRun_point (zeroCostLoop (O := O) s) n 0 s ((.inr s : O ⊕ S))]
    rw [tsum_eq_single (((.inr s : O ⊕ S)), 0)]
    · have h1 : (zeroCostLoop (O := O) s) s (((.inr s : O ⊕ S)), 0) = 1 := by
        simp [zeroCostLoop, PMF.pure_apply]
      rw [h1]
      simp only [Nat.sub_zero, one_mul]
      exact ih
    · intro b hb
      have hbne : b ≠ ((.inr s : O ⊕ S), 0) := hb
      have h2 : (zeroCostLoop (O := O) s) s b = 0 := by
        simp [zeroCostLoop, PMF.pure_apply_of_ne _ _ hbne]
      rw [h2, zero_mul]

theorem walkGoal_conditional_output_interface : ConditionalOutputInterface := by
  intro S O X _ _ _ _ _ _ _ D E
  refine ⟨?_, ?_, ?_⟩
  · intro P fuel cfg Ev
    exact jointEventMap_cp P fuel cfg Ev
  · intro P fuel cfg Ev _ ρ hρ
    exact jointEventMap_trace P fuel cfg Ev ρ hρ
  · intro P fuel cfg Ev _ ρ hρ hzero
    exact jointEventMap_zero_of_prob_zero P fuel cfg Ev ρ hρ hzero

theorem walkGoal_reference_event_consumer (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
    (Ev : O × X × ℕ → Prop) [DecidablePred Ev] {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : IsDensityOperator (jointMemoryMarginal D R ρ)) :
    Matrix.trace (jointReferenceEventMap P fuel cfg Ev ρ)
      = ((jointEventProb P (jointMemoryMarginal D R ρ) fuel cfg Ev : ℝ) : ℂ) :=
  jointReferenceEventMap_trace P fuel cfg Ev ρ hρ

theorem walkGoal_reference_stop_consumer (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
    (o : O) (x : X) (k : ℕ) {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : IsDensityOperator (jointMemoryMarginal D R ρ)) :
    Matrix.trace (tensorLeft (jointStopMap P fuel cfg o x k) ρ)
      = ((jointProb P (jointMemoryMarginal D R ρ) fuel cfg o x k : ℝ) : ℂ) :=
  jointReferenceStopMap_trace_prob P fuel cfg o x k R ρ hρ

theorem walkGoal_zero_mass_event_has_zero_branch (P : JointProgram S O X D E) (fuel : ℕ)
    (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (hzero : jointEventProb P ρ fuel cfg Ev = 0) :
    jointEventMap P fuel cfg Ev ρ = 0 :=
  jointEventMap_zero_of_prob_zero P fuel cfg Ev ρ hρ hzero

theorem clause16_effective_sampler_ledger : EffectiveSamplerLedger := by
  intro X _ _ D E k m I
  refine ⟨fairBitProgram_cost k m I, ?_⟩
  intro fuel cfg o c hc
  exact fairBit_joint_charge_bound k m I fuel cfg o c hc

theorem clause16_native_cycle_bit_cost (k : ℕ) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.cycleWord k).length = 2 * k := by
  exact Qatlib.Concepts.AdversaryBounds.AdvDuality.cycleWord_length k

theorem clause16_fair_bit_pending_is_geometric_tail (k m : ℕ) (hm : m ≤ 2 ^ k) (fuel : ℕ)
    (I : Instrument X D E) :
    jointPendingMass (fairBitProgram k m I) fuel (.inr ()) = coinRejectMass k m ^ fuel :=
  jointPendingMass_fairBit k m hm fuel I

end Qatlib.Concepts.QueryComplexity.DegreeMethod
