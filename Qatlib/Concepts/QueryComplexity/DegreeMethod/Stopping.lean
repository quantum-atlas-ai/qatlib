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

/-!
# Stopping interfaces and fair-bit costs

This module connects joint instrument programs to nontermination mass, conditional event
outputs, and reference-register probabilities. It also verifies an effective sampler ledger and
the geometric pending-mass formula for a fair-bit retry program.

The zero-cost loop gives a concrete failure of positive receipt costs and remains pending with
probability one at every finite fuel. The event-map statements use the quantum-instrument
framework of [DaviesLewis1970].

## Main statements

* `clause14_never_semantics`: joint never-halting mass agrees with transition-kernel
  nontermination mass.
* `walkGoal_conditional_output_interface`: event maps satisfy complete positivity and the
  required probability and zero-output laws.
* `clause16_effective_sampler_ledger`: the fair-bit sampler satisfies its cost ledger.
* `clause16_fair_bit_pending_is_geometric_tail`: pending mass is a power of the rejection mass.

## References

* [Davies and Lewis, 1970][DaviesLewis1970]
-/

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

/-- The never-halting mass of a joint program equals the nontermination mass of its underlying
transition kernel. -/
theorem clause14_never_semantics (P : JointProgram S O X D E) (cfg : O ⊕ S) :
    jointNeverMass P cfg = nonterminationMass P.next cfg :=
  jointNeverMass_eq P cfg

omit [Fintype S] [DecidableEq S] [Nonempty S] in

/-- A deterministic loop with zero receipt cost fails the positive-receipt-cost condition. -/
theorem clause14_zero_cost_loop_violates_positive_cost (O : Type) (s : S) :
    ¬ PositiveReceiptCost (O := O) (zeroCostLoop (O := O) s) := by
  intro h
  have hne : (zeroCostLoop (O := O) s) s ((.inr s : O ⊕ S), 0) ≠ 0 := by
    simp [zeroCostLoop, PMF.pure_apply]
  have h1 := h s (.inr s : O ⊕ S) 0 hne
  omega

omit [Fintype S] [DecidableEq S] [Nonempty S] [Fintype O] [DecidableEq O] in

/-- At every finite fuel value, the zero-cost loop has probability one of remaining at its
initial state with zero accumulated cost. -/
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

/-- Establishes the conditional-output interface: event maps are completely positive, have the
prescribed trace probabilities, and vanish on zero-probability density inputs. -/
theorem walkGoal_conditional_output_interface : ConditionalOutputInterface := by
  intro S O X _ _ _ _ _ _ _ D E
  refine ⟨?_, ?_, ?_⟩
  · intro P fuel cfg Ev
    exact jointEventMap_cp P fuel cfg Ev
  · intro P fuel cfg Ev _ ρ hρ
    exact jointEventMap_trace P fuel cfg Ev ρ hρ
  · intro P fuel cfg Ev _ ρ hρ hzero
    exact jointEventMap_zero_of_prob_zero P fuel cfg Ev ρ hρ hzero

/-- The trace of a reference-extended event map equals the event probability computed from the
memory marginal, when that marginal is a density operator. -/
theorem walkGoal_reference_event_consumer (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
    (Ev : O × X × ℕ → Prop) [DecidablePred Ev] {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : IsDensityOperator (jointMemoryMarginal D R ρ)) :
    Matrix.trace (jointReferenceEventMap P fuel cfg Ev ρ)
      = ((jointEventProb P (jointMemoryMarginal D R ρ) fuel cfg Ev : ℝ) : ℂ) :=
  jointReferenceEventMap_trace P fuel cfg Ev ρ hρ

/-- The trace of a reference-extended stop map equals the probability of the specified output,
outcome, and cost on the memory marginal. -/
theorem walkGoal_reference_stop_consumer (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
    (o : O) (x : X) (k : ℕ) {R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : IsDensityOperator (jointMemoryMarginal D R ρ)) :
    Matrix.trace (tensorLeft (jointStopMap P fuel cfg o x k) ρ)
      = ((jointProb P (jointMemoryMarginal D R ρ) fuel cfg o x k : ℝ) : ℂ) :=
  jointReferenceStopMap_trace_prob P fuel cfg o x k R ρ hρ

/-- An event with zero probability on a density operator has zero output under the corresponding
joint event map. -/
theorem walkGoal_zero_mass_event_has_zero_branch (P : JointProgram S O X D E) (fuel : ℕ)
    (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (hzero : jointEventProb P ρ fuel cfg Ev = 0) :
    jointEventMap P fuel cfg Ev ρ = 0 :=
  jointEventMap_zero_of_prob_zero P fuel cfg Ev ρ hρ hzero

/-- Establishes the cost and supported-receipt bounds required by the effective sampler ledger. -/
theorem clause16_effective_sampler_ledger : EffectiveSamplerLedger := by
  intro X _ _ D E k m I
  refine ⟨fairBitProgram_cost k m I, ?_⟩
  intro fuel cfg o c hc
  exact fairBit_joint_charge_bound k m I fuel cfg o c hc

/-- The native cycle word for `k` random bits has length `2 * k`. -/
theorem clause16_native_cycle_bit_cost (k : ℕ) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.cycleWord k).length = 2 * k := by
  exact Qatlib.Concepts.AdversaryBounds.AdvDuality.cycleWord_length k

/-- When `m ≤ 2 ^ k`, the pending mass after the given fuel is the one-cycle rejection mass
raised to that fuel. -/
theorem clause16_fair_bit_pending_is_geometric_tail (k m : ℕ) (hm : m ≤ 2 ^ k) (fuel : ℕ)
    (I : Instrument X D E) :
    jointPendingMass (fairBitProgram k m I) fuel (.inr ()) = coinRejectMass k m ^ fuel :=
  jointPendingMass_fairBit k m hm fuel I

end Qatlib.Concepts.QueryComplexity.DegreeMethod
