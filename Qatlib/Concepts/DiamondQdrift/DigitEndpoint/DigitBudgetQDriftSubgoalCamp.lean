/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.DigitEndpoint.DigitBudgetQDriftSubgoalStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.EffectiveInput
open Qatlib.Concepts.RandCompile.FairBitSampling

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint
open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

theorem digitBudgetQDriftSubgoal : DigitBudgetQDriftSubgoal := by
  intro L D a K t ε j0 q sgn hK hε hε1 hor hp r W terms
  have hG1 := digitBudgetQDriftData_spec L a t ε q sgn hε hε1 hor hp
  have hG2 : ∀ ref : ℕ, ∀ X : Matrix (Fin D × Fin ref) (Fin D × Fin ref) ℂ,
      Matrix.traceNorm (
        tensorLeft (fairQdriftActualMap r.weights j0 r.steps r.fuel terms r.baseTime) X -
        tensorLeft (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)) X)
      ≤ (ε : ℝ) * Matrix.traceNorm X :=
    digitBudgetQDrift_reference_error L D a K t ε j0 q sgn hK hε hε1 hor hp
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hdiamond := finiteDiamondDistance_le_of_uniform
    (fairQdriftActualMap r.weights j0 r.steps r.fuel terms r.baseTime)
    (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t))
    (ε : ℝ) hεR.le hG2
  have hdiamond' : finiteDiamondDistance
      (fairQdriftActualMap r.weights j0 r.steps r.fuel terms r.baseTime)
      (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)) ≤
      ENNReal.ofReal (ε : ℝ) :=
    hdiamond.trans (ENNReal.ofReal_le_ofReal (by linarith))
  refine ⟨hG1.1, hG1.2.1, hG1.2.2.2.2.2, hdiamond', ?_⟩
  intro ω
  by_cases hW : W = 0
  · have hW' : weightTotal r.weights = 0 := hW
    have hcir : fairQdriftCircuit r.weights j0 r.steps r.fuel terms r.baseTime ω = [] := by
      rw [fairQdriftCircuit, if_pos hW']
    have hzero := fairQdrift_zero_protocol r.weights j0 r.steps r.fuel terms r.baseTime ω
      0 (0 : Matrix (Fin D × Fin 0) (Fin D × Fin 0) ℂ) hW'
    refine ⟨by rw [hcir]; exact isUnitaryCircuit_nil, by rw [hcir]; rfl,
      by rw [hcir, if_pos hW]; rfl, ?_, ?_⟩
    · rw [hW]
      simpa using hzero.2.1
    · rw [hzero.2.2.1]
      exact Nat.zero_le _
  · have hKterms : ∀ j, (terms j).IsHermitian :=
      fun j => (dyadicSignedTerms_contract r.precision r.table K hK j).1
    have hWpos : 0 < weightTotal r.weights :=
      Nat.pos_of_ne_zero (fun h => hW h)
    have hcounts := fair_bit_qdrift_actual_quantum_and_classical_path_counts L D
      r.steps r.fuel r.weights j0 terms r.baseTime ω hWpos hKterms
    exact ⟨hcounts.1, hcounts.2.1, by rw [if_neg hW]; exact hcounts.2.2.1,
      hcounts.2.2.2.1, hcounts.2.2.2.2⟩

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
