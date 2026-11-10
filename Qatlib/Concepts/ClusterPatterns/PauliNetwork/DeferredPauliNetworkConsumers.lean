/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.PauliNetwork.DeferredPauliNetwork
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

theorem deferred_pauli_actual_path_ledger :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n))
      (hist : Fin gs.length → Bool × Bool), networkLegal gs →
      networkBranchValid gs hist →
      deferredPathCost gs hist (zeroPauliFrame n) =
        (0, 4 * (networkCounts gs).1 + 9 * (networkCounts gs).2 +
          frameCorrectionCost (finalPauliFrame gs hist (zeroPauliFrame n)),
         (networkCounts gs).1 + 2 * (networkCounts gs).2,
         (networkCounts gs).1 + 2 * (networkCounts gs).2) := by
  intro n gs hist hgs hh
  simp only [deferredPathCost, deferredRawPathCost_eq gs hist _ hgs hh,
    frameCorrectionSteps_length]

theorem deferred_pauli_corrected_history_entangled_reference :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hist : Fin gs.length → Bool × Bool),
      networkLegal gs → let F := finalPauliFrame gs hist (zeroPauliFrame n);
      let T := (conjBranch ((pauliFrameGate n F)ᴴ)).comp
        (deferredHistoryBranch gs hist (zeroPauliFrame n));
      ∀ (R : ℕ) (X : Matrix (Fin R × Fin (2 ^ n)) (Fin R × Fin (2 ^ n)) ℂ),
        ChannelAmplification T R X = if networkBranchValid gs hist then
          ((2 : ℂ)⁻¹)^((networkCounts gs).1 + 2 * (networkCounts gs).2) •
            (TensorGate (1 : Operator R) (networkLogicalMatrix gs)) * X *
              (TensorGate (1 : Operator R) (networkLogicalMatrix gs))ᴴ else 0 := by
  intro n gs hist hgs
  (try dsimp only)
  intro R X
  rw [deferredCorrectedBranch_eq gs hist hgs]
  by_cases hv : networkBranchValid gs hist
  · rw [if_pos hv, if_pos hv]
    have hs : ∀ (c : ℂ) (T : Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n)),
        ChannelAmplification (c • T) R X = c • ChannelAmplification T R X := fun _ _ => rfl
    rw [hs, channelAmplification_conjBranch]
    change ((2 : ℂ)⁻¹)^((networkCounts gs).1 + 2 * (networkCounts gs).2) •
      (TensorGate (1 : Operator R) (networkLogicalMatrix gs) * X *
        (TensorGate (1 : Operator R) (networkLogicalMatrix gs))ᴴ) = _
    rw [Matrix.smul_mul, Matrix.smul_mul]
  · rw [if_neg hv, if_neg hv]
    rfl

theorem deferredHistoryBranch_cp {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hgs : networkLegal gs) (hist : Fin gs.length → Bool × Bool) :
    CompletelyPositive (deferredHistoryBranch gs hist (zeroPauliFrame n)) := by
  have he : deferredHistoryBranch gs hist (zeroPauliFrame n) =
      if networkBranchValid gs hist then
        ((2 : ℂ)⁻¹)^((networkCounts gs).1 + 2 * (networkCounts gs).2) •
          conjBranch (pauliFrameGate n (finalPauliFrame gs hist (zeroPauliFrame n)) *
            networkLogicalMatrix gs) else 0 := by
    apply LinearMap.ext
    intro ρ
    by_cases hv : networkBranchValid gs hist <;>
      simp [hv, deferredHistoryBranch_zero_formula gs hist hgs ρ]
  rw [he]
  by_cases hv : networkBranchValid gs hist
  · rw [if_pos hv, networkHalf_pow_cast]
    exact networkCP_const_smul (completelyPositive_conjBranch _) (by positivity)
  · rw [if_neg hv]
    exact networkCP_zero

theorem deferred_pauli_physical_branches_and_forget_consumer :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)), networkLegal gs →
      (∀ hist : Fin gs.length → Bool × Bool,
        CompletelyPositive (deferredHistoryBranch gs hist (zeroPauliFrame n))) ∧
      (∀ ρ : Operator (2 ^ n),
        (∑ hist : Fin gs.length → Bool × Bool,
          conjBranch ((pauliFrameGate n (finalPauliFrame gs hist (zeroPauliFrame n)))ᴴ)
            (deferredHistoryBranch gs hist (zeroPauliFrame n) ρ)) =
          conjBranch (networkLogicalMatrix gs) ρ) := by
  intro n gs hgs
  refine ⟨deferredHistoryBranch_cp gs hgs, ?_⟩
  intro ρ
  have he : ∀ hist : Fin gs.length → Bool × Bool,
      conjBranch ((pauliFrameGate n (finalPauliFrame gs hist (zeroPauliFrame n)))ᴴ)
        (deferredHistoryBranch gs hist (zeroPauliFrame n) ρ) =
        (networkHistoryInstrument gs hgs).branch hist ρ := by
    intro hist
    change ((conjBranch ((pauliFrameGate n (finalPauliFrame gs hist (zeroPauliFrame n)))ᴴ)).comp
      (deferredHistoryBranch gs hist (zeroPauliFrame n))) ρ = _
    rw [deferredCorrectedBranch_eq gs hist hgs,
      cluster_network_history_actual_branch_formula n gs hgs hist ρ]
    by_cases hv : networkBranchValid gs hist <;> simp [hv]
  simp_rw [he]
  rw [← Instrument.forget_apply]
  exact (cluster_network_forget_correct_arbitrary_input n gs hgs).2 ρ

end Qatlib.Concepts.ClusterPatterns.PauliNetwork
