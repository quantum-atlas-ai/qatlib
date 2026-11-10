/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ResourceCompile.ClusterStabilizerResourceStat
import Qatlib.Concepts.ClusterPatterns.ClusterCompile.IsingClusterPulseCompilationQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClusterPatterns.ClusterCompile

namespace Qatlib.Concepts.ClusterPatterns.ResourceCompile
open Qatlib

private theorem czResource_apply {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Reg n) :
    czResource edges x = czPhase edges x * Uniform (Reg n) x := by
  exact Matrix.mulVec_diagonal _ _ _

private theorem frameMatrix_apply {n : ℕ} (edges : Finset (Fin n × Fin n))
    (ψ : QState (Reg n)) (x : Reg n) :
    ApplyGate (frameMatrix edges) ψ x = framePhase edges x * ψ x := by
  exact Matrix.mulVec_diagonal _ _ _

theorem czResource_stabilizer {n : ℕ} (edges : Finset (Fin n × Fin n))
    (horder : ∀ e ∈ edges, e.1 < e.2) (v : Fin n) :
    ApplyGate (stabilizer edges v) (czResource edges) = czResource edges := by
  funext x
  rw [apply_stabilizer, neighborPhase_flip edges horder, czResource_apply,
    czResource_apply, czPhase_flip edges horder]
  change neighborPhase edges v x * (neighborPhase edges v x * czPhase edges x *
    Uniform (Reg n) x) = _
  rw [← mul_assoc, ← mul_assoc, neighborPhase_sq, one_mul]

theorem clusterStabilizerResource : ClusterStabilizerResource := by
  classical
  intro n edges horder
  obtain ⟨htransport, hsourceUnitary, _, _, _, _⟩ :=
    isingClusterPulseCompilation n edges horder
  have hstate : sourceResource edges = ApplyGate (frameMatrix edges) (czResource edges) := by
    rw [sourceResource, htransport, applyGate_mul]
    rfl
  have hsource (x : Reg n) : sourceResource edges x =
      framePhase edges x * czPhase edges x * Uniform (Reg n) x := by
    rw [hstate, frameMatrix_apply, czResource_apply, ← mul_assoc]
  have hnormalized : Normalized (Uniform (Reg n)) := normalized_uniform Fintype.card_pos
  refine ⟨normalized_applyGate hsourceUnitary hnormalized, ?_, ?_,
    normalized_applyGate (czMatrix_unitary edges) hnormalized,
    czResource_stabilizer edges horder⟩
  · intro v
    funext x
    rw [apply_stabilizer, neighborPhase_flip edges horder, hsource,
      framePhase_flip, czPhase_flip edges horder]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsource]
    change neighborPhase edges v x *
      ((bitPhase (incomingOdd edges v) * framePhase edges x) *
        (neighborPhase edges v x * czPhase edges x) * Uniform (Reg n) x) =
      bitPhase (incomingOdd edges v) *
        (framePhase edges x * czPhase edges x * Uniform (Reg n) x)
    calc
      _ = (neighborPhase edges v x * neighborPhase edges v x) *
          (bitPhase (incomingOdd edges v) *
            (framePhase edges x * czPhase edges x * Uniform (Reg n) x)) := by ring
      _ = _ := by rw [neighborPhase_sq, one_mul]
  · rw [run_frameWord]
    funext x
    rw [frameMatrix_apply, hsource, czResource_apply]
    rw [← mul_assoc, ← mul_assoc, framePhase_sq, one_mul]

end Qatlib.Concepts.ClusterPatterns.ResourceCompile
