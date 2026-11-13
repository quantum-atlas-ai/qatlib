/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ResourceCompile.ClusterStabilizerResourceStat
import Qatlib.Concepts.ClusterPatterns.ClusterCompile.IsingClusterPulseCompilationQuan

/-!
# Stabilizer properties of cluster resources

This module proves normalization and stabilizer properties for ordered finite graph resources.
It shows that the frame word carries `sourceResource` to `czResource`, whose graph stabilizers
fix it, while the source resource has the specified incoming-edge parity signs.

The result `clusterStabilizerResource` packages these resource-state properties for the
measurement-based construction of [RaussendorfBriegel2000].

## Main statements

* `czResource_stabilizer`: each graph stabilizer fixes the CZ resource.
* `clusterStabilizerResource`: normalization, source eigenvalues, and frame-word transport.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClusterPatterns.ClusterCompile

namespace Qatlib.Concepts.ClusterPatterns.ResourceCompile
open Qatlib

/-- Each amplitude of the CZ resource is the uniform amplitude multiplied by its graph CZ phase. -/
private theorem czResource_apply {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Reg n) :
    czResource edges x = czPhase edges x * Uniform (Reg n) x := by
  exact Matrix.mulVec_diagonal _ _ _

/-- The frame matrix acts pointwise by multiplication by `framePhase`. -/
private theorem frameMatrix_apply {n : ℕ} (edges : Finset (Fin n × Fin n))
    (ψ : QState (Reg n)) (x : Reg n) :
    ApplyGate (frameMatrix edges) ψ x = framePhase edges x * ψ x := by
  exact Matrix.mulVec_diagonal _ _ _

/-- For edges ordered by their endpoints, the graph stabilizer at any vertex fixes the CZ
resource. -/
theorem czResource_stabilizer {n : ℕ} (edges : Finset (Fin n × Fin n))
    (horder : ∀ e ∈ edges, e.1 < e.2) (v : Fin n) :
    ApplyGate (stabilizer edges v) (czResource edges) = czResource edges := by
  funext x
  rw [apply_stabilizer, neighborPhase_flip edges horder, czResource_apply,
    czResource_apply, czPhase_flip edges horder]
  change neighborPhase edges v x * (neighborPhase edges v x * czPhase edges x *
    Uniform (Reg n) x) = _
  rw [← mul_assoc, ← mul_assoc, neighborPhase_sq, one_mul]

/-- Ordered graph resources are normalized, have the stated stabilizer eigenvalues, and are
carried from the source resource to the stabilized CZ resource by the frame word. See
[RaussendorfBriegel2000]. -/
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
