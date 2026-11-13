/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.ClusterWireInstrument
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Cluster CZ preparation and instrument

This module constructs a four-qubit resource preparation and the two-outcome-bit instrument
implementing a logical CZ. It defines physical Hadamard and edge gates, the input and prepared
frames, raw Kraus operators, and outcome-dependent Pauli feedback.

The corrected Kraus operators retain an explicit outcome-dependent sign and have amplitude
magnitude one half. Every instrument branch is one quarter of CZ conjugation, and forgetting or
conditioning outcomes yields the expected logical action, in the measurement-based setting of
[RaussendorfBriegel2000].

## Main statements

* `cluster_cz_actual_resource_preparation`: isometric resource preparation by a seven-gate
  circuit.
* `cluster_cz_raw_corrected_kraus_phase_and_completeness`: exact Kraus phases and completeness.
* `cluster_cz_instrument_arbitrary_probability_conditioning`: branch maps, probabilities,
  forgetting, and conditional states.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.WireComposition

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

/-- The equivalence encoding two pairs of Boolean qubits as a sixteen-dimensional computational
basis. -/
def clusterCZRegisterEquiv : (Bool × Bool) × (Bool × Bool) ≃ Fin 16 :=
  (Equiv.prodCongr teleportOutcomeEquiv teleportOutcomeEquiv).trans finProdFinEquiv

/-- The embedding of two logical qubits into physical vertices `a` and `d`, with vertices `b`
and `c` initialized to zero. -/
def clusterCZInitialFrame : Matrix (Fin 16) (Fin 4) ℂ :=
  Matrix.of fun r i =>
    if r = clusterCZRegisterEquiv (teleportOutcomeEquiv.symm i, (false, false)) then 1 else 0

/-- Each column of the CZ input frame is the relabeled basis vector with the logical input in
the first pair and zeros in the second. -/
theorem clusterCZInitialFrame_column (i : Fin 4) (r : Fin 16) :
    clusterCZInitialFrame r i
      = relabelState clusterCZRegisterEquiv
          (Qatlib.Foundations.PureStateMath.Ket (teleportOutcomeEquiv.symm i, (false, false))) r := by
  by_cases h : r = clusterCZRegisterEquiv (teleportOutcomeEquiv.symm i, (false, false))
  · subst h
    simp [clusterCZInitialFrame, relabelState, Qatlib.Foundations.PureStateMath.Ket,
        Equiv.symm_apply_apply]
  · have h2 : clusterCZRegisterEquiv.symm r ≠ (teleportOutcomeEquiv.symm i, (false, false)) := by
      intro hc
      apply h
      have h3 := congrArg clusterCZRegisterEquiv hc
      rwa [Equiv.apply_symm_apply] at h3
    simp [clusterCZInitialFrame, relabelState, Qatlib.Foundations.PureStateMath.Ket, h, h2]

/-- The CZ input frame is an isometry. -/
theorem clusterCZInitialFrame_isometry : IsIsometry clusterCZInitialFrame := by
  have hInj : ∀ i j : Fin 4,
      clusterCZRegisterEquiv (teleportOutcomeEquiv.symm i, (false, false))
        = clusterCZRegisterEquiv (teleportOutcomeEquiv.symm j, (false, false)) → i = j := by
    intro i j hij
    have h2 := congrArg clusterCZRegisterEquiv.symm hij
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Prod.mk.injEq] at h2
    exact teleportOutcomeEquiv.symm.injective h2.1
  have h : clusterCZInitialFrameᴴ * clusterCZInitialFrame = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hval : ∀ r : Fin 16, clusterCZInitialFrameᴴ i r * clusterCZInitialFrame r i
          = if r = clusterCZRegisterEquiv (teleportOutcomeEquiv.symm i, (false, false))
              then (1 : ℂ) else 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold clusterCZInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = clusterCZRegisterEquiv (teleportOutcomeEquiv.symm i, (false, false))
        · rw [if_pos hr]; simp
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply,
        Finset.sum_congr rfl (fun r _ => hval r),
        Finset.sum_ite_eq' Finset.univ
          (clusterCZRegisterEquiv (teleportOutcomeEquiv.symm i, (false, false)))
          (fun _ => (1 : ℂ)),
        if_pos (Finset.mem_univ _)]
      simp
    · have hzero : ∀ r : Fin 16,
          clusterCZInitialFrameᴴ i r * clusterCZInitialFrame r j = 0 := by
        intro r
        rw [conjTranspose_apply]
        unfold clusterCZInitialFrame
        simp only [Matrix.of_apply]
        by_cases hr : r = clusterCZRegisterEquiv (teleportOutcomeEquiv.symm i, (false, false))
        · rw [if_pos hr, if_neg (fun hc => hij (hInj i j (hr.symm.trans hc))), mul_zero]
        · rw [if_neg hr, star_zero, zero_mul]
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hzero r),
        Finset.sum_const_zero]
      simp [hij]
  exact h

/-- The Hadamard on physical vertex `a` in Boolean product coordinates. -/
noncomputable def clusterCZHaB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))
    (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)

/-- The Hadamard on physical vertex `d` in Boolean product coordinates. -/
noncomputable def clusterCZHdB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)
    (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)

/-- The Hadamard on physical vertex `b` in Boolean product coordinates. -/
noncomputable def clusterCZHbB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))

/-- The Hadamard on physical vertex `c` in Boolean product coordinates. -/
noncomputable def clusterCZHcB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)

/-- The diagonal CZ gate joining physical vertices `a` and `b` in Boolean coordinates. -/
noncomputable def clusterCZEdgeAbB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  Matrix.diagonal fun p => if p.1.1 && p.2.1 then (-1 : ℂ) else 1

/-- The diagonal CZ gate joining physical vertices `d` and `c` in Boolean coordinates. -/
noncomputable def clusterCZEdgeDcB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  Matrix.diagonal fun p => if p.1.2 && p.2.2 then (-1 : ℂ) else 1

/-- The diagonal CZ gate joining physical vertices `b` and `c` in Boolean coordinates. -/
noncomputable def clusterCZEdgeBcB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  Matrix.diagonal fun p => if p.2.1 && p.2.2 then (-1 : ℂ) else 1

/-- The Hadamard on vertex `a` relabeled to `Fin 16`. -/
noncomputable def clusterCZHaGate : Operator 16 := relabelGate clusterCZRegisterEquiv clusterCZHaB

/-- The Hadamard on vertex `d` relabeled to `Fin 16`. -/
noncomputable def clusterCZHdGate : Operator 16 := relabelGate clusterCZRegisterEquiv clusterCZHdB

/-- The Hadamard on vertex `b` relabeled to `Fin 16`. -/
noncomputable def clusterCZHbGate : Operator 16 := relabelGate clusterCZRegisterEquiv clusterCZHbB

/-- The Hadamard on vertex `c` relabeled to `Fin 16`. -/
noncomputable def clusterCZHcGate : Operator 16 := relabelGate clusterCZRegisterEquiv clusterCZHcB

/-- The physical CZ on vertices `a` and `b`, relabeled to `Fin 16`. -/
noncomputable def clusterCZEdgeAbGate : Operator 16 :=
  relabelGate clusterCZRegisterEquiv clusterCZEdgeAbB

/-- The physical CZ on vertices `d` and `c`, relabeled to `Fin 16`. -/
noncomputable def clusterCZEdgeDcGate : Operator 16 :=
  relabelGate clusterCZRegisterEquiv clusterCZEdgeDcB

/-- The physical CZ on vertices `b` and `c`, relabeled to `Fin 16`. -/
noncomputable def clusterCZEdgeBcGate : Operator 16 :=
  relabelGate clusterCZRegisterEquiv clusterCZEdgeBcB

/-- The Boolean-coordinate Hadamard on vertex `a` is unitary. -/
theorem clusterCZHaB_unitary :
    clusterCZHaB ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ :=
  tensorGate_unitary (tensorGate_unitary hadamard_unitary (Submonoid.one_mem _))
    (Submonoid.one_mem _)

/-- The Boolean-coordinate Hadamard on vertex `d` is unitary. -/
theorem clusterCZHdB_unitary :
    clusterCZHdB ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ :=
  tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
    (Submonoid.one_mem _)

/-- The Boolean-coordinate Hadamard on vertex `b` is unitary. -/
theorem clusterCZHbB_unitary :
    clusterCZHbB ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ :=
  tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary hadamard_unitary (Submonoid.one_mem _))

/-- The Boolean-coordinate Hadamard on vertex `c` is unitary. -/
theorem clusterCZHcB_unitary :
    clusterCZHcB ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ :=
  tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)

/-- The Boolean-coordinate CZ on vertices `a` and `b` is unitary. -/
theorem clusterCZEdgeAbB_unitary :
    clusterCZEdgeAbB ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ := by
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  obtain ⟨⟨a, d⟩, ⟨b, c⟩⟩ := p
  cases a <;> cases b <;> simp

/-- The Boolean-coordinate CZ on vertices `d` and `c` is unitary. -/
theorem clusterCZEdgeDcB_unitary :
    clusterCZEdgeDcB ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ := by
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  obtain ⟨⟨a, d⟩, ⟨b, c⟩⟩ := p
  cases d <;> cases c <;> simp

/-- The Boolean-coordinate CZ on vertices `b` and `c` is unitary. -/
theorem clusterCZEdgeBcB_unitary :
    clusterCZEdgeBcB ∈ Matrix.unitaryGroup ((Bool × Bool) × (Bool × Bool)) ℂ := by
  refine diagonal_mem_unitaryGroup _ fun p => ?_
  obtain ⟨⟨a, d⟩, ⟨b, c⟩⟩ := p
  cases b <;> cases c <;> simp

/-- The finite-index Hadamard on vertex `a` is unitary. -/
theorem clusterCZHaGate_unitary : clusterCZHaGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZHaB_unitary _

/-- The finite-index Hadamard on vertex `d` is unitary. -/
theorem clusterCZHdGate_unitary : clusterCZHdGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZHdB_unitary _

/-- The finite-index Hadamard on vertex `b` is unitary. -/
theorem clusterCZHbGate_unitary : clusterCZHbGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZHbB_unitary _

/-- The finite-index Hadamard on vertex `c` is unitary. -/
theorem clusterCZHcGate_unitary : clusterCZHcGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZHcB_unitary _

/-- The finite-index CZ on vertices `a` and `b` is unitary. -/
theorem clusterCZEdgeAbGate_unitary : clusterCZEdgeAbGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZEdgeAbB_unitary _

/-- The finite-index CZ on vertices `d` and `c` is unitary. -/
theorem clusterCZEdgeDcGate_unitary : clusterCZEdgeDcGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZEdgeDcB_unitary _

/-- The finite-index CZ on vertices `b` and `c` is unitary. -/
theorem clusterCZEdgeBcGate_unitary : clusterCZEdgeBcGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  teleportRelabelGate_mem_unitaryGroup clusterCZEdgeBcB_unitary _

/-- The resource preparation matrix in Boolean coordinates, consisting of four Hadamards
followed by three CZ edges. -/
noncomputable def clusterCZPreparationB :
    Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ :=
  clusterCZEdgeBcB * (clusterCZEdgeDcB * (clusterCZEdgeAbB *
    (clusterCZHcB * (clusterCZHbB * (clusterCZHdB * clusterCZHaB)))))

/-- The finite-index resource preparation matrix consisting of four Hadamards followed by three
CZ edges. -/
noncomputable def clusterCZPreparationGate : Operator 16 :=
  clusterCZEdgeBcGate * (clusterCZEdgeDcGate * (clusterCZEdgeAbGate *
    (clusterCZHcGate * (clusterCZHbGate * (clusterCZHdGate * clusterCZHaGate)))))

/-- The finite-index CZ preparation matrix is the relabeling of its Boolean-coordinate form. -/
theorem clusterCZPreparationGate_eq_relabel :
    clusterCZPreparationGate = relabelGate clusterCZRegisterEquiv clusterCZPreparationB := by
  unfold clusterCZPreparationGate clusterCZPreparationB clusterCZEdgeBcGate clusterCZEdgeDcGate
    clusterCZEdgeAbGate clusterCZHcGate clusterCZHbGate clusterCZHdGate clusterCZHaGate
  rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul,
    ← teleportRelabelGate_mul, ← teleportRelabelGate_mul, ← teleportRelabelGate_mul]

/-- The full CZ resource preparation matrix is unitary. -/
theorem clusterCZPreparationGate_unitary :
    clusterCZPreparationGate ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  Submonoid.mul_mem _ clusterCZEdgeBcGate_unitary
    (Submonoid.mul_mem _ clusterCZEdgeDcGate_unitary
      (Submonoid.mul_mem _ clusterCZEdgeAbGate_unitary
        (Submonoid.mul_mem _ clusterCZHcGate_unitary
          (Submonoid.mul_mem _ clusterCZHbGate_unitary
            (Submonoid.mul_mem _ clusterCZHdGate_unitary clusterCZHaGate_unitary)))))

/-- The seven-gate circuit implementing the CZ resource preparation. -/
noncomputable def clusterCZPreparationCircuit : Circuit (Fin 16) :=
  [Step.gate clusterCZHaGate, Step.gate clusterCZHdGate, Step.gate clusterCZHbGate,
    Step.gate clusterCZHcGate, Step.gate clusterCZEdgeAbGate, Step.gate clusterCZEdgeDcGate,
    Step.gate clusterCZEdgeBcGate]

/-- The prepared CZ resource frame obtained by applying `clusterCZPreparationGate` to the input
frame. -/
noncomputable def clusterCZPreparedFrame : Matrix (Fin 16) (Fin 4) ℂ :=
  clusterCZPreparationGate * clusterCZInitialFrame

/-- The prepared CZ resource frame is an isometry. -/
theorem clusterCZPreparedFrame_isometry : IsIsometry clusterCZPreparedFrame := by
  have hU : clusterCZPreparationGateᴴ * clusterCZPreparationGate = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp clusterCZPreparationGate_unitary
    rwa [Matrix.star_eq_conjTranspose] at h
  show clusterCZPreparedFrameᴴ * clusterCZPreparedFrame = 1
  rw [clusterCZPreparedFrame, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc clusterCZPreparationGateᴴ clusterCZPreparationGate
      clusterCZInitialFrame, hU, Matrix.one_mul]
  exact clusterCZInitialFrame_isometry

/-- The initial and prepared CZ frames are isometries, and the unitary preparation is
implemented on every input by a query-free seven-gate circuit. See [RaussendorfBriegel2000]. -/
theorem cluster_cz_actual_resource_preparation :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry clusterCZInitialFrame ∧
      clusterCZPreparationGate ∈ Matrix.unitaryGroup (Fin 16) ℂ ∧
      clusterCZPreparedFrame = clusterCZPreparationGate * clusterCZInitialFrame ∧
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry clusterCZPreparedFrame ∧
      QueryCount clusterCZPreparationCircuit = 0 ∧ GateCount clusterCZPreparationCircuit = 7 ∧
      (∀ ψ : QState (Fin 4), Run (1 : Operator 16) clusterCZPreparationCircuit
        (clusterCZInitialFrame *ᵥ ψ) = clusterCZPreparedFrame *ᵥ ψ) := by
  refine ⟨clusterCZInitialFrame_isometry, clusterCZPreparationGate_unitary, rfl,
    clusterCZPreparedFrame_isometry, rfl, rfl, fun ψ => ?_⟩
  simp only [clusterCZPreparationCircuit, run_gate, run_nil, ApplyGate]
  conv_rhs => rw [clusterCZPreparedFrame, ← Matrix.mulVec_mulVec, clusterCZPreparationGate,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- The Hadamard on vertex `a` forms the normalized sum or difference of the two amplitudes at
that vertex. -/
theorem clusterCZHaB_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCZHaB ψ = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
      (ψ ((false, p.1.2), p.2) + (if p.1.1 then (-1 : ℂ) else 1) * ψ ((true, p.1.2), p.2)) := by
  rw [show clusterCZHaB = TensorGate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))
      (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) from rfl, applyGate_firstFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_firstFactor]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply, Fintype.sum_bool]
  cases a0 <;> simp <;> ring

/-- The Hadamard on vertex `d` forms the normalized sum or difference of the two amplitudes at
that vertex. -/
theorem clusterCZHdB_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCZHdB ψ = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
      (ψ ((p.1.1, false), p.2) + (if p.1.2 then (-1 : ℂ) else 1) * ψ ((p.1.1, true), p.2)) := by
  rw [show clusterCZHdB = TensorGate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)
      (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) from rfl, applyGate_firstFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_secondFactor]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply, Fintype.sum_bool]
  cases d0 <;> simp <;> ring

/-- The Hadamard on vertex `b` forms the normalized sum or difference of the two amplitudes at
that vertex. -/
theorem clusterCZHbB_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCZHbB ψ = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
      (ψ (p.1, (false, p.2.2)) + (if p.2.1 then (-1 : ℂ) else 1) * ψ (p.1, (true, p.2.2))) := by
  rw [show clusterCZHbB = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (TensorGate Hadamard (1 : Matrix Bool Bool ℂ)) from rfl, applyGate_secondFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_firstFactor]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply, Fintype.sum_bool]
  cases b0 <;> simp <;> ring

/-- The Hadamard on vertex `c` forms the normalized sum or difference of the two amplitudes at
that vertex. -/
theorem clusterCZHcB_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCZHcB ψ = fun p => ((Real.sqrt 2 : ℂ)⁻¹) *
      (ψ (p.1, (p.2.1, false)) + (if p.2.2 then (-1 : ℂ) else 1) * ψ (p.1, (p.2.1, true))) := by
  rw [show clusterCZHcB = TensorGate (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard) from rfl, applyGate_secondFactor]
  funext p
  obtain ⟨⟨a0, d0⟩, ⟨b0, c0⟩⟩ := p
  rw [applyGate_secondFactor]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Hadamard, Matrix.of_apply, Fintype.sum_bool]
  cases c0 <;> simp <;> ring

/-- The CZ edge between `a` and `b` multiplies the amplitude by minus one exactly when both
endpoint bits are true. -/
theorem clusterCZEdgeAbB_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCZEdgeAbB ψ
      = fun p => (if p.1.1 && p.2.1 then (-1 : ℂ) else 1) * ψ p := by
  rw [show clusterCZEdgeAbB = Matrix.diagonal
      (fun p : (Bool × Bool) × (Bool × Bool) => if p.1.1 && p.2.1 then (-1 : ℂ) else 1) from rfl,
    applyGate_diagonal]

/-- The CZ edge between `d` and `c` multiplies the amplitude by minus one exactly when both
endpoint bits are true. -/
theorem clusterCZEdgeDcB_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCZEdgeDcB ψ
      = fun p => (if p.1.2 && p.2.2 then (-1 : ℂ) else 1) * ψ p := by
  rw [show clusterCZEdgeDcB = Matrix.diagonal
      (fun p : (Bool × Bool) × (Bool × Bool) => if p.1.2 && p.2.2 then (-1 : ℂ) else 1) from rfl,
    applyGate_diagonal]

/-- The CZ edge between `b` and `c` multiplies the amplitude by minus one exactly when both
endpoint bits are true. -/
theorem clusterCZEdgeBcB_apply (ψ : QState ((Bool × Bool) × (Bool × Bool))) :
    ApplyGate clusterCZEdgeBcB ψ
      = fun p => (if p.2.1 && p.2.2 then (-1 : ℂ) else 1) * ψ p := by
  rw [show clusterCZEdgeBcB = Matrix.diagonal
      (fun p : (Bool × Bool) × (Bool × Bool) => if p.2.1 && p.2.2 then (-1 : ℂ) else 1) from rfl,
    applyGate_diagonal]

set_option maxHeartbeats 4000000 in

/-- The decoded CZ resource column has amplitude one half times the output CZ sign, supported
where the first pair equals the input bits XOR the second pair. -/
theorem clusterCZDecoded (x y : Bool) :
    ApplyGate (clusterCZHdB * (clusterCZHaB * clusterCZPreparationB))
        (Qatlib.Foundations.PureStateMath.Ket ((x, y), (false, false)))
      = fun p : (Bool × Bool) × (Bool × Bool) =>
          (1 / 2 : ℂ) * (if p.1.1 = (x ^^ p.2.1) ∧ p.1.2 = (y ^^ p.2.2)
            then (if p.2.1 && p.2.2 then (-1 : ℂ) else 1) else 0) := by
  rw [clusterCZPreparationB, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul,
    applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul,
    clusterCZHdB_apply, clusterCZHaB_apply, clusterCZEdgeBcB_apply, clusterCZEdgeDcB_apply,
    clusterCZEdgeAbB_apply, clusterCZHcB_apply, clusterCZHbB_apply, clusterCZHdB_apply,
    clusterCZHaB_apply]
  funext p
  obtain ⟨⟨a', d'⟩, ⟨b, c⟩⟩ := p
  cases x <;> cases y <;> cases a' <;> cases d' <;> cases b <;> cases c <;>
    simp [Qatlib.Foundations.PureStateMath.Ket, sqrt2_inv_sq, mul_comm, mul_left_comm] <;> ring_nf <;>
      try (rw [pow_two, sqrt2_inv_sq]) <;> ring_nf

/-- The logical Kraus matrix extracted at measurement outcomes `a` and `d` after preparation and
decoding. -/
noncomputable def clusterCZRawKraus (a d : Bool) : Operator 4 :=
  Matrix.of fun c i =>
    (clusterCZHdGate * clusterCZHaGate * clusterCZPreparationGate * clusterCZInitialFrame)
      (clusterCZRegisterEquiv ((a, d), teleportOutcomeEquiv.symm c)) i

/-- The logical tensor-product X correction specified by the two measurement bits. -/
noncomputable def clusterCZInputPauli (a d : Bool) : Operator 4 :=
  relabelGate teleportOutcomeEquiv
    (TensorGate (if a then PauliX else 1) (if d then PauliX else 1))

/-- The logical Pauli feedback consisting of outcome-dependent X corrections and the
cross-coupled Z corrections. -/
noncomputable def clusterCZLogicalFeedback (a d : Bool) : Operator 4 :=
  relabelGate teleportOutcomeEquiv
    (TensorGate ((if d then PauliZ else 1) * (if a then PauliX else 1))
      ((if a then PauliZ else 1) * (if d then PauliX else 1)))

/-- The raw CZ Kraus operator followed by its logical Pauli feedback. -/
noncomputable def clusterCZCorrectedKraus (a d : Bool) : Operator 4 :=
  clusterCZLogicalFeedback a d * clusterCZRawKraus a d

/-- The raw CZ Kraus operator is one half of the logical CZ composed with the outcome-dependent
input X operators. -/
theorem clusterCZRawKraus_eq (a d : Bool) :
    clusterCZRawKraus a d = (1 / 2 : ℂ) • (clusterCZ * clusterCZInputPauli a d) := by
  ext c i
  obtain ⟨⟨b', c'⟩, rfl⟩ : ∃ q : Bool × Bool, c = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  obtain ⟨⟨x, y⟩, rfl⟩ : ∃ q : Bool × Bool, i = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  have hG : clusterCZHdGate * clusterCZHaGate * clusterCZPreparationGate
      = relabelGate clusterCZRegisterEquiv
          (clusterCZHdB * (clusterCZHaB * clusterCZPreparationB)) := by
    rw [Matrix.mul_assoc, clusterCZPreparationGate_eq_relabel]
    unfold clusterCZHdGate clusterCZHaGate
    rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul]
  have hcol : (fun r : Fin 16 => clusterCZInitialFrame r (teleportOutcomeEquiv (x, y)))
      = relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((x, y), (false, false))) := by
    funext r
    rw [clusterCZInitialFrame_column, Equiv.symm_apply_apply]
  have hP : clusterCZ * clusterCZInputPauli a d
      = relabelGate teleportOutcomeEquiv
          (clusterCZb * TensorGate (if a then PauliX else 1) (if d then PauliX else 1)) := by
    unfold clusterCZ clusterCZInputPauli
    rw [← teleportRelabelGate_mul]
  simp only [clusterCZRawKraus, Matrix.of_apply, Equiv.symm_apply_apply]
  rw [Matrix.smul_apply, smul_eq_mul, hP, matrix_mul_column, hG, hcol, applyGate_relabelGate,
    clusterCZDecoded]
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    relabelState, Function.comp_apply, Matrix.mul_apply, clusterCZb, Matrix.diagonal_apply]
  cases a <;> cases d <;> cases b' <;> cases c' <;> cases x <;> cases y <;>
    simp [TensorGate, Fintype.sum_prod_type, PauliX, permMatrix,
      Matrix.one_apply, Matrix.of_apply]

/-- The Boolean-coordinate Pauli feedback cancels the input X byproducts of CZ up to the sign
that is negative exactly when both outcomes are true. -/
theorem clusterCZFeedbackBool_mul (a d : Bool) :
    TensorGate ((if d then PauliZ else 1) * (if a then PauliX else 1))
        ((if a then PauliZ else 1) * (if d then PauliX else 1)) *
      (clusterCZb * TensorGate (if a then PauliX else 1) (if d then PauliX else 1))
    = (if a && d then (-1 : ℂ) else 1) • clusterCZb := by
  ext ⟨b, c⟩ ⟨x, y⟩
  cases a <;> cases d <;> cases b <;> cases c <;> cases x <;> cases y <;>
    simp [TensorGate, Matrix.mul_apply, Fintype.sum_prod_type, clusterCZb,
      Matrix.diagonal_apply, PauliX, PauliZ, permMatrix, Matrix.one_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul]

/-- The corrected CZ Kraus operator equals the logical CZ multiplied by one half and the sign
determined by the conjunction of the outcomes. -/
theorem clusterCZCorrectedKraus_eq (a d : Bool) :
    clusterCZCorrectedKraus a d
      = ((if a && d then (-1 : ℂ) else 1) / 2) • clusterCZ := by
  have hP : clusterCZ * clusterCZInputPauli a d
      = relabelGate teleportOutcomeEquiv
          (clusterCZb * TensorGate (if a then PauliX else 1) (if d then PauliX else 1)) := by
    unfold clusterCZ clusterCZInputPauli
    rw [← teleportRelabelGate_mul]
  rw [clusterCZCorrectedKraus, clusterCZRawKraus_eq, Matrix.mul_smul, hP]
  rw [clusterCZLogicalFeedback, ← teleportRelabelGate_mul, clusterCZFeedbackBool_mul]
  ext c i
  simp [clusterCZ, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  cases a <;> cases d <;> simp; ring

/-- The raw and corrected CZ Kraus operators have the stated Pauli and phase formulas, and the
corrected Kraus family satisfies completeness. See [RaussendorfBriegel2000]. -/
theorem cluster_cz_raw_corrected_kraus_phase_and_completeness :
    ∀ a d : Bool,
      clusterCZRawKraus a d = (1 / 2 : ℂ) • (clusterCZ * clusterCZInputPauli a d) ∧
      clusterCZCorrectedKraus a d = clusterCZLogicalFeedback a d * clusterCZRawKraus a d ∧
      clusterCZCorrectedKraus a d = ((if a && d then (-1 : ℂ) else 1) / 2) • clusterCZ ∧
      (∑ o : Bool × Bool, (clusterCZCorrectedKraus o.1 o.2)ᴴ * clusterCZCorrectedKraus o.1 o.2)
        = 1 := by
  intro a d
  refine ⟨clusterCZRawKraus_eq a d, rfl, clusterCZCorrectedKraus_eq a d, ?_⟩
  have hCZ : (clusterCZ : Operator 4)ᴴ * clusterCZ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp clusterCZ_unitary
    rwa [Matrix.star_eq_conjTranspose] at h
  have hterm : ∀ o : Bool × Bool,
      (clusterCZCorrectedKraus o.1 o.2)ᴴ * clusterCZCorrectedKraus o.1 o.2
        = (1 / 4 : ℂ) • (1 : Operator 4) := by
    intro o
    obtain ⟨o1, o2⟩ := o
    rw [clusterCZCorrectedKraus_eq o1 o2, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hCZ]
    have hstar : star ((if o1 && o2 then (-1 : ℂ) else 1) / 2)
        = (if o1 && o2 then (-1 : ℂ) else 1) / 2 := by
      cases o1 <;> cases o2 <;> norm_num
    rw [hstar]
    cases o1 <;> cases o2 <;> norm_num
  rw [Finset.sum_congr rfl (fun o _ => hterm o), sum_univ_boolPair_smul,
    show ((4 : ℂ) * (1 / 4)) = 1 from by norm_num, one_smul]

/-- The four-outcome instrument built from the corrected CZ Kraus operators. -/
noncomputable def clusterCZInstrument : Instrument (Bool × Bool) 4 4 :=
  Instrument.ofKraus (fun o : Bool × Bool => clusterCZCorrectedKraus o.1 o.2)
    (cluster_cz_raw_corrected_kraus_phase_and_completeness false false).2.2.2

/-- Each CZ instrument branch is one quarter of conjugation by `clusterCZ`. -/
theorem clusterCZInstrument_branch_apply (ρ : Operator 4) (a d : Bool) :
    clusterCZInstrument.branch (a, d) ρ = (1 / 4 : ℂ) • conjBranch clusterCZ ρ := by
  have hstar : star ((if a && d then (-1 : ℂ) else 1) / 2)
      = (if a && d then (-1 : ℂ) else 1) / 2 := by
    cases a <;> cases d <;> norm_num
  rw [show clusterCZInstrument.branch (a, d) ρ
      = clusterCZCorrectedKraus a d * ρ * (clusterCZCorrectedKraus a d)ᴴ from rfl,
    clusterCZCorrectedKraus_eq, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, smul_smul, hstar]
  cases a <;> cases d <;> norm_num [conjBranch_apply]

/-- Each CZ branch is one quarter of CZ conjugation with probability equal to the real trace
divided by four; forgetting outcomes gives CZ conjugation, as does conditioning a density
input on any positive-probability outcome. -/
theorem cluster_cz_instrument_arbitrary_probability_conditioning :
    ∀ (ρ : Operator 4) (a d : Bool),
      clusterCZInstrument.branch (a, d) ρ = (1 / 4 : ℂ) • conjBranch clusterCZ ρ ∧
      instrumentProb clusterCZInstrument ρ (a, d) = (Matrix.trace ρ).re / 4 ∧
      clusterCZInstrument.forget.map ρ = conjBranch clusterCZ ρ ∧
      (IsDensityOperator ρ → ∀ h : 0 < instrumentProb clusterCZInstrument ρ (a, d),
        clusterCZInstrument.conditionalState ρ (a, d) h = conjBranch clusterCZ ρ) := by
  intro ρ a d
  refine ⟨clusterCZInstrument_branch_apply ρ a d, ?_, ?_, ?_⟩
  · rw [instrumentProb, clusterCZInstrument_branch_apply ρ a d, Matrix.trace_smul, smul_eq_mul,
      trace_conjBranch_unitary clusterCZ clusterCZ_unitary ρ, Complex.mul_re]
    simp
    ring
  · rw [Instrument.forget_apply,
      Finset.sum_congr rfl fun o _ => clusterCZInstrument_branch_apply ρ o.1 o.2,
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4)) = 1 from by norm_num, one_smul]
  · intro hρ h
    have htr : Matrix.trace ρ = 1 := hρ.2
    have hprob : instrumentProb clusterCZInstrument ρ (a, d) = 1 / 4 := by
      rw [instrumentProb, clusterCZInstrument_branch_apply ρ a d, Matrix.trace_smul,
        smul_eq_mul, trace_conjBranch_unitary clusterCZ clusterCZ_unitary ρ, htr]
      norm_num
    have hrecon := (Instrument.conditionalState_reconstruction clusterCZInstrument ρ (a, d) h).1
    rw [hprob, clusterCZInstrument_branch_apply] at hrecon
    have hquarter : (((1 / 4 : ℝ)) : ℂ) = (1 / 4 : ℂ) := by norm_num
    rw [hquarter] at hrecon
    have hscaled := congrArg (fun σ : Operator 4 => (4 : ℂ) • σ) hrecon
    simpa only [smul_smul, show (4 : ℂ) * (1 / 4) = 1 from by norm_num, one_smul]
      using hscaled

end Qatlib.Concepts.ClusterPatterns.WireComposition
