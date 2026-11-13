/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore
import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution

/-!
# Controlled qDRIFT simulation

The controlled-copy Hamiltonian embedding preserves Hermiticity and the unit
norm bound, and commutes with taking the weighted Hamiltonian mean. Applying
qDRIFT to these embedded components gives finite diamond-distance error at
most `2 * lam² * t² / N`. Each sampled path is a unitary circuit with exactly
`N` gates in the component-gate model.

The randomized compiler is introduced in [Campbell2019]. This module applies
it to the explicit controlled-copy embedding.
-/
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ReferenceModel
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.RandCompiler19.ControlledDrift

/-- A Hermitian operator of norm at most one yields a controlled copy Hamiltonian that is
Hermitian and has norm at most one. -/
theorem source_controlled_components (D : ℕ) (K : Operator D)
    (hK : K.IsHermitian) (hKn : ‖K‖ ≤ 1) :
    (controlledCopyHamiltonian D K).IsHermitian ∧ ‖controlledCopyHamiltonian D K‖ ≤ 1 := by
  constructor
  · have hh : (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) K).IsHermitian := by
      show (TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)) K)ᴴ = _
      rw [tensorGate_conjTranspose, hK.eq,
          (outerProduct_posSemidef (Qatlib.Foundations.PureStateMath.Ket true)).isHermitian.eq]
    exact hh.submatrix (controlDataEquiv D).symm
  · rw [controlledCopyHamiltonian, l2_norm_relabelGate, l2_norm_tensorGate]
    have hp : ‖outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool)‖ ≤ 1 := by
      have he : outerProduct (Qatlib.Foundations.PureStateMath.Ket true : QState Bool) =
          Matrix.diagonal (fun b : Bool => if b then (1 : ℂ) else 0) := by
        ext b c
        cases b <;> cases c <;> simp [outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket]
      rw [he, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro b; cases b <;> simp)
    exact (mul_le_mul hp hKn (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

/-- Forming the qDRIFT mean Hamiltonian commutes with the controlled copy-Hamiltonian
construction. -/
theorem source_controlled_mean (L D : ℕ) (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam : ℝ) :
    qdriftHamiltonian d (fun j => controlledCopyHamiltonian D (K j)) lam =
      controlledCopyHamiltonian D (qdriftHamiltonian d K lam) := by
  ext a b
  simp [qdriftHamiltonian, controlledCopyHamiltonian, relabelGate, TensorGate,
    Matrix.smul_apply, Matrix.sum_apply, Finset.mul_sum, mul_assoc, mul_comm]

/-- The qDRIFT error bound survives the controlled-copy Hamiltonian embedding;
compare [Campbell, qDRIFT][Campbell2019]. -/
theorem source_controlled_error (L D N : ℕ) (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam t : ℝ) (hlam : 0 ≤ lam) (hN : 0 < N)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    finiteDiamondDistance (exactQdriftMap d (fun j => controlledCopyHamiltonian D (K j)) lam t N)
      (conjBranch (copyControlledEvolution (qdriftHamiltonian d K lam) t)) ≤
        ENNReal.ofReal (2*lam^2*t^2/(N:ℝ)) := by
  have h := (exact_qdrift_actual_finite_diamond_budget L (2*D) d
    (fun j => controlledCopyHamiltonian D (K j)) lam t N hlam hN
    (fun j => source_controlled_components D (K j) (hK j).1 (hK j).2)).1
  rwa [source_controlled_mean, ← copyControlledEvolution_hamiltonian] at h

/-- For Hermitian component operators of norm at most one, a controlled qDRIFT path has word
length and circuit gate count `N`, its fold agrees with circuit execution, and its circuit
is unitary [Campbell2019]. -/
theorem source_controlled_path_cost (L D N : ℕ) (K : Fin L → Operator D)
    (ω : Fin N → Fin L) (s : ℝ) (ψ : QState (Fin (2*D)))
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    (qdriftComponentWord ω s).length = N ∧
    (qdriftComponentWord ω s).foldl
      (fun v step => ApplyGate (HamiltonianEvolution
        (controlledCopyHamiltonian D (K step.1)) step.2) v) ψ =
      Run 1 (mixturePathCircuit
        (fun j => HamiltonianEvolution (controlledCopyHamiltonian D (K j)) s) ω) ψ ∧
    GateCount (mixturePathCircuit
      (fun j => HamiltonianEvolution (controlledCopyHamiltonian D (K j)) s) ω) = N ∧
    IsUnitaryCircuit (mixturePathCircuit
      (fun j => HamiltonianEvolution (controlledCopyHamiltonian D (K j)) s) ω) := by
  have h := qdrift_actual_fresh_path_and_component_cost L (2*D) N
    (fun j => controlledCopyHamiltonian D (K j)) ω s ψ
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2
    (fun j => (source_controlled_components D (K j) (hK j).1 (hK j).2).1)⟩

end Qatlib.Papers.RandCompiler19.ControlledDrift
