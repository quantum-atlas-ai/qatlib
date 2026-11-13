/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.CountedClusterSequence

/-!
# Actual cluster Euler rotation examples

The definitions `clusterEulerWord` and `clusterEulerRotation` specialize cluster measurement
sequences to a four-measurement Euler rotation, following the measurement-based framework of
[RaussendorfBriegel2000]. The actual branch sum implements conjugation by the rotation even with
a finite reference system, and each observed branch has explicit gate and measurement counts.

Concrete examples compute the three-angle `π/2` matrix and its action on a basis-state density.
Further statements verify the empty sequence and the four-unit-phase identity sequence,
including a mixed-state input.

## Main statements

* `cluster_euler_four_measurement_actual_consumer`: Euler rotation semantics and exact branch
  resource counts.
* `cluster_euler_nontrivial_hadamard_density_consumer`: a nontrivial basis-density
  transformation.
* `cluster_sequence_empty_and_identity_mixed_reference_consumer`: empty and identity sequence
  behavior with reference systems.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.ClusterPatterns.ChainFeedback
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix
open scoped ComplexOrder

/-- The four-entry cluster phase word `[exp(γ*I), exp(β*I), exp(α*I), 1]`. -/
noncomputable def clusterEulerWord (α β γ : ℝ) : List ℂ :=
  [Complex.exp ((γ : ℂ)*Complex.I), Complex.exp ((β : ℂ)*Complex.I),
    Complex.exp ((α : ℂ)*Complex.I), 1]

/-- The relabeled one-qubit matrix `Rz α * Hadamard * Rz β * Hadamard * Rz γ`. -/
noncomputable def clusterEulerRotation (α β γ : ℝ) : Operator 2 :=
  relabelGate boolEquivFin2 (Rz α * Hadamard * Rz β * Hadamard * Rz γ)

/-- A cluster phase with parameter `exp(θ*I)` equals the relabeled gate `Rz θ`. -/
private theorem euler_phase (θ : ℝ) :
    clusterPhase (Complex.exp ((θ : ℂ)*Complex.I)) = relabelGate boolEquivFin2 (Rz θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [clusterPhase, Rz, relabelGate, boolEquivFin2]

/-- Every entry of the cluster Euler word has complex norm one. -/
private theorem euler_word_norm (α β γ : ℝ) :
    ∀ z ∈ clusterEulerWord α β γ, ‖z‖ = 1 := by
  simp [clusterEulerWord]

/-- The sequence matrix of the cluster Euler word equals `clusterEulerRotation α β γ`. -/
private theorem euler_word_unitary (α β γ : ℝ) :
    clusterSequenceUnitary (clusterEulerWord α β γ) = clusterEulerRotation α β γ := by
  simp only [clusterEulerWord, clusterSequenceUnitary, Matrix.one_mul, clusterJ_one]
  simp only [clusterJ, euler_phase]
  simp only [← teleportRelabelGate_mul]
  simp only [← Matrix.mul_assoc]
  rw [hadamard_mul_self, Matrix.one_mul]
  rfl

/-- The four-entry cluster Euler word realizes the stated Euler rotation, and summing its actual
branches implements conjugation by that rotation with any finite reference system. Every
observed branch uses exactly 23 gates and four measurements [RaussendorfBriegel2000]. -/
theorem cluster_euler_four_measurement_actual_consumer (α β γ : ℝ) :
    (clusterEulerWord α β γ).length = 4 ∧
    (∀ z ∈ clusterEulerWord α β γ, ‖z‖ = 1) ∧
    clusterSequenceUnitary (clusterEulerWord α β γ) = clusterEulerRotation α β γ ∧
    clusterEulerRotation α β γ =
      relabelGate boolEquivFin2 (Rz α * Hadamard * Rz β * Hadamard * Rz γ) ∧
    (∀ (r : ℕ) (ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ),
      (∑ ω : Reg (clusterEulerWord α β γ).length,
        tensorLeft (clusterSequenceActualBranchMap (clusterEulerWord α β γ) ω) ρ) =
          TensorGate (clusterEulerRotation α β γ) (1 : Operator r) * ρ *
            (TensorGate (clusterEulerRotation α β γ) (1 : Operator r))ᴴ) ∧
    (∀ ω : Reg (clusterEulerWord α β γ).length,
      (observedLeaf 1 (clusterSequenceProgram (clusterEulerWord α β γ))
        (clusterSequenceLeaf (clusterEulerWord α β γ) ω)).gates = 23 ∧
      (observedLeaf 1 (clusterSequenceProgram (clusterEulerWord α β γ))
        (clusterSequenceLeaf (clusterEulerWord α β γ) ω)).measurements = 4) := by
  refine ⟨rfl, euler_word_norm α β γ, euler_word_unitary α β γ, rfl, ?_, ?_⟩
  · intro r ρ
    simpa only [euler_word_unitary] using
      (cluster_sequence_actual_reference_output _ (euler_word_norm α β γ) r ρ (ZeroStr _)).2
  · intro ω
    have h := (cluster_sequence_actual_program_and_feedback_cost _
      (euler_word_norm α β γ)).2.2.2 ω
    exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- The complex exponential `exp((π/2)*I)` equals `I`. -/
private theorem euler_half_pi_phase :
    Complex.exp (((Real.pi/2 : ℝ) : ℂ)*Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I]
  simp

/-- At three angles equal to `π/2`, the cluster Euler rotation is one half times the matrix with
rows `(1+I, 1+I)` and `(1+I, -1-I)`. -/
private theorem euler_half_pi_matrix :
    clusterEulerRotation (Real.pi/2) (Real.pi/2) (Real.pi/2) =
      (1/2 : ℂ) • !![1+Complex.I,1+Complex.I;1+Complex.I,-1-Complex.I] := by
  rw [← euler_word_unitary]
  simp only [clusterEulerWord, euler_half_pi_phase, clusterSequenceUnitary, Matrix.one_mul]
  have hs2 : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt 2 : ℂ)^4 = 4 := by
    calc _ = ((Real.sqrt 2 : ℂ)^2)^2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, clusterJ_entry,
      Matrix.smul_apply, smul_eq_mul, sqrt2_inv_sq] <;>
    ring_nf <;> simp [hs2, hs4, Complex.I_sq] <;> ring

/-- The three-angle `π/2` specialization has the stated phase-scaled Hadamard matrix and sends
the zero-basis pure density to the all-ones matrix divided by two after summing actual
branches. This output differs from the input density. -/
theorem cluster_euler_nontrivial_hadamard_density_consumer :
    clusterEulerRotation (Real.pi/2) (Real.pi/2) (Real.pi/2) =
      (1/2 : ℂ) • !![1+Complex.I,1+Complex.I;1+Complex.I,-1-Complex.I] ∧
    (∑ ω : Reg (clusterEulerWord (Real.pi/2) (Real.pi/2) (Real.pi/2)).length,
      clusterSequenceActualBranchMap (clusterEulerWord (Real.pi/2) (Real.pi/2) (Real.pi/2)) ω
        (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)))) = (1/2 : ℂ) • !![1,1;1,1] ∧
    (∑ ω : Reg (clusterEulerWord (Real.pi/2) (Real.pi/2) (Real.pi/2)).length,
      clusterSequenceActualBranchMap (clusterEulerWord (Real.pi/2) (Real.pi/2) (Real.pi/2)) ω
        (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)))) ≠ outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) := by
  have hout : (∑ ω : Reg (clusterEulerWord (Real.pi/2) (Real.pi/2) (Real.pi/2)).length,
      clusterSequenceActualBranchMap (clusterEulerWord (Real.pi/2) (Real.pi/2) (Real.pi/2)) ω
        (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)))) = (1/2 : ℂ) • !![1,1;1,1] := by
    rw [clusterSequenceActualBranchMap_sum _ (euler_word_norm (Real.pi/2) (Real.pi/2) (Real.pi/2)), euler_word_unitary,
      euler_half_pi_matrix]
    rw [conjBranch_outerProduct]
    have hv : ApplyGate ((1/2 : ℂ) • !![1+Complex.I,1+Complex.I;1+Complex.I,-1-Complex.I])
        (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) = fun _ => (1/2 : ℂ)*(1+Complex.I) := by
      funext i
      fin_cases i <;> simp [ApplyGate, Matrix.mulVec, dotProduct,
        Matrix.smul_apply, smul_eq_mul, ket_apply]
    change ((1/2 : ℂ) • !![1+Complex.I,1+Complex.I;1+Complex.I,-1-Complex.I]) *ᵥ
      Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) = (fun _ => (1/2 : ℂ)*(1+Complex.I)) at hv
    rw [hv]
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      change star (2 : ℂ) = 2
      simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [outerProduct_apply, Matrix.smul_apply, smul_eq_mul] <;>
      ring_nf <;> simp [Complex.I_sq, htwo] <;> ring
  refine ⟨euler_half_pi_matrix, hout, ?_⟩
  rw [hout]
  intro h
  have h00 := congrArg (fun M : Operator 2 => M 0 0) h
  norm_num [Matrix.smul_apply, smul_eq_mul, outerProduct, ket_apply] at h00

/-- Every empty-sequence branch fixes its input, while the four-unit-phase sequence sums to the
identity channel with any finite reference system. The maximally mixed qubit is a non-pure
density operator and is fixed by this sequence. -/
theorem cluster_sequence_empty_and_identity_mixed_reference_consumer :
    (∀ (ρ : Operator 2) (ω : Reg 0), clusterSequenceActualBranchMap [] ω ρ = ρ) ∧
    IsDensityOperator ((1/2 : ℂ) • (1 : Operator 2)) ∧
    ¬ IsPureDensityOperator ((1/2 : ℂ) • (1 : Operator 2)) ∧
    (∑ ω : Reg ([1,1,1,1] : List ℂ).length,
      clusterSequenceActualBranchMap [1,1,1,1] ω ((1/2 : ℂ) • (1 : Operator 2))) =
        (1/2 : ℂ) • (1 : Operator 2) ∧
    (∀ (r : ℕ) (ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ),
      (∑ ω : Reg ([1,1,1,1] : List ℂ).length,
        tensorLeft (clusterSequenceActualBranchMap [1,1,1,1] ω) ρ) = ρ) := by
  have hnorm : ∀ z ∈ ([1,1,1,1] : List ℂ), ‖z‖ = 1 := by simp
  have hid : clusterSequenceUnitary ([1,1,1,1] : List ℂ) = 1 := by
    simp only [clusterSequenceUnitary, Matrix.one_mul]
    rw [clusterJ_one_sq, Matrix.one_mul, clusterJ_one_sq]
  refine ⟨?_, cluster_two_identity_mixed_reference_consumer.1,
    cluster_two_identity_mixed_reference_consumer.2.1, ?_, ?_⟩
  · intro ρ ω
    rw [clusterSequenceActualBranchMap_apply [] (by simp)]
    simp [clusterSequenceUnitary]
  · rw [clusterSequenceActualBranchMap_sum _ hnorm, hid]
    simp
  · intro r ρ
    rw [(cluster_sequence_actual_reference_output _ hnorm r ρ (ZeroStr _)).2,
      hid, tensorGate_one]
    simp

end Qatlib.Concepts.InstrumentCore.PatternCompile
