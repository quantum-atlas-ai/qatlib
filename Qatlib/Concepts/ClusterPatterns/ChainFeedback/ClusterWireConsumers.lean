/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterWire

/-!
# Cluster wire examples with mixed states and references

This module evaluates two-step cluster wires on a maximally mixed input and on inputs entangled
with a reference. It specializes `clusterTwoActualBranchMap` to identity transport and to a
logical square root of Pauli-X, illustrating the wire and rotation constructions of
[RaussendorfBriegel2000].

## Main statements

* `cluster_two_identity_mixed_reference_consumer`: The phase-one wire preserves the maximally
  mixed state and every joint operator after summing branches.
* `cluster_square_root_x_actual_consumer`: The phases one and the imaginary unit give the
  displayed square root of Pauli-X.
* `cluster_square_root_x_bell_consumer`: The logical operation acts on one half of the
  normalized Bell input and changes its joint density operator.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.ClusterPatterns.ChainFeedback

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option linter.unusedSectionVars false

/-- The complex number one has norm one. -/
theorem clusterOne_norm : ‖(1 : ℂ)‖ = 1 := by simp

/-- The imaginary unit has norm one. -/
theorem clusterI_norm : ‖Complex.I‖ = 1 := by simp

/-- The phase matrix at parameter one is the identity. -/
theorem clusterPhase_one : clusterPhase 1 = 1 := by
  unfold clusterPhase
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The logical gate `clusterJ 1` is the Hadamard matrix in integer-indexed qubit coordinates. -/
theorem clusterJ_one : clusterJ 1 = relabelGate boolEquivFin2 Hadamard := by
  unfold clusterJ
  rw [clusterPhase_one, Matrix.mul_one]

/-- The logical gate `clusterJ 1` squares to the identity. -/
theorem clusterJ_one_sq : clusterJ 1 * clusterJ 1 = 1 := by
  have hH2 : relabelGate boolEquivFin2 Hadamard * relabelGate boolEquivFin2 Hadamard = 1 := by
    rw [← teleportRelabelGate_mul, hadamard_mul_self, teleportRelabelGate_one]
  unfold clusterJ
  rw [clusterPhase_one, Matrix.mul_one, hH2]

/-- Conjugating a pure-state outer product by a gate tensored with the identity gives the outer
product of the transformed joint state. -/
theorem tensorGate_outerProduct_conj {D R : ℕ} (M : Operator D)
    (ψ : QState (Fin D × Fin R)) :
    TensorGate M (1 : Operator R) * outerProduct ψ * (TensorGate M (1 : Operator R))ᴴ
      = outerProduct (ApplyGate (TensorGate M (1 : Operator R)) ψ) := by
  have h1 : outerProduct ψ = matOuter ψ ψ := rfl
  rw [h1, matOuter_sandwich]
  rfl

/-- The maximally mixed qubit state is a density operator and is not pure. Summing the two-step
branches at phases one preserves it and preserves every joint operator with a finite
reference; see [RaussendorfBriegel2000]. -/
theorem cluster_two_identity_mixed_reference_consumer :
    IsDensityOperator ((1/2 : ℂ) • (1 : Operator 2)) ∧
      ¬ IsPureDensityOperator ((1/2 : ℂ) • (1 : Operator 2)) ∧
      (∑ o : Bool × Bool, clusterTwoActualBranchMap 1 1 o.1 o.2 ((1/2 : ℂ) • (1 : Operator 2))) =
        (1/2 : ℂ) • (1 : Operator 2) ∧
      (∀ r : ℕ, ∀ ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ,
        (∑ o : Bool × Bool, tensorLeft (clusterTwoActualBranchMap 1 1 o.1 o.2) ρ) = ρ) := by
  have hone : (1 : Operator 2).PosSemidef := Matrix.PosSemidef.one
  refine ⟨⟨Matrix.PosSemidef.smul hone (by simp), ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num
  · intro ⟨⟨_, _⟩, hmul⟩
    have h00 := congrArg (fun M : Operator 2 => M 0 0) hmul
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Fin.sum_univ_two] at h00
    norm_num at h00
  · rw [Finset.sum_congr rfl (fun o _ => clusterTwoActualBranchMap_apply 1 1 o.1 o.2 _),
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4 : ℂ)) = 1 from by norm_num, one_smul,
      clusterJ_one_sq,
      show conjBranch (1 : Operator 2) ((1/2 : ℂ) • (1 : Operator 2))
        = (1/2 : ℂ) • (1 : Operator 2) from by
        rw [conjBranch_apply, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]]
  · intro r ρ
    have h := (cluster_two_actual_reference_output 1 1 clusterOne_norm clusterOne_norm r ρ
      false false).2
    have hT1 : TensorGate (1 : Operator 2) (1 : Operator r) = 1 := tensorGate_one
    rw [h, clusterJ_one_sq, hT1, Matrix.one_mul, conjTranspose_one, Matrix.mul_one]

/-- The square of `1 + Complex.I` is `2 * Complex.I`. -/
theorem complex_addI_sq : (1 + Complex.I) * (1 + Complex.I) = 2 * Complex.I := by
  rw [show (1 + Complex.I) * (1 + Complex.I)
      = 1 + Complex.I * 2 + Complex.I * Complex.I from by ring, Complex.I_mul_I]
  ring

/-- The square of `1 - Complex.I` is `-2 * Complex.I`. -/
theorem complex_subI_sq : (1 - Complex.I) * (1 - Complex.I) = -2 * Complex.I := by
  rw [show (1 - Complex.I) * (1 - Complex.I)
      = 1 - Complex.I * 2 + Complex.I * Complex.I from by ring, Complex.I_mul_I]
  ring

/-- The product of `1 + Complex.I` and `1 - Complex.I` is two. -/
theorem complex_addI_mul_subI : (1 + Complex.I) * (1 - Complex.I) = 2 := by
  rw [show (1 + Complex.I) * (1 - Complex.I)
      = 1 - Complex.I * Complex.I from by ring, Complex.I_mul_I]
  ring

/-- The two-step logical gate at phases one and the imaginary unit has the displayed matrix with
diagonal entries `(1 + Complex.I) / 2`. -/
theorem clusterJ_I_mul_one : clusterJ Complex.I * clusterJ 1
      = (1/2 : ℂ) • !![1+Complex.I, 1-Complex.I; 1-Complex.I, 1+Complex.I] := by
  ext c i
  fin_cases c <;> fin_cases i <;>
    simp [clusterJ_mul_entry 1 Complex.I, boolEquivFin2, Matrix.smul_apply, smul_eq_mul] <;>
    ring

/-- The two-step logical gate at phases one and the imaginary unit squares to Pauli-X, and its
branch sum sends the zero basis state to the displayed density matrix; see
[RaussendorfBriegel2000]. -/
theorem cluster_square_root_x_actual_consumer :
    clusterJ Complex.I * clusterJ 1
      = (1/2 : ℂ) • !![1+Complex.I, 1-Complex.I; 1-Complex.I, 1+Complex.I] ∧
      (clusterJ Complex.I * clusterJ 1)^2 = pauliXChoice true ∧
      (∑ o : Bool × Bool,
          clusterTwoActualBranchMap 1 Complex.I o.1 o.2 (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)))) =
        !![1/2, Complex.I/2; -Complex.I/2, 1/2] := by
  refine ⟨clusterJ_I_mul_one, ?_, ?_⟩
  · rw [clusterJ_I_mul_one, pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show (1/2 : ℂ) * (1/2 : ℂ) = 1/4 from by norm_num]
    ext c i
    fin_cases c <;> fin_cases i <;>
      simp [Matrix.smul_apply, smul_eq_mul, pauliXChoice, PauliX, permMatrix, relabelGate,
        Matrix.reindex_apply, Matrix.submatrix_apply, boolEquivFin2, complex_addI_sq,
        complex_subI_sq, complex_addI_mul_subI] <;>
      (ring_nf; norm_num)
  · rw [Finset.sum_congr rfl (fun o _ => clusterTwoActualBranchMap_apply 1 Complex.I o.1 o.2 _),
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4 : ℂ)) = 1 from by norm_num, one_smul,
      conjBranch_outerProduct, clusterJ_I_mul_one]
    ext c i
    fin_cases c <;> fin_cases i <;>
      simp [outerProduct_apply, dotProduct, Qatlib.Foundations.PureStateMath.Ket, smul_eq_mul,
          Complex.conj_ofNat] <;>
      (ring_nf; norm_num)

/-- The Bell input state on a qubit and a qubit reference. -/
noncomputable def clusterWireBellInput : QState (Fin 2 × Fin 2) :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℂ)⁻¹) else 0

/-- The Bell input state `clusterWireBellInput` is normalized. -/
theorem clusterWireBellInput_normalized : Normalized clusterWireBellInput := by
  have h0 : ‖(((Real.sqrt 2 : ℝ)⁻¹ : ℂ))‖ ^ 2 = 1 / 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  show ∑ p : Fin 2 × Fin 2, ‖clusterWireBellInput p‖ ^ 2 = 1
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, clusterWireBellInput]
  norm_num [h0]

/-- On the normalized Bell input, the two-step branch sum is conjugation by the logical square
root of Pauli-X on the first qubit, and it changes the joint density operator; see
[RaussendorfBriegel2000]. -/
theorem cluster_square_root_x_bell_consumer :
    Normalized clusterWireBellInput ∧
      (∑ o : Bool × Bool,
          tensorLeft (clusterTwoActualBranchMap 1 Complex.I o.1 o.2)
            (outerProduct clusterWireBellInput)) =
        outerProduct (ApplyGate (TensorGate (clusterJ Complex.I * clusterJ 1) (1 : Operator 2))
          clusterWireBellInput) ∧
      (∑ o : Bool × Bool,
          tensorLeft (clusterTwoActualBranchMap 1 Complex.I o.1 o.2)
            (outerProduct clusterWireBellInput)) ≠
        outerProduct clusterWireBellInput := by
  refine ⟨clusterWireBellInput_normalized, ?_, ?_⟩
  · have h := (cluster_two_actual_reference_output 1 Complex.I clusterOne_norm clusterI_norm 2
      (outerProduct clusterWireBellInput) false false).2
    rw [h, tensorGate_outerProduct_conj]
  · intro hcontra
    have h := (cluster_two_actual_reference_output 1 Complex.I clusterOne_norm clusterI_norm 2
      (outerProduct clusterWireBellInput) false false).2
    rw [h, tensorGate_outerProduct_conj] at hcontra
    have hval : ApplyGate (TensorGate (clusterJ Complex.I * clusterJ 1) (1 : Operator 2))
        clusterWireBellInput (0, 1) = (1 - Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) / 2 := by
      rw [clusterJ_I_mul_one]
      simp [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        tensorGate_apply, Matrix.one_apply, clusterWireBellInput, smul_eq_mul]
      ring
    have e := congrFun (congrFun hcontra (0, 1)) (0, 1)
    rw [outerProduct_apply, outerProduct_apply, hval] at e
    rw [clusterWireBellInput] at e
    have hconj : (starRingEnd ℂ) ((1 - Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) / 2)
        = (1 + Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) / 2 := by
      norm_num [Complex.conj_ofNat, Complex.conj_natCast, Complex.conj_ofReal, map_mul,
        map_sub, map_div₀, map_inv₀, Complex.conj_I]
    have habs : ((1 - Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) / 2)
        * ((1 + Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) / 2) = 1 / 4 := by
      rw [show ((1 - Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) / 2)
            * ((1 + Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) / 2)
          = ((1 - Complex.I) * (1 + Complex.I))
              * (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) / 4 from by ring,
        sqrt2_inv_sq, mul_comm (1 - Complex.I) (1 + Complex.I), complex_addI_mul_subI]
      norm_num
    rw [hconj, habs] at e
    norm_num [Complex.conj_ofNat, Complex.conj_natCast] at e

end Qatlib.Concepts.ClusterPatterns.ChainFeedback
