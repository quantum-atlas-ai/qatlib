/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterWire
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

theorem clusterOne_norm : ‖(1 : ℂ)‖ = 1 := by simp

theorem clusterI_norm : ‖Complex.I‖ = 1 := by simp

theorem clusterPhase_one : clusterPhase 1 = 1 := by
  unfold clusterPhase
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem clusterJ_one : clusterJ 1 = relabelGate boolEquivFin2 Hadamard := by
  unfold clusterJ
  rw [clusterPhase_one, Matrix.mul_one]

theorem clusterJ_one_sq : clusterJ 1 * clusterJ 1 = 1 := by
  have hH2 : relabelGate boolEquivFin2 Hadamard * relabelGate boolEquivFin2 Hadamard = 1 := by
    rw [← teleportRelabelGate_mul, hadamard_mul_self, teleportRelabelGate_one]
  unfold clusterJ
  rw [clusterPhase_one, Matrix.mul_one, hH2]

theorem tensorGate_outerProduct_conj {D R : ℕ} (M : Operator D)
    (ψ : QState (Fin D × Fin R)) :
    TensorGate M (1 : Operator R) * outerProduct ψ * (TensorGate M (1 : Operator R))ᴴ
      = outerProduct (ApplyGate (TensorGate M (1 : Operator R)) ψ) := by
  have h1 : outerProduct ψ = matOuter ψ ψ := rfl
  rw [h1, matOuter_sandwich]
  rfl

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

theorem complex_addI_sq : (1 + Complex.I) * (1 + Complex.I) = 2 * Complex.I := by
  rw [show (1 + Complex.I) * (1 + Complex.I)
      = 1 + Complex.I * 2 + Complex.I * Complex.I from by ring, Complex.I_mul_I]
  ring

theorem complex_subI_sq : (1 - Complex.I) * (1 - Complex.I) = -2 * Complex.I := by
  rw [show (1 - Complex.I) * (1 - Complex.I)
      = 1 - Complex.I * 2 + Complex.I * Complex.I from by ring, Complex.I_mul_I]
  ring

theorem complex_addI_mul_subI : (1 + Complex.I) * (1 - Complex.I) = 2 := by
  rw [show (1 + Complex.I) * (1 - Complex.I)
      = 1 - Complex.I * Complex.I from by ring, Complex.I_mul_I]
  ring

theorem clusterJ_I_mul_one : clusterJ Complex.I * clusterJ 1
      = (1/2 : ℂ) • !![1+Complex.I, 1-Complex.I; 1-Complex.I, 1+Complex.I] := by
  ext c i
  fin_cases c <;> fin_cases i <;>
    simp [clusterJ_mul_entry 1 Complex.I, boolEquivFin2, Matrix.smul_apply, smul_eq_mul] <;>
    ring

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

noncomputable def clusterWireBellInput : QState (Fin 2 × Fin 2) :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℂ)⁻¹) else 0

theorem clusterWireBellInput_normalized : Normalized clusterWireBellInput := by
  have h0 : ‖(((Real.sqrt 2 : ℝ)⁻¹ : ℂ))‖ ^ 2 = 1 / 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  show ∑ p : Fin 2 × Fin 2, ‖clusterWireBellInput p‖ ^ 2 = 1
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, clusterWireBellInput]
  norm_num [h0]

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
