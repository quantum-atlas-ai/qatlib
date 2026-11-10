/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.PauliNetwork.CountedClusterNetwork
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ClusterPatterns.WireComposition

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.PauliNetwork

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder
open scoped Classical

set_option linter.unusedSectionVars false
set_option autoImplicit false

def networkBellWord : List (ClusterNetworkGate 2) :=
  [.inl (0, 1), .inl (1, 1), .inr (0, 1), .inl (1, 1)]

noncomputable def networkBellDensity : Operator 4 :=
  outerProduct (fun i : Fin 4 => if i = 0 ∨ i = 3 then (Real.sqrt 2 : ℂ)⁻¹ else 0)

theorem networkBellErase0_prod (w v : Reg 2) :
    (∏ j ∈ Finset.univ.erase (0 : Fin 2), (if w j = v j then (1 : ℂ) else 0))
      = (if w 1 = v 1 then (1 : ℂ) else 0) := by
  have hE : (Finset.univ.erase (0 : Fin 2)) = ({1} : Finset (Fin 2)) := by
    ext j
    fin_cases j <;> simp
  rw [hE, Finset.prod_singleton]

theorem networkBellErase1_prod (w v : Reg 2) :
    (∏ j ∈ Finset.univ.erase (1 : Fin 2), (if w j = v j then (1 : ℂ) else 0))
      = (if w 0 = v 0 then (1 : ℂ) else 0) := by
  have hE : (Finset.univ.erase (1 : Fin 2)) = ({0} : Finset (Fin 2)) := by
    ext j
    fin_cases j <;> simp
  rw [hE, Finset.prod_singleton]

theorem networkBellBitVecEquiv2_symm_pos0 (x : Fin 4) :
    ((bitVecEquiv 2).symm x) 0 = decide (2 ≤ (x : ℕ)) := by
  fin_cases x <;> rfl

theorem networkBellBitVecEquiv2_symm_pos1 (x : Fin 4) :
    ((bitVecEquiv 2).symm x) 1 = decide ((x : ℕ) % 2 = 1) := by
  fin_cases x <;> rfl

theorem networkBellBoolEquivFin2_false : boolEquivFin2 false = 0 := rfl

theorem networkBellBoolEquivFin2_true : boolEquivFin2 true = 1 := rfl

theorem networkBellWireGate0_entry_bve (ζ : ℂ) (x y : Fin 4) :
    networkWireGate (0 : Fin 2) ζ x y
      = (if ((bitVecEquiv 2).symm x) 1 = ((bitVecEquiv 2).symm y) 1
        then clusterJ ζ (boolEquivFin2 (((bitVecEquiv 2).symm x) 0))
            (boolEquivFin2 (((bitVecEquiv 2).symm y) 0))
        else 0) := by
  have h := networkWireGateB_apply 2 0 ζ ((bitVecEquiv 2).symm x) ((bitVecEquiv 2).symm y)
  rw [networkBellErase0_prod] at h
  show (relabelGate (bitVecEquiv 2) (networkWireGateB (0 : Fin 2) ζ)) x y = _
  rw [show (relabelGate (bitVecEquiv 2) (networkWireGateB (0 : Fin 2) ζ)) x y
        = networkWireGateB (0 : Fin 2) ζ ((bitVecEquiv 2).symm x) ((bitVecEquiv 2).symm y)
      from rfl,
    h]
  by_cases hc : ((bitVecEquiv 2).symm x) 1 = ((bitVecEquiv 2).symm y) 1
  · rw [if_pos hc, if_pos hc, mul_one]
  · rw [if_neg hc, if_neg hc, mul_zero]

theorem networkBellWireGate1_entry_bve (ζ : ℂ) (x y : Fin 4) :
    networkWireGate (1 : Fin 2) ζ x y
      = (if ((bitVecEquiv 2).symm x) 0 = ((bitVecEquiv 2).symm y) 0
        then clusterJ ζ (boolEquivFin2 (((bitVecEquiv 2).symm x) 1))
            (boolEquivFin2 (((bitVecEquiv 2).symm y) 1))
        else 0) := by
  have h := networkWireGateB_apply 2 1 ζ ((bitVecEquiv 2).symm x) ((bitVecEquiv 2).symm y)
  rw [networkBellErase1_prod] at h
  show (relabelGate (bitVecEquiv 2) (networkWireGateB (1 : Fin 2) ζ)) x y = _
  rw [show (relabelGate (bitVecEquiv 2) (networkWireGateB (1 : Fin 2) ζ)) x y
        = networkWireGateB (1 : Fin 2) ζ ((bitVecEquiv 2).symm x) ((bitVecEquiv 2).symm y)
      from rfl,
    h]
  by_cases hc : ((bitVecEquiv 2).symm x) 0 = ((bitVecEquiv 2).symm y) 0
  · rw [if_pos hc, if_pos hc, mul_one]
  · rw [if_neg hc, if_neg hc, mul_zero]

theorem networkBellCzGate_entry_bve (x y : Fin 4) :
    networkCzGate (0 : Fin 2) (1 : Fin 2) x y
      = (if ((bitVecEquiv 2).symm x) = ((bitVecEquiv 2).symm y)
        then (if (((bitVecEquiv 2).symm x) 0 && ((bitVecEquiv 2).symm x) 1)
              then (-1 : ℂ) else 1)
        else 0) := by
  show (relabelGate (bitVecEquiv 2) (networkCzGateB (0 : Fin 2) (1 : Fin 2))) x y = _
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, networkCzGateB,
    Matrix.diagonal_apply]

theorem networkBellWireGate0_entry (ζ : ℂ) (x y : Fin 4) :
    networkWireGate (0 : Fin 2) ζ x y
      = (if (x : ℕ) % 2 = (y : ℕ) % 2
        then clusterJ ζ (if 2 ≤ (x : ℕ) then (1 : Fin 2) else 0)
            (if 2 ≤ (y : ℕ) then (1 : Fin 2) else 0)
        else 0) := by
  rw [networkBellWireGate0_entry_bve ζ x y,
    networkBellBitVecEquiv2_symm_pos1 x, networkBellBitVecEquiv2_symm_pos1 y,
    networkBellBitVecEquiv2_symm_pos0 x, networkBellBitVecEquiv2_symm_pos0 y]
  fin_cases x <;> fin_cases y <;>
    simp [networkBellBoolEquivFin2_false, networkBellBoolEquivFin2_true]

theorem networkBellWireGate1_entry (ζ : ℂ) (x y : Fin 4) :
    networkWireGate (1 : Fin 2) ζ x y
      = (if decide (2 ≤ (x : ℕ)) = decide (2 ≤ (y : ℕ))
        then clusterJ ζ (if (x : ℕ) % 2 = 1 then (1 : Fin 2) else 0)
            (if (y : ℕ) % 2 = 1 then (1 : Fin 2) else 0)
        else 0) := by
  rw [networkBellWireGate1_entry_bve ζ x y,
    networkBellBitVecEquiv2_symm_pos0 x, networkBellBitVecEquiv2_symm_pos0 y,
    networkBellBitVecEquiv2_symm_pos1 x, networkBellBitVecEquiv2_symm_pos1 y]
  fin_cases x <;> fin_cases y <;>
    simp [networkBellBoolEquivFin2_false, networkBellBoolEquivFin2_true]

theorem networkBellCzGate_entry (x y : Fin 4) :
    networkCzGate (0 : Fin 2) (1 : Fin 2) x y
      = (if x = y then (if (x : ℕ) = 3 then (-1 : ℂ) else 1) else 0) := by
  rw [networkBellCzGate_entry_bve]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, networkBellBitVecEquiv2_symm_pos0,
      networkBellBitVecEquiv2_symm_pos1]
    fin_cases x <;> simp
  · rw [if_neg hxy, if_neg (fun he => hxy ((bitVecEquiv 2).symm.injective he))]

theorem networkBellClusterJ_one_entry (c i : Fin 2) :
    clusterJ (1 : ℂ) c i
      = ((Real.sqrt 2 : ℂ)⁻¹)
        * (if c = 0 then (1 : ℂ) else if i = 0 then 1 else -1) := by
  rw [clusterJ_entry]
  fin_cases c <;> fin_cases i <;> norm_num

theorem networkBellStep1 :
    ApplyGate (networkWireGate (0 : Fin 2) (1 : ℂ)) (Ket (0 : Fin 4))
      = (fun i : Fin 4 => if i = 0 ∨ i = 2 then (Real.sqrt 2 : ℂ)⁻¹ else 0) := by
  funext x
  fin_cases x <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, ket_apply,
      networkBellWireGate0_entry, networkBellClusterJ_one_entry]

theorem networkBellStep2 :
    ApplyGate (networkWireGate (1 : Fin 2) (1 : ℂ))
        (fun i : Fin 4 => if i = 0 ∨ i = 2 then (Real.sqrt 2 : ℂ)⁻¹ else 0)
      = (fun _ : Fin 4 => (1 / 2 : ℂ)) := by
  funext x
  fin_cases x <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      networkBellWireGate1_entry, networkBellClusterJ_one_entry, sqrt2_inv_sq]

theorem networkBellStep3 :
    ApplyGate (networkCzGate (0 : Fin 2) (1 : Fin 2)) (fun _ : Fin 4 => (1 / 2 : ℂ))
      = (fun i : Fin 4 => if i = 3 then -(1 / 2 : ℂ) else 1 / 2) := by
  funext x
  fin_cases x <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, networkBellCzGate_entry]

theorem networkBellStep4 :
    ApplyGate (networkWireGate (1 : Fin 2) (1 : ℂ))
        (fun i : Fin 4 => if i = 3 then -(1 / 2 : ℂ) else 1 / 2)
      = (fun i : Fin 4 => if i = 0 ∨ i = 3 then (Real.sqrt 2 : ℂ)⁻¹ else 0) := by
  funext x
  fin_cases x <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      networkBellWireGate1_entry, networkBellClusterJ_one_entry] <;>
    norm_num <;>
    ring

theorem networkBellWord_logicalMatrix_mulVec :
    networkLogicalMatrix networkBellWord *ᵥ (Ket (0 : Fin 4))
      = (fun i : Fin 4 => if i = 0 ∨ i = 3 then (Real.sqrt 2 : ℂ)⁻¹ else 0) := by
  have hU : networkLogicalMatrix networkBellWord
      = ((networkWireGate (1 : Fin 2) (1 : ℂ) * networkCzGate (0 : Fin 2) (1 : Fin 2))
          * networkWireGate (1 : Fin 2) (1 : ℂ)) * networkWireGate (0 : Fin 2) (1 : ℂ) := by
    show (((1 : Operator 4) * networkWireGate (1 : Fin 2) (1 : ℂ))
          * networkCzGate (0 : Fin 2) (1 : Fin 2))
        * networkWireGate (1 : Fin 2) (1 : ℂ)
        * networkWireGate (0 : Fin 2) (1 : ℂ) = _
    rw [Matrix.one_mul]
  rw [hU]
  show ApplyGate (((networkWireGate (1 : Fin 2) (1 : ℂ) * networkCzGate (0 : Fin 2) (1 : Fin 2))
      * networkWireGate (1 : Fin 2) (1 : ℂ)) * networkWireGate (0 : Fin 2) (1 : ℂ))
      (Ket (0 : Fin 4)) = _
  rw [applyGate_mul, applyGate_mul, applyGate_mul, networkBellStep1, networkBellStep2,
    networkBellStep3, networkBellStep4]

theorem networkBellVector_normalized :
    Normalized (fun i : Fin 4 => if i = 0 ∨ i = 3 then (Real.sqrt 2 : ℂ)⁻¹ else 0) := by
  have hsq : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num
  unfold Normalized
  have e0 : ‖(if (0 : Fin 4) = 0 ∨ (0 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2
      = 1 / 2 := by rw [if_pos (Or.inl rfl), hsq]
  have e1 : ‖(if (1 : Fin 4) = 0 ∨ (1 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2
      = 0 := by
    rw [if_neg (by decide : ¬((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 3))]
    norm_num
  have e2 : ‖(if (2 : Fin 4) = 0 ∨ (2 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2
      = 0 := by
    rw [if_neg (by decide : ¬((2 : Fin 4) = 0 ∨ (2 : Fin 4) = 3))]
    norm_num
  have e3 : ‖(if (3 : Fin 4) = 0 ∨ (3 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2
      = 1 / 2 := by rw [if_pos (Or.inr rfl), hsq]
  show (∑ i : Fin 4,
      ‖(if i = 0 ∨ i = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2) = 1
  rw [Fin.sum_univ_four]
  show ‖(if (0 : Fin 4) = 0 ∨ (0 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2
      + ‖(if (1 : Fin 4) = 0 ∨ (1 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2
      + ‖(if (2 : Fin 4) = 0 ∨ (2 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2
      + ‖(if (3 : Fin 4) = 0 ∨ (3 : Fin 4) = 3 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)‖ ^ 2 = 1
  rw [e0, e1, e2, e3]
  norm_num

theorem networkBellWord_legal : networkLegal networkBellWord := by
  intro g hg
  simp only [networkBellWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact norm_one
  · exact norm_one
  · decide
  · exact norm_one

theorem networkBellWord_counts : networkCounts networkBellWord = (3, 1) := by
  simp [networkBellWord, networkCounts]

theorem networkBellWord_trace_peak : (networkWireTrace networkBellWord).foldl max 0 = 4 := by
  have h := networkWireTrace_peak networkBellWord
  rw [if_neg (by simp [networkBellWord])] at h
  exact h

theorem cluster_network_bell_actual_consumer :
    networkLegal networkBellWord ∧
    networkCounts networkBellWord = (3, 1) ∧
    networkBellDensity
      = outerProduct (fun i : Fin 4 => if i = 0 ∨ i = 3 then (Real.sqrt 2 : ℂ)⁻¹ else 0) ∧
    IsDensityOperator networkBellDensity ∧
    ∀ h : networkLegal networkBellWord,
      (networkHistoryInstrument networkBellWord h).forget.map
          (outerProduct (Ket (0 : Fin 4))) = networkBellDensity ∧
      (networkWireTrace networkBellWord).foldl max 0 = 4 := by
  refine ⟨networkBellWord_legal, networkBellWord_counts, rfl,
    isDensityOperator_outerProduct networkBellVector_normalized, ?_⟩
  intro h
  refine ⟨?_, networkBellWord_trace_peak⟩
  show (networkHistoryInstrument networkBellWord h).forget.map
      (outerProduct (Ket (0 : Fin 4)))
    = outerProduct (fun i : Fin 4 => if i = 0 ∨ i = 3 then (Real.sqrt 2 : ℂ)⁻¹ else 0)
  rw [(cluster_network_forget_correct_arbitrary_input 2 networkBellWord h).2
      (outerProduct (Ket (0 : Fin 4))), conjBranch_outerProduct,
    networkBellWord_logicalMatrix_mulVec]

end Qatlib.Concepts.ClusterPatterns.PauliNetwork
