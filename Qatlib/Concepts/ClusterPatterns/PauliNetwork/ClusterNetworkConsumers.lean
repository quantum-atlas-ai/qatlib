/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.PauliNetwork.CountedClusterNetwork

/-!
# A Bell-state consumer of cluster networks

This module gives an explicit two-qubit cluster-network word that prepares the Bell state `(Ket
0 + Ket 3) / sqrt(2)` from `Ket 0`. Entry formulas and intermediate state calculations connect
its logical matrix to the channel obtained by forgetting the history instrument's outcomes.

The construction is a concrete consumer of the measurement-based computation framework of
[RaussendorfBriegel2000], with legality, gate counts, density-operator validity, and peak wire
usage verified for this word.

## Main statements

* `networkBellWord_logicalMatrix_mulVec` computes the logical output vector.
* `networkBellVector_normalized` proves that this Bell vector has unit norm.
* `cluster_network_bell_actual_consumer` packages the Bell-state channel calculation, counts,
  and four-wire peak.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000], *Quantum computing via measurements
  only*.
-/

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

/-- The two-qubit word consisting of unit-phase wire gates on wires 0 and 1, a CZ gate between
them, and a final unit-phase wire gate on wire 1. -/
def networkBellWord : List (ClusterNetworkGate 2) :=
  [.inl (0, 1), .inl (1, 1), .inr (0, 1), .inl (1, 1)]

/-- The outer-product density matrix of the Bell vector with amplitude `1 / sqrt(2)` at basis
indices 0 and 3 and zero elsewhere. -/
noncomputable def networkBellDensity : Operator 4 :=
  outerProduct (fun i : Fin 4 => if i = 0 ∨ i = 3 then (Real.sqrt 2 : ℂ)⁻¹ else 0)

/-- For two-bit registers, the product of equality indicators over all positions except 0 is the
equality indicator at position 1. -/
theorem networkBellErase0_prod (w v : Reg 2) :
    (∏ j ∈ Finset.univ.erase (0 : Fin 2), (if w j = v j then (1 : ℂ) else 0))
      = (if w 1 = v 1 then (1 : ℂ) else 0) := by
  have hE : (Finset.univ.erase (0 : Fin 2)) = ({1} : Finset (Fin 2)) := by
    ext j
    fin_cases j <;> simp
  rw [hE, Finset.prod_singleton]

/-- For two-bit registers, the product of equality indicators over all positions except 1 is the
equality indicator at position 0. -/
theorem networkBellErase1_prod (w v : Reg 2) :
    (∏ j ∈ Finset.univ.erase (1 : Fin 2), (if w j = v j then (1 : ℂ) else 0))
      = (if w 0 = v 0 then (1 : ℂ) else 0) := by
  have hE : (Finset.univ.erase (1 : Fin 2)) = ({0} : Finset (Fin 2)) := by
    ext j
    fin_cases j <;> simp
  rw [hE, Finset.prod_singleton]

/-- Position 0 of the two-bit register corresponding to `x : Fin 4` is true exactly when the
natural-number value of `x` is at least 2. -/
theorem networkBellBitVecEquiv2_symm_pos0 (x : Fin 4) :
    ((bitVecEquiv 2).symm x) 0 = decide (2 ≤ (x : ℕ)) := by
  fin_cases x <;> rfl

/-- Position 1 of the two-bit register corresponding to `x : Fin 4` is true exactly when the
natural-number value of `x` is odd. -/
theorem networkBellBitVecEquiv2_symm_pos1 (x : Fin 4) :
    ((bitVecEquiv 2).symm x) 1 = decide ((x : ℕ) % 2 = 1) := by
  fin_cases x <;> rfl

/-- The Boolean-to-`Fin 2` equivalence maps `false` to 0. -/
theorem networkBellBoolEquivFin2_false : boolEquivFin2 false = 0 := rfl

/-- The Boolean-to-`Fin 2` equivalence maps `true` to 1. -/
theorem networkBellBoolEquivFin2_true : boolEquivFin2 true = 1 := rfl

/-- The matrix entry of a wire gate on position 0 is the corresponding `clusterJ` entry when the
position-1 bits agree, and zero otherwise, expressed through `bitVecEquiv 2`. -/
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

/-- The matrix entry of a wire gate on position 1 is the corresponding `clusterJ` entry when the
position-0 bits agree, and zero otherwise, expressed through `bitVecEquiv 2`. -/
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

/-- The two-qubit CZ matrix is diagonal in the register basis, with sign minus one exactly when
both bits are true, expressed through `bitVecEquiv 2`. -/
theorem networkBellCzGate_entry_bve (x y : Fin 4) :
    networkCzGate (0 : Fin 2) (1 : Fin 2) x y
      = (if ((bitVecEquiv 2).symm x) = ((bitVecEquiv 2).symm y)
        then (if (((bitVecEquiv 2).symm x) 0 && ((bitVecEquiv 2).symm x) 1)
              then (-1 : ℂ) else 1)
        else 0) := by
  show (relabelGate (bitVecEquiv 2) (networkCzGateB (0 : Fin 2) (1 : Fin 2))) x y = _
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, networkCzGateB,
    Matrix.diagonal_apply]

/-- The wire-0 gate entry vanishes unless the row and column indices have the same parity;
otherwise it is the `clusterJ` entry indexed by whether each index is at least 2. -/
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

/-- The wire-1 gate entry vanishes unless the row and column indices agree on whether they are
at least 2; otherwise it is the `clusterJ` entry indexed by their parity bits. -/
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

/-- The two-qubit CZ matrix has diagonal entries 1, 1, 1, and minus one, with all off-diagonal
entries zero. -/
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

/-- At phase 1, every `clusterJ` entry is `1 / sqrt(2)` except the entry with row and column
both 1, which has the opposite sign. -/
theorem networkBellClusterJ_one_entry (c i : Fin 2) :
    clusterJ (1 : ℂ) c i
      = ((Real.sqrt 2 : ℂ)⁻¹)
        * (if c = 0 then (1 : ℂ) else if i = 0 then 1 else -1) := by
  rw [clusterJ_entry]
  fin_cases c <;> fin_cases i <;> norm_num

/-- Applying the unit-phase wire-0 gate to `Ket 0` gives amplitude `1 / sqrt(2)` at basis
indices 0 and 2 and zero at the other indices. -/
theorem networkBellStep1 :
    ApplyGate (networkWireGate (0 : Fin 2) (1 : ℂ)) (Ket (0 : Fin 4))
      = (fun i : Fin 4 => if i = 0 ∨ i = 2 then (Real.sqrt 2 : ℂ)⁻¹ else 0) := by
  funext x
  fin_cases x <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, ket_apply,
      networkBellWireGate0_entry, networkBellClusterJ_one_entry]

/-- Applying the unit-phase wire-1 gate to the first intermediate vector gives amplitude `1 / 2`
at all four basis indices. -/
theorem networkBellStep2 :
    ApplyGate (networkWireGate (1 : Fin 2) (1 : ℂ))
        (fun i : Fin 4 => if i = 0 ∨ i = 2 then (Real.sqrt 2 : ℂ)⁻¹ else 0)
      = (fun _ : Fin 4 => (1 / 2 : ℂ)) := by
  funext x
  fin_cases x <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      networkBellWireGate1_entry, networkBellClusterJ_one_entry, sqrt2_inv_sq]

/-- Applying CZ to the uniform two-qubit vector changes only the amplitude at basis index 3,
from `1 / 2` to `-1 / 2`. -/
theorem networkBellStep3 :
    ApplyGate (networkCzGate (0 : Fin 2) (1 : Fin 2)) (fun _ : Fin 4 => (1 / 2 : ℂ))
      = (fun i : Fin 4 => if i = 3 then -(1 / 2 : ℂ) else 1 / 2) := by
  funext x
  fin_cases x <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, networkBellCzGate_entry]

/-- Applying the final unit-phase wire-1 gate to the signed uniform vector gives the Bell vector
supported at basis indices 0 and 3 with amplitude `1 / sqrt(2)`. -/
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

/-- The logical matrix of `networkBellWord` sends `Ket 0` to the Bell vector with equal
amplitude `1 / sqrt(2)` at basis indices 0 and 3. -/
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

/-- The Bell vector with amplitude `1 / sqrt(2)` at basis indices 0 and 3 and zero elsewhere is
normalized. -/
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

/-- The explicit Bell word is legal: its wire phases have unit norm and its CZ endpoints are
distinct. -/
theorem networkBellWord_legal : networkLegal networkBellWord := by
  intro g hg
  simp only [networkBellWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact norm_one
  · exact norm_one
  · decide
  · exact norm_one

/-- The Bell word contains three wire gates and one CZ gate. -/
theorem networkBellWord_counts : networkCounts networkBellWord = (3, 1) := by
  simp [networkBellWord, networkCounts]

/-- The maximum entry of the Bell word's wire-occupancy trace is four. -/
theorem networkBellWord_trace_peak : (networkWireTrace networkBellWord).foldl max 0 = 4 := by
  have h := networkWireTrace_peak networkBellWord
  rw [if_neg (by simp [networkBellWord])] at h
  exact h

/-- The Bell word is legal, has three wire gates and one CZ gate, and its history instrument
sends the density of `Ket 0` to the Bell-state density after forgetting outcomes, with peak
four wires. This packages density-operator validity and the explicit consumer calculation in
the measurement-based setting of [RaussendorfBriegel2000]. -/
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
