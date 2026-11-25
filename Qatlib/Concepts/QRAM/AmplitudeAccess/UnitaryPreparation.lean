/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.ControlledSplit
public import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Qatlib.Foundations.PureStateMath.Tensor

@[expose] public section

/-!
# Exact unitary preparation from a cached mass tree

The preparation of [KerenidisPrakash2017], Appendix A, and
[ChenXueChenEtAl2022], Appendix E, rotates the next bit and uses it to
select the rest of the preparation coherently. Full preparation applies
a final sign phase at each leaf. Prefix preparation stops at the selected
depth. Zero-mass children
receive zero amplitude from a positive-mass parent. The gates use exact
cached real masses and phases.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.AmplitudeAccess

open Matrix
open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.BlockEncoding.EncodingCore (relabelGate_mem_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators

/-- A block-diagonal operation acts separately on every slice of its control register. -/
theorem applyGate_blockDiagFirst_slice {C I : Type} [Fintype C] [Fintype I]
    (blocks : C → Matrix I I ℂ) (ψ : QState (C × I)) (c : C) (i : I) :
    ApplyGate (blockDiagFirst blocks) ψ (c, i) = ApplyGate (blocks c) (fun k => ψ (c, k)) i := by
  classical
  simp only [ApplyGate, Matrix.mulVec, dotProduct, blockDiagFirst, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Address concatenation with the root's selected bit first. -/
def headAddressEquiv (levels : ℕ) : Bool × Address levels ≃ Address (levels + 1) :=
  Fin.consEquiv (fun _ => Bool)

/-- The relabeled product of two clean registers is the clean full address. -/
private theorem clean_head_address (levels : ℕ) :
    relabelState (headAddressEquiv levels) (TensorState (Ket false) (Ket (ZeroStr levels))) =
      Ket (ZeroStr (levels + 1)) := by
  have hClean : headAddressEquiv levels (false, ZeroStr levels) = ZeroStr (levels + 1) := by
    apply (headAddressEquiv levels).symm.injective
    exact ((headAddressEquiv levels).symm_apply_apply _).trans rfl
  rw [tensorState_ket_ket, ← hClean]
  funext a
  simp [relabelState, Ket, Equiv.symm_apply_eq]

/-- Rotate the root bit, then coherently execute its selected suffix preparation. -/
def splitThenPrepare {depth slots : ℕ} (tree : Tree ℝ (depth + 1))
    (suffix : Bool → Matrix (Address slots) (Address slots) ℂ) :
    Matrix (Address (slots + 1)) (Address (slots + 1)) ℂ :=
  relabelGate (headAddressEquiv slots) (blockDiagFirst suffix * TensorGate (branchGate tree) 1)

/-- Combining a valid mass split and unitary suffix preparations gives a unitary. -/
theorem split_then_prepare_unitary {depth slots : ℕ} (tree : Tree ℝ (depth + 1)) (h : Valid tree)
    (suffix : Bool → Matrix (Address slots) (Address slots) ℂ)
    (hs : ∀ bit, suffix bit ∈ Matrix.unitaryGroup (Address slots) ℂ) :
    splitThenPrepare tree suffix ∈ Matrix.unitaryGroup (Address (slots + 1)) ℂ :=
  relabelGate_mem_unitary ((Matrix.unitaryGroup (Bool × Address slots) ℂ).mul_mem
    (blockDiagFirst_unitary suffix hs)
    (tensorGate_unitary (branch_gate_unitary tree h) (Matrix.unitaryGroup (Address slots) ℂ).one_mem)) _

/-- The clean-register amplitude is the first-bit rotation amplitude times the selected
suffix amplitude. -/
theorem split_then_prepare_apply {depth slots : ℕ} (tree : Tree ℝ (depth + 1))
    (hPos : 0 < mass tree) (suffix : Bool → Matrix (Address slots) (Address slots) ℂ)
    (address : Address (slots + 1)) :
    ApplyGate (splitThenPrepare tree suffix) (Ket (ZeroStr (slots + 1))) address =
      (branchAmplitude tree (address 0) : ℂ) *
        ApplyGate (suffix (address 0)) (Ket (ZeroStr slots)) (Fin.tail address) := by
  rw [splitThenPrepare, ← clean_head_address slots, applyGate_relabelGate]
  change ApplyGate (blockDiagFirst suffix * TensorGate (branchGate tree) 1)
    (TensorState (Ket false) (Ket (ZeroStr slots))) (address 0, Fin.tail address) = _
  rw [applyGate_mul, applyGate_tensorGate, applyGate_one, applyGate_blockDiagFirst_slice]
  have hHead : ApplyGate (branchGate tree) (Ket false) (address 0) = (branchAmplitude tree (address 0) : ℂ) := by
    rw [branch_gate_ket_false tree hPos]
    cases address 0 <;> simp [Ket]
  have hSlice : (fun k => TensorState (ApplyGate (branchGate tree) (Ket false)) (Ket (ZeroStr slots))
      (address 0, k)) = (branchAmplitude tree (address 0) : ℂ) • Ket (ZeroStr slots) := by
    funext k
    simp only [TensorState, hHead, Pi.smul_apply, smul_eq_mul]
  rw [hSlice]
  simp only [ApplyGate, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

/-- A nonpositive child of a valid tree has zero branch amplitude. -/
private theorem branch_amplitude_zero {depth : ℕ} (tree : Tree ℝ (depth + 1))
    (h : Valid tree) (bit : Bool) (hZero : ¬ 0 < mass (child tree bit)) : branchAmplitude tree bit = 0 := by
  have hm : mass (child tree bit) = 0 :=
    le_antisymm (le_of_not_gt hZero) (mass_nonneg _ (valid_child tree bit h))
  simp [branchAmplitude, hm]

/-- Prepare the requested prefix using the cached masses at its successive levels. -/
def prefixPreparation {remaining : ℕ} : (levels : ℕ) → Tree ℝ (remaining + levels) →
    Matrix (Address levels) (Address levels) ℂ
  | 0, _ => 1
  | levels + 1, tree => splitThenPrepare tree (fun bit => prefixPreparation levels (child tree bit))

/-- Prefix preparation is unitary on every valid tree. -/
theorem prefix_preparation_unitary {remaining : ℕ} (levels : ℕ) (tree : Tree ℝ (remaining + levels))
    (h : Valid tree) : prefixPreparation levels tree ∈ Matrix.unitaryGroup (Address levels) ℂ := by
  induction levels with
  | zero => exact (Matrix.unitaryGroup (Address 0) ℂ).one_mem
  | succ levels ih =>
    exact split_then_prepare_unitary tree h _ (fun bit => ih _ (valid_child tree bit h))

/-- The prefix preparation realizes the cached subtree square-root amplitudes. -/
theorem prefix_preparation_apply {remaining : ℕ} (levels : ℕ) (tree : Tree ℝ (remaining + levels))
    (h : Valid tree) (hPos : 0 < mass tree) (address : Address levels) :
    ApplyGate (prefixPreparation levels tree) (Ket (ZeroStr levels)) address =
      (prefixAmplitude levels tree address : ℂ) := by
  induction levels with
  | zero =>
    have ha : address = ZeroStr 0 := Subsingleton.elim _ _
    simp [prefixPreparation, prefixAmplitude, Ket, ha]
  | succ levels ih =>
    rw [prefixPreparation, split_then_prepare_apply tree hPos]
    by_cases hc : 0 < mass (child tree (address 0))
    · rw [ih _ (valid_child tree (address 0) h) hc]
      simp only [prefixAmplitude, Complex.ofReal_mul]
    · simp [prefixAmplitude, branch_amplitude_zero tree h (address 0) hc]

/-- Restore the sign of a terminal entry by a unit-modulus phase. -/
def signedLeafPhase (tree : Tree ℝ 0) : ℂ := if leafEntry tree < 0 then -1 else 1

/-- Prepare the signed normalized entries of a cached tree. -/
def signedTreePreparation : {depth : ℕ} → Tree ℝ depth → Matrix (Address depth) (Address depth) ℂ
  | 0, tree => Matrix.diagonal (fun _ => signedLeafPhase tree)
  | _ + 1, tree => splitThenPrepare tree (fun bit => signedTreePreparation (child tree bit))

/-- The signed preparation is unitary, including trees whose root mass is zero. -/
theorem signed_tree_preparation_unitary {depth : ℕ} (tree : Tree ℝ depth) (h : Valid tree) :
    signedTreePreparation tree ∈ Matrix.unitaryGroup (Address depth) ℂ := by
  induction depth with
  | zero =>
    rw [signedTreePreparation]
    apply diagonal_mem_unitaryGroup
    intro _
    by_cases ht : leafEntry tree < 0 <;> simp [signedLeafPhase, ht]
  | succ depth ih =>
    exact split_then_prepare_unitary tree h _ (fun bit => ih _ (valid_child tree bit h))

/-- On a nonzero leaf the terminal phase gives the normalized signed entry. -/
private theorem signed_leaf_phase_eq_path (tree : Tree ℝ 0) (hPos : 0 < mass tree) (address : Address 0) :
    signedLeafPhase tree = (pathAmplitude tree address : ℂ) := by
  simp only [pathAmplitude, Qatlib.Foundations.QramData.SquaredNormTree.read, mass_eq_leaf,
    Real.sqrt_sq_eq_abs, signedLeafPhase]
  have hn : leafEntry tree ≠ 0 := by
    intro he
    simp [mass_eq_leaf, he] at hPos
  by_cases ht : leafEntry tree < 0
  · rw [ite_eq_left ht, abs_of_neg ht, div_neg, div_self hn, Complex.ofReal_neg, Complex.ofReal_one]
  · rw [ite_eq_right ht, abs_of_nonneg (le_of_not_gt ht), div_self hn, Complex.ofReal_one]

/-- The circuit applied to a clean address realizes the signed path amplitudes. -/
theorem signed_tree_preparation_apply {depth : ℕ} (tree : Tree ℝ depth) (h : Valid tree)
    (hPos : 0 < mass tree) (address : Address depth) :
    ApplyGate (signedTreePreparation tree) (Ket (ZeroStr depth)) address = (pathAmplitude tree address : ℂ) := by
  induction depth with
  | zero =>
    have ha : address = ZeroStr 0 := Subsingleton.elim _ _
    rw [signedTreePreparation, applyGate_diagonal]
    simp [Ket, ha]
    exact signed_leaf_phase_eq_path tree hPos (ZeroStr 0)
  | succ depth ih =>
    rw [signedTreePreparation, split_then_prepare_apply tree hPos]
    by_cases hc : 0 < mass (child tree (address 0))
    · rw [ih _ (valid_child tree (address 0) h) hc]
      simp only [pathAmplitude, Complex.ofReal_mul]
    · simp [pathAmplitude, branch_amplitude_zero tree h (address 0) hc]

/-- The signed preparation gives the normalized real entries of the tree as quantum amplitudes. -/
theorem signed_tree_preparation_entries {depth : ℕ} (tree : Tree ℝ depth) (h : Valid tree)
    (hPos : 0 < mass tree) (address : Address depth) :
    ApplyGate (signedTreePreparation tree) (Ket (ZeroStr depth)) address =
      (read tree address / Real.sqrt (mass tree) : ℝ) := by
  rw [signed_tree_preparation_apply tree h hPos, path_amplitude_eq tree h]

end Qatlib.Concepts.QRAM.AmplitudeAccess
