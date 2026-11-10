/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ChainFeedback.ClusterWireConsumers
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.ClusterPatterns.AdaptiveEuler

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option linter.unusedSectionVars false

theorem applyGate_smul' {I : Type*} [Fintype I] (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    U *ᵥ (c • ψ) = c • (U *ᵥ ψ) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem applyGate_add' {I : Type*} [Fintype I] (U : Matrix I I ℂ) (ψ φ : QState I) :
    ApplyGate U (ψ + φ) = ApplyGate U ψ + ApplyGate U φ := by
  funext r
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem applyGate_ket_col {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℂ) (i : J) : M *ᵥ Qatlib.Foundations.PureStateMath.Ket i = fun r => M r i := by
  funext r
  simp only [Matrix.mulVec, dotProduct, ket_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk, mul_zero]) (fun h =>
    (h (Finset.mem_univ i)).elim)]
  rw [if_pos rfl, mul_one]

theorem qstate_bool_decomp (χ : QState Bool) :
    χ = χ false • Qatlib.Foundations.PureStateMath.Ket false + χ true • Qatlib.Foundations.PureStateMath.Ket true := by
  funext r
  cases r <;> simp [Qatlib.Foundations.PureStateMath.Ket]

theorem bitVecEquiv_succ_val (n : ℕ) (x : Reg (n + 1)) :
    (bitVecEquiv (n + 1) x).val =
      (boolEquivFin2 (x (Fin.last n))).val +
        2 * (bitVecEquiv n (fun j => x (Fin.castSucc j))).val := by
  have h1 : (bitVecEquiv (n + 1) x).val =
      (finProdFinEquiv (bitVecEquiv n (fun j => x (Fin.castSucc j)),
        boolEquivFin2 (x (Fin.last n)))).val := rfl
  rw [h1]
  rfl

theorem bitVecEquiv_val_msb (n : ℕ) (x : Reg n) :
    (bitVecEquiv n x).val = ∑ j : Fin n, (boolEquivFin2 (x j)).val * 2 ^ (n - 1 - j.val) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bitVecEquiv_succ_val, Fin.sum_univ_castSucc, ih, Finset.mul_sum, add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [Fin.val_castSucc]
      have hexp : n + 1 - 1 - j.val = n - 1 - j.val + 1 := by
        have := j.isLt
        omega
      rw [hexp, pow_succ]
      ring
    · have h0 : n + 1 - 1 - n = 0 := by omega
      rw [Fin.val_last, h0]
      simp

theorem bitVecEquiv_cons_val (n : ℕ) (b : Bool) (ω : Reg n) :
    (bitVecEquiv (n + 1) (Fin.cons b ω)).val =
      (boolEquivFin2 b).val * 2 ^ n + (bitVecEquiv n ω).val := by
  rw [bitVecEquiv_val_msb, Fin.sum_univ_succ, Fin.cons_zero, bitVecEquiv_val_msb]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [Fin.cons_succ, Fin.val_succ]
    have hexp : n + 1 - 1 - (j.val + 1) = n - 1 - j.val := by omega
    rw [hexp]

noncomputable def clusterSeqOneBitB (n : ℕ) (j : Fin (n + 1)) (U : Matrix Bool Bool ℂ) :
    Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ :=
  Matrix.of fun x y => if (∀ k : Fin (n + 1), k ≠ j → x k = y k) then U (x j) (y j) else 0

noncomputable def clusterSeqCzB (n : ℕ) (j : Fin n) : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ :=
  Matrix.diagonal fun x => if x (Fin.castSucc j) && x (Fin.succ j) then (-1 : ℂ) else 1

def clusterSeqDropEquiv (n : ℕ) (j : Fin (n + 1)) : Bool × Reg n ≃ Reg (n + 1) :=
  Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j

theorem clusterSeqOneBitB_eq_tensor (n : ℕ) (j : Fin (n + 1)) (U : Matrix Bool Bool ℂ) :
    clusterSeqOneBitB n j U =
      relabelGate (clusterSeqDropEquiv n j) (TensorGate U (1 : Matrix (Reg n) (Reg n) ℂ)) := by
  ext x y
  have hentry : relabelGate (clusterSeqDropEquiv n j) (TensorGate U (1 : Matrix (Reg n) (Reg n) ℂ)) x y
      = U (x j) (y j) * (if (fun i => x (j.succAbove i)) = (fun i => y (j.succAbove i))
          then (1 : ℂ) else 0) := by
    show (TensorGate U (1 : Matrix (Reg n) (Reg n) ℂ))
        (x j, fun i => x (j.succAbove i)) (y j, fun i => y (j.succAbove i)) = _
    rw [tensorGate_apply, Matrix.one_apply]
  show (if (∀ k : Fin (n + 1), k ≠ j → x k = y k) then U (x j) (y j) else 0) = _
  rw [hentry]
  by_cases hoff : (∀ k : Fin (n + 1), k ≠ j → x k = y k)
  · rw [if_pos hoff]
    have htail : (fun i => x (j.succAbove i)) = (fun i => y (j.succAbove i)) :=
      funext fun i => hoff _ (Fin.succAbove_ne j i)
    rw [if_pos htail, mul_one]
  · rw [if_neg hoff]
    rw [Classical.not_forall] at hoff
    obtain ⟨k, hoff⟩ := hoff
    rw [Classical.not_imp] at hoff
    obtain ⟨hkj, hne⟩ := hoff
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hkj
    have htail : (fun i => x (j.succAbove i)) ≠ (fun i => y (j.succAbove i)) := by
      intro hc
      have hcon := congrFun hc i
      rw [hi] at hcon
      exact hne hcon
    rw [if_neg htail, mul_zero]

theorem clusterSeqOneBitB_unitary (n : ℕ) (j : Fin (n + 1)) {U : Matrix Bool Bool ℂ}
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    clusterSeqOneBitB n j U ∈ Matrix.unitaryGroup (Reg (n + 1)) ℂ := by
  rw [clusterSeqOneBitB_eq_tensor]
  exact (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary hU (Submonoid.one_mem _))

theorem clusterSeqCzB_unitary (n : ℕ) (j : Fin n) :
    clusterSeqCzB n j ∈ Matrix.unitaryGroup (Reg (n + 1)) ℂ := by
  unfold clusterSeqCzB
  refine diagonal_mem_unitaryGroup _ fun x => ?_
  cases x (Fin.castSucc j) <;> cases x (Fin.succ j) <;> simp

theorem clusterSeqOneBitB_one (n : ℕ) (j : Fin (n + 1)) :
    clusterSeqOneBitB n j (1 : Matrix Bool Bool ℂ) = 1 := by
  rw [clusterSeqOneBitB_eq_tensor, tensorGate_one, CircuitRelabel.relabelGate_one]

theorem clusterSeqOneBitB_mul (n : ℕ) (j : Fin (n + 1)) (U V : Matrix Bool Bool ℂ) :
    clusterSeqOneBitB n j U * clusterSeqOneBitB n j V = clusterSeqOneBitB n j (U * V) := by
  rw [clusterSeqOneBitB_eq_tensor, clusterSeqOneBitB_eq_tensor, clusterSeqOneBitB_eq_tensor,
    ← teleportRelabelGate_mul, tensorGate_mul, Matrix.one_mul]

theorem clusterSeqOneBitB_commute (n : ℕ) (j k : Fin (n + 1)) (hjk : j ≠ k)
    (U V : Matrix Bool Bool ℂ) :
    clusterSeqOneBitB n j U * clusterSeqOneBitB n k V =
      clusterSeqOneBitB n k V * clusterSeqOneBitB n j U := by
  ext x y
  simp only [clusterSeqOneBitB, Matrix.of_apply, Matrix.mul_apply]
  set z₀ : Reg (n + 1) := Function.update x j (y j)
  set z₁ : Reg (n + 1) := Function.update x k (y k)
  have hz₀_j : z₀ j = y j := Function.update_self ..
  have hz₀_k : z₀ k = x k := Function.update_of_ne hjk.symm _ x
  have hz₀_off : ∀ l : Fin (n + 1), l ≠ j → z₀ l = x l :=
    fun l hl => Function.update_of_ne hl _ x
  have hz₁_k : z₁ k = y k := Function.update_self ..
  have hz₁_j : z₁ j = x j := Function.update_of_ne hjk _ x
  have hz₁_off : ∀ l : Fin (n + 1), l ≠ k → z₁ l = x l :=
    fun l hl => Function.update_of_ne hl _ x
  set C := ∀ l : Fin (n + 1), l ≠ j → l ≠ k → x l = y l
  have hL : (∑ z : Reg (n + 1), (if (∀ l, l ≠ j → x l = z l) then U (x j) (z j) else 0) *
        (if (∀ l, l ≠ k → z l = y l) then V (z k) (y k) else 0))
      = U (x j) (y j) * (if C then V (x k) (y k) else 0) := by
    rw [Finset.sum_eq_single z₀]
    · have hoff0 : (∀ l, l ≠ j → x l = z₀ l) := fun l hl => (hz₀_off l hl).symm
      rw [if_pos hoff0, hz₀_j, hz₀_k]
      have hB : (∀ l, l ≠ k → z₀ l = y l) ↔ C := by
        constructor
        · intro h l hlj hlk
          rw [← hz₀_off l hlj]
          exact h l hlk
        · intro hC l hlk
          by_cases hlj : l = j
          · rw [hlj, hz₀_j]
          · rw [hz₀_off l hlj]
            exact hC l hlj hlk
      by_cases hC : C
      · rw [if_pos (hB.mpr hC), if_pos hC]
      · rw [if_neg (fun h => hC (hB.mp h)), if_neg hC, mul_zero]
    · intro z _ hz
      by_cases hoff : (∀ l, l ≠ j → x l = z l)
      · have hzj : z j ≠ y j := by
          intro h
          apply hz
          funext l
          by_cases hlj : l = j
          · rw [hlj, h, hz₀_j]
          · rw [hz₀_off l hlj]
            exact (hoff l hlj).symm
        have hk : j ≠ k := hjk
        have : ¬(∀ l, l ≠ k → z l = y l) := fun h => hzj (h j hk)
        rw [if_neg this, mul_zero]
      · rw [if_neg hoff, zero_mul]
    · intro h
      exact (h (Finset.mem_univ z₀)).elim
  have hR : (∑ z : Reg (n + 1), (if (∀ l, l ≠ k → x l = z l) then V (x k) (z k) else 0) *
        (if (∀ l, l ≠ j → z l = y l) then U (z j) (y j) else 0))
      = V (x k) (y k) * (if C then U (x j) (y j) else 0) := by
    rw [Finset.sum_eq_single z₁]
    · have hoff1 : (∀ l, l ≠ k → x l = z₁ l) := fun l hl => (hz₁_off l hl).symm
      rw [if_pos hoff1, hz₁_k, hz₁_j]
      have hB : (∀ l, l ≠ j → z₁ l = y l) ↔ C := by
        constructor
        · intro h l hlj hlk
          rw [← hz₁_off l hlk]
          exact h l hlj
        · intro hC l hlj
          by_cases hlk : l = k
          · rw [hlk, hz₁_k]
          · rw [hz₁_off l hlk]
            exact hC l hlj hlk
      by_cases hC : C
      · rw [if_pos (hB.mpr hC), if_pos hC]
      · rw [if_neg (fun h => hC (hB.mp h)), if_neg hC, mul_zero]
    · intro z _ hz
      by_cases hoff : (∀ l, l ≠ k → x l = z l)
      · have hzk : z k ≠ y k := by
          intro h
          apply hz
          funext l
          by_cases hlk : l = k
          · rw [hlk, h, hz₁_k]
          · rw [hz₁_off l hlk]
            exact (hoff l hlk).symm
        have hj : k ≠ j := fun h => hjk h.symm
        have : ¬(∀ l, l ≠ j → z l = y l) := fun h => hzk (h k hj)
        rw [if_neg this, mul_zero]
      · rw [if_neg hoff, zero_mul]
    · intro h
      exact (h (Finset.mem_univ z₁)).elim
  rw [hL, hR]
  by_cases hC : C
  · rw [if_pos hC, if_pos hC, mul_comm]
  · rw [if_neg hC, if_neg hC, mul_zero, mul_zero]

theorem clusterSeqDiagonal_oneBitB_commute (n : ℕ) (k : Fin (n + 1)) (d : Reg (n + 1) → ℂ)
    (hd : ∀ x y : Reg (n + 1), (∀ l : Fin (n + 1), l ≠ k → x l = y l) → d x = d y)
    (V : Matrix Bool Bool ℂ) :
    Matrix.diagonal d * clusterSeqOneBitB n k V =
      clusterSeqOneBitB n k V * Matrix.diagonal d := by
  ext x y
  simp only [clusterSeqOneBitB, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single x (fun z _ hz => by
      rw [if_neg (fun h => hz h.symm), zero_mul]) (fun h => (h (Finset.mem_univ x)).elim),
    Finset.sum_eq_single y (fun z _ hz => by
      rw [if_neg hz, mul_zero]) (fun h => (h (Finset.mem_univ y)).elim),
    if_pos rfl, if_pos rfl]
  by_cases hoff : (∀ l : Fin (n + 1), l ≠ k → x l = y l)
  · rw [if_pos hoff, hd x y hoff, mul_comm]
  · rw [if_neg hoff, mul_zero, zero_mul]

theorem clusterSeqOneBitB_diagonal (n : ℕ) (j : Fin (n + 1)) (f : Bool → ℂ) :
    clusterSeqOneBitB n j (Matrix.diagonal f) = Matrix.diagonal (fun x => f (x j)) := by
  ext x y
  simp only [clusterSeqOneBitB, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h
    rw [if_pos (fun k _ => rfl), if_pos rfl, if_pos rfl]
  · rw [if_neg h]
    by_cases hoff : (∀ k : Fin (n + 1), k ≠ j → x k = y k)
    · have hne : x j ≠ y j := by
        intro hj
        apply h
        funext l
        by_cases hlj : l = j
        · rw [hlj, hj]
        · exact hoff l hlj
      rw [if_pos hoff, if_neg hne]
    · rw [if_neg hoff]

noncomputable def clusterSeqShiftOp (m : ℕ) (W : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ) :
    Matrix (Reg (m + 2)) (Reg (m + 2)) ℂ :=
  relabelGate (Fin.consEquiv (fun _ : Fin (m + 2) => Bool)) (TensorGate (1 : Matrix Bool Bool ℂ) W)

theorem clusterSeqShiftOp_mul (m : ℕ) (A B : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ) :
    clusterSeqShiftOp m (A * B) = clusterSeqShiftOp m A * clusterSeqShiftOp m B := by
  unfold clusterSeqShiftOp
  rw [← teleportRelabelGate_mul, tensorGate_mul, Matrix.one_mul]

theorem clusterSeqShiftOp_one (m : ℕ) :
    clusterSeqShiftOp m (1 : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ) = 1 := by
  unfold clusterSeqShiftOp
  rw [tensorGate_one, CircuitRelabel.relabelGate_one]

theorem clusterSeqShiftOp_unitary (m : ℕ) {W : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Reg (m + 1)) ℂ) :
    clusterSeqShiftOp m W ∈ Matrix.unitaryGroup (Reg (m + 2)) ℂ := by
  unfold clusterSeqShiftOp
  exact (relabelGate_mem_unitaryGroup _ _).mpr
    (tensorGate_unitary (Submonoid.one_mem _) hW)

theorem clusterSeqShiftOp_entry (m : ℕ) (W : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ)
    (x y : Reg (m + 2)) :
    clusterSeqShiftOp m W x y =
      (if x 0 = y 0 then (1 : ℂ) else 0) * W (Fin.tail x) (Fin.tail y) := by
  show (TensorGate (1 : Matrix Bool Bool ℂ) W) (x 0, Fin.tail x) (y 0, Fin.tail y) = _
  rw [tensorGate_apply, Matrix.one_apply]

theorem clusterSeqOneBitB_zero_eq (m : ℕ) (U : Matrix Bool Bool ℂ) :
    clusterSeqOneBitB (m + 1) (0 : Fin (m + 2)) U =
      relabelGate (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
        (TensorGate U (1 : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ)) := by
  rw [clusterSeqOneBitB_eq_tensor]
  unfold clusterSeqDropEquiv
  rw [Fin.insertNthEquiv_zero]

theorem clusterSeqShiftOp_oneBitB (m : ℕ) (j : Fin (m + 1)) (U : Matrix Bool Bool ℂ) :
    clusterSeqShiftOp m (clusterSeqOneBitB m j U) =
      clusterSeqOneBitB (m + 1) j.succ U := by
  ext x y
  rw [clusterSeqShiftOp_entry]
  have hcond : (∀ k : Fin (m + 2), k ≠ j.succ → x k = y k) ↔
      (x 0 = y 0) ∧ (∀ k : Fin (m + 1), k ≠ j → (Fin.tail x) k = (Fin.tail y) k) := by
    constructor
    · intro h
      refine ⟨h 0 (Fin.succ_ne_zero j).symm, fun k hk => ?_⟩
      exact h k.succ (fun c => hk (Fin.succ_injective _ c))
    · intro ⟨h0, htail⟩ k hk
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
      · exact h0
      · exact htail k' (fun c => hk (by rw [c]))
  simp only [clusterSeqOneBitB, Matrix.of_apply]
  by_cases hoff : (∀ k : Fin (m + 2), k ≠ j.succ → x k = y k)
  · rw [if_pos hoff, if_pos (hcond.mp hoff).1, if_pos (hcond.mp hoff).2, one_mul]
    rfl
  · rw [if_neg hoff]
    rcases (not_and_or.mp (fun h => hoff (hcond.mpr h))) with h0 | htail
    · rw [if_neg h0, zero_mul]
    · rw [if_neg htail, mul_zero]

theorem clusterSeqOneBitB_zero_mul_shiftOp (m : ℕ) (U : Matrix Bool Bool ℂ)
    (W : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ) :
    clusterSeqOneBitB (m + 1) (0 : Fin (m + 2)) U * clusterSeqShiftOp m W =
      clusterSeqShiftOp m W * clusterSeqOneBitB (m + 1) (0 : Fin (m + 2)) U := by
  rw [clusterSeqOneBitB_zero_eq]
  unfold clusterSeqShiftOp
  rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul, tensorGate_mul, tensorGate_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

def clusterSeqBasisVec (n : ℕ) (i : Fin 2) : Reg (n + 1) :=
  fun j => if j.val = 0 then boolEquivFin2.symm i else false

theorem clusterSeqBasisVec_zero (n : ℕ) (i : Fin 2) :
    clusterSeqBasisVec n i 0 = boolEquivFin2.symm i := by
  simp [clusterSeqBasisVec]

theorem clusterSeqBasisVec_succ (n : ℕ) (i : Fin 2) (j : Fin n) :
    clusterSeqBasisVec n i j.succ = false := by
  simp [clusterSeqBasisVec, Fin.val_succ]

def clusterSeqInitialFrameB (n : ℕ) : Matrix (Reg (n + 1)) (Fin 2) ℂ :=
  Matrix.of fun x i => if x = clusterSeqBasisVec n i then 1 else 0

def clusterSequenceInitialFrame (n : ℕ) : Matrix (Fin (2 ^ (n + 1))) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if r = bitVecEquiv (n + 1) (clusterSeqBasisVec n i) then 1 else 0

theorem clusterSequenceInitialFrame_entry (n : ℕ) (r : Fin (2 ^ (n + 1))) (i : Fin 2) :
    clusterSequenceInitialFrame n r i =
      clusterSeqInitialFrameB n ((bitVecEquiv (n + 1)).symm r) i := by
  simp only [clusterSequenceInitialFrame, clusterSeqInitialFrameB, Matrix.of_apply]
  by_cases h : r = bitVecEquiv (n + 1) (clusterSeqBasisVec n i)
  · rw [if_pos h]
    have h' : (bitVecEquiv (n + 1)).symm r = clusterSeqBasisVec n i := by
      rw [h, Equiv.symm_apply_apply]
    rw [if_pos h']
  · rw [if_neg h]
    have h' : (bitVecEquiv (n + 1)).symm r ≠ clusterSeqBasisVec n i := by
      intro hc
      exact h ((Equiv.symm_apply_eq (bitVecEquiv (n + 1))).mp hc)
    rw [if_neg h']

theorem clusterSeqBasisVec_injective (n : ℕ) :
    Function.Injective (clusterSeqBasisVec n) := by
  intro i j hij
  have h0 := congrFun hij (0 : Fin (n + 1))
  rw [clusterSeqBasisVec_zero, clusterSeqBasisVec_zero] at h0
  exact boolEquivFin2.symm.injective h0

theorem clusterSeqInitialFrameB_isometry (n : ℕ) :
    IsIsometry (clusterSeqInitialFrameB n) := by
  have hInj := clusterSeqBasisVec_injective n
  have h : (clusterSeqInitialFrameB n)ᴴ * clusterSeqInitialFrameB n = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hval : ∀ r : Reg (n + 1), (clusterSeqInitialFrameB n)ᴴ i r *
          clusterSeqInitialFrameB n r i = if r = clusterSeqBasisVec n i then (1 : ℂ) else 0 := by
        intro r
        rw [conjTranspose_apply]
        simp only [clusterSeqInitialFrameB, Matrix.of_apply]
        by_cases hr : r = clusterSeqBasisVec n i
        · rw [if_pos hr]; simp
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hval r),
        Finset.sum_ite_eq' Finset.univ (clusterSeqBasisVec n i) (fun _ => (1 : ℂ)),
        if_pos (Finset.mem_univ _)]
      simp
    · have hzero : ∀ r : Reg (n + 1),
          (clusterSeqInitialFrameB n)ᴴ i r * clusterSeqInitialFrameB n r j = 0 := by
        intro r
        rw [conjTranspose_apply]
        simp only [clusterSeqInitialFrameB, Matrix.of_apply]
        by_cases hr : r = clusterSeqBasisVec n i
        · rw [if_pos hr, if_neg (fun hc => hij (hInj (hr.symm.trans hc))), mul_zero]
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hzero r), Finset.sum_const_zero]
      exact (Matrix.one_apply_ne hij).symm
  exact h

theorem clusterSequenceInitialFrame_isometry (n : ℕ) :
    IsIsometry (clusterSequenceInitialFrame n) := by
  have hInj : Function.Injective (fun i : Fin 2 => bitVecEquiv (n + 1) (clusterSeqBasisVec n i)) :=
    (bitVecEquiv (n + 1)).injective.comp (clusterSeqBasisVec_injective n)
  have h : (clusterSequenceInitialFrame n)ᴴ * clusterSequenceInitialFrame n = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hval : ∀ r : Fin (2 ^ (n + 1)), (clusterSequenceInitialFrame n)ᴴ i r *
          clusterSequenceInitialFrame n r i =
            if r = bitVecEquiv (n + 1) (clusterSeqBasisVec n i) then (1 : ℂ) else 0 := by
        intro r
        rw [conjTranspose_apply]
        simp only [clusterSequenceInitialFrame, Matrix.of_apply]
        by_cases hr : r = bitVecEquiv (n + 1) (clusterSeqBasisVec n i)
        · rw [if_pos hr]; simp
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hval r),
        Finset.sum_ite_eq' Finset.univ (bitVecEquiv (n + 1) (clusterSeqBasisVec n i))
          (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ _)]
      simp
    · have hzero : ∀ r : Fin (2 ^ (n + 1)),
          (clusterSequenceInitialFrame n)ᴴ i r * clusterSequenceInitialFrame n r j = 0 := by
        intro r
        rw [conjTranspose_apply]
        simp only [clusterSequenceInitialFrame, Matrix.of_apply]
        by_cases hr : r = bitVecEquiv (n + 1) (clusterSeqBasisVec n i)
        · rw [if_pos hr, if_neg (fun hc => hij (hInj (hr.symm.trans hc))), mul_zero]
        · rw [if_neg hr]; simp
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hzero r), Finset.sum_const_zero]
      exact (Matrix.one_apply_ne hij).symm
  exact h

theorem clusterSeqInitialFrameB_mulVec (n : ℕ) (φ : QState (Fin 2)) :
    clusterSeqInitialFrameB n *ᵥ φ =
      relabelState (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
        (TensorState (relabelState boolEquivFin2.symm φ) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))) := by
  funext x
  show (∑ i : Fin 2, clusterSeqInitialFrameB n x i * φ i) = _
  simp only [clusterSeqInitialFrameB, Matrix.of_apply]
  show (∑ i : Fin 2, (if x = clusterSeqBasisVec n i then (1 : ℂ) else 0) * φ i) =
    φ (boolEquivFin2 (x 0)) * (if Fin.tail x = ZeroStr n then 1 else 0)
  by_cases htail : Fin.tail x = ZeroStr n
  · have hx : x = clusterSeqBasisVec n (boolEquivFin2 (x 0)) := by
      funext j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [clusterSeqBasisVec_zero, Equiv.symm_apply_apply]
      · rw [clusterSeqBasisVec_succ]
        have h0 : Fin.tail x j' = false := by
          have := congrFun htail j'
          rw [show ZeroStr n j' = false from rfl] at this
          exact this
        exact h0
    rw [if_pos htail, mul_one]
    rw [Finset.sum_eq_single (boolEquivFin2 (x 0))]
    · rw [if_pos hx, one_mul]
    · intro i _ hi
      have hne : x ≠ clusterSeqBasisVec n i := by
        intro h
        apply hi
        have h0 := congrFun h (0 : Fin (n + 1))
        rw [clusterSeqBasisVec_zero] at h0
        have h1 := congrArg boolEquivFin2 h0
        rw [Equiv.apply_symm_apply] at h1
        exact h1.symm
      rw [if_neg hne, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [if_neg htail, mul_zero]
    apply Finset.sum_eq_zero
    intro i _
    have hne : x ≠ clusterSeqBasisVec n i := by
      intro h
      apply htail
      funext k
      have hk := congrFun h k.succ
      rw [clusterSeqBasisVec_succ] at hk
      exact hk
    rw [if_neg hne, zero_mul]

theorem clusterSequenceInitialFrame_mulVec (n : ℕ) (ψ : QState (Fin 2)) :
    clusterSequenceInitialFrame n *ᵥ ψ =
      relabelState (bitVecEquiv (n + 1)) (clusterSeqInitialFrameB n *ᵥ ψ) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, clusterSequenceInitialFrame_entry, relabelState,
    Function.comp_apply]

noncomputable def clusterSeqCircuitGate {I : Type*} [Fintype I] [DecidableEq I] :
    Circuit I → Matrix I I ℂ
  | [] => 1
  | Step.gate U :: C => clusterSeqCircuitGate C * U
  | Step.query :: C => clusterSeqCircuitGate C

theorem clusterSeqCircuitGate_append {I : Type*} [Fintype I] [DecidableEq I] (C D : Circuit I) :
    clusterSeqCircuitGate (C ++ D) =
      clusterSeqCircuitGate D * clusterSeqCircuitGate C := by
  induction C with
  | nil =>
    show clusterSeqCircuitGate D = clusterSeqCircuitGate D * 1
    rw [mul_one]
  | cons s C ih =>
    cases s with
    | gate U =>
      show clusterSeqCircuitGate (C ++ D) * U =
        clusterSeqCircuitGate D * (clusterSeqCircuitGate C * U)
      rw [ih, Matrix.mul_assoc]
    | query => exact ih

theorem run_clusterSeqCircuitGate {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ)
    (C : Circuit I) (hC : QueryCount C = 0) (ψ : QState I) :
    Run oracle C ψ = ApplyGate (clusterSeqCircuitGate C) ψ := by
  induction C generalizing ψ with
  | nil =>
    show ψ = ApplyGate 1 ψ
    rw [applyGate_one]
  | cons s C ih =>
    cases s with
    | gate U =>
      show Run oracle C (ApplyGate U ψ) = ApplyGate (clusterSeqCircuitGate C * U) ψ
      rw [ih hC, ← applyGate_mul]
    | query =>
      have hC' : QueryCount C + 1 = 0 := hC
      exact absurd hC' (Nat.succ_ne_zero _)

theorem clusterSeqCircuitGate_unitary {I : Type*} [Fintype I] [DecidableEq I] (C : Circuit I)
    (hC : IsUnitaryCircuit C) : clusterSeqCircuitGate C ∈ Matrix.unitaryGroup I ℂ := by
  induction C with
  | nil => exact Submonoid.one_mem _
  | cons s C ih =>
    cases s with
    | gate U =>
      show clusterSeqCircuitGate C * U ∈ Matrix.unitaryGroup I ℂ
      exact Submonoid.mul_mem _ (ih (fun V hV => hC V (List.mem_cons_of_mem _ hV)))
        (hC U List.mem_cons_self)
    | query =>
      exact ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))

theorem clusterSeqCircuitGate_relabel {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (C : Circuit I) :
    clusterSeqCircuitGate (relabelCircuit e C) = relabelGate e (clusterSeqCircuitGate C) := by
  induction C with
  | nil =>
    show (1 : Matrix J J ℂ) = relabelGate e 1
    rw [CircuitRelabel.relabelGate_one]
  | cons s C ih =>
    cases s with
    | gate U =>
      show clusterSeqCircuitGate (relabelCircuit e C) * relabelGate e U =
        relabelGate e (clusterSeqCircuitGate C * U)
      rw [ih, ← CircuitRelabel.relabelGate_mul]
    | query => exact ih

theorem clusterSeqCircuitGate_commute {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (C : Circuit I)
    (hC : ∀ U : Matrix I I ℂ, Step.gate U ∈ C → A * U = U * A) :
    A * clusterSeqCircuitGate C = clusterSeqCircuitGate C * A := by
  induction C with
  | nil =>
    show A * 1 = 1 * A
    rw [mul_one, one_mul]
  | cons s C ih =>
    cases s with
    | gate U =>
      show A * (clusterSeqCircuitGate C * U) = (clusterSeqCircuitGate C * U) * A
      rw [← Matrix.mul_assoc, ih (fun V hV => hC V (List.mem_cons_of_mem _ hV)),
        Matrix.mul_assoc, hC U List.mem_cons_self, Matrix.mul_assoc]
    | query =>
      show A * clusterSeqCircuitGate C = clusterSeqCircuitGate C * A
      exact ih (fun V hV => hC V (List.mem_cons_of_mem _ hV))

noncomputable def clusterSeqShiftStep (m : ℕ) : Step (Reg (m + 1)) → Step (Reg (m + 2))
  | Step.gate U => Step.gate (clusterSeqShiftOp m U)
  | Step.query => Step.query

noncomputable def clusterSeqShiftCircuitB (m : ℕ) (C : Circuit (Reg (m + 1))) :
    Circuit (Reg (m + 2)) :=
  C.map (clusterSeqShiftStep m)

theorem clusterSeqCircuitGate_shiftCircuitB (m : ℕ) (C : Circuit (Reg (m + 1))) :
    clusterSeqCircuitGate (clusterSeqShiftCircuitB m C) =
      clusterSeqShiftOp m (clusterSeqCircuitGate C) := by
  induction C with
  | nil =>
    show (1 : Matrix (Reg (m + 2)) (Reg (m + 2)) ℂ) = clusterSeqShiftOp m 1
    rw [clusterSeqShiftOp_one]
  | cons s C ih =>
    cases s with
    | gate U =>
      show clusterSeqCircuitGate (clusterSeqShiftCircuitB m C) * clusterSeqShiftOp m U =
        clusterSeqShiftOp m (clusterSeqCircuitGate C * U)
      rw [ih, ← clusterSeqShiftOp_mul]
    | query =>
      show clusterSeqCircuitGate (clusterSeqShiftCircuitB m C) =
        clusterSeqShiftOp m (clusterSeqCircuitGate C)
      exact ih

theorem gateCount_shiftCircuitB (m : ℕ) (C : Circuit (Reg (m + 1))) :
    GateCount (clusterSeqShiftCircuitB m C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      show GateCount (Step.gate (clusterSeqShiftOp m U) :: clusterSeqShiftCircuitB m C) =
        GateCount (Step.gate U :: C)
      rw [gateCount_gate, gateCount_gate, ih]
    | query =>
      show GateCount (Step.query :: clusterSeqShiftCircuitB m C) = GateCount (Step.query :: C)
      exact ih

theorem queryCount_shiftCircuitB (m : ℕ) (C : Circuit (Reg (m + 1))) :
    QueryCount (clusterSeqShiftCircuitB m C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      show QueryCount (Step.gate (clusterSeqShiftOp m U) :: clusterSeqShiftCircuitB m C) =
        QueryCount (Step.gate U :: C)
      rw [queryCount_gate, queryCount_gate, ih]
    | query =>
      show QueryCount (Step.query :: clusterSeqShiftCircuitB m C) = QueryCount (Step.query :: C)
      rw [queryCount_query, queryCount_query, ih]

theorem gateCount_ofFn_gate {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) (G : Fin m → Matrix I I ℂ) :
    GateCount (List.ofFn fun j => Step.gate (G j)) = m := by
  have h : ∀ L : List (Fin m), GateCount (L.map (fun j => Step.gate (G j))) = L.length := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.map_cons, gateCount_gate, ih, List.length_cons]
  rw [List.ofFn_eq_map, h, List.length_finRange]

theorem queryCount_ofFn_gate {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) (G : Fin m → Matrix I I ℂ) :
    QueryCount (List.ofFn fun j => Step.gate (G j)) = 0 := by
  have h : ∀ L : List (Fin m), QueryCount (L.map (fun j => Step.gate (G j))) = 0 := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.map_cons, queryCount_gate, ih]
  rw [List.ofFn_eq_map, h]

theorem clusterSeqShiftOp_diagonal (m : ℕ) (d : Reg (m + 1) → ℂ) :
    clusterSeqShiftOp m (Matrix.diagonal d) = Matrix.diagonal (fun x => d (Fin.tail x)) := by
  ext x y
  rw [clusterSeqShiftOp_entry, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h
    rw [if_pos rfl, if_pos rfl, one_mul, if_pos rfl]
  · rw [if_neg h]
    by_cases h0 : x 0 = y 0
    · rw [if_pos h0]
      have ht : Fin.tail x ≠ Fin.tail y := fun ht => h (by
        rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, h0, ht])
      rw [if_neg ht, mul_zero]
    · rw [if_neg h0, zero_mul]

theorem clusterSeqShiftOp_czB (m : ℕ) (j : Fin m) :
    clusterSeqShiftOp m (clusterSeqCzB m j) = clusterSeqCzB (m + 1) j.succ := by
  rw [clusterSeqCzB, clusterSeqShiftOp_diagonal, clusterSeqCzB]
  congr 1

noncomputable def clusterSeqResourceHB (n : ℕ) : Circuit (Reg (n + 1)) :=
  List.ofFn fun j : Fin n => Step.gate (clusterSeqOneBitB n j.succ Hadamard)

noncomputable def clusterSeqResourceCzB (n : ℕ) : Circuit (Reg (n + 1)) :=
  List.ofFn fun j : Fin n => Step.gate (clusterSeqCzB n j)

noncomputable def clusterSeqResourceCircuitB (n : ℕ) : Circuit (Reg (n + 1)) :=
  clusterSeqResourceHB n ++ clusterSeqResourceCzB n

theorem clusterSeqResourceHB_succ (n : ℕ) :
    clusterSeqResourceHB (n + 1) =
      Step.gate (clusterSeqOneBitB (n + 1) (0 : Fin (n + 1)).succ Hadamard) ::
        clusterSeqShiftCircuitB n (clusterSeqResourceHB n) := by
  show List.ofFn (fun j : Fin (n + 1) => Step.gate (clusterSeqOneBitB (n + 1) j.succ Hadamard)) = _
  rw [List.ofFn_succ]
  congr 1
  show List.ofFn (fun i : Fin n => Step.gate (clusterSeqOneBitB (n + 1) i.succ.succ Hadamard)) =
    (List.ofFn fun j : Fin n => Step.gate (clusterSeqOneBitB n j.succ Hadamard)).map
      (clusterSeqShiftStep n)
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext j
  show Step.gate (clusterSeqOneBitB (n + 1) j.succ.succ Hadamard) =
    Step.gate (clusterSeqShiftOp n (clusterSeqOneBitB n j.succ Hadamard))
  rw [clusterSeqShiftOp_oneBitB]

theorem clusterSeqResourceCzB_succ (n : ℕ) :
    clusterSeqResourceCzB (n + 1) =
      Step.gate (clusterSeqCzB (n + 1) (0 : Fin (n + 1))) ::
        clusterSeqShiftCircuitB n (clusterSeqResourceCzB n) := by
  show List.ofFn (fun j : Fin (n + 1) => Step.gate (clusterSeqCzB (n + 1) j)) = _
  rw [List.ofFn_succ]
  congr 1
  show List.ofFn (fun i : Fin n => Step.gate (clusterSeqCzB (n + 1) i.succ)) =
    (List.ofFn fun j : Fin n => Step.gate (clusterSeqCzB n j)).map (clusterSeqShiftStep n)
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext j
  show Step.gate (clusterSeqCzB (n + 1) j.succ) =
    Step.gate (clusterSeqShiftOp n (clusterSeqCzB n j))
  rw [clusterSeqShiftOp_czB]

theorem gateCount_resourceCircuitB (n : ℕ) :
    GateCount (clusterSeqResourceCircuitB n) = 2 * n := by
  show GateCount ((List.ofFn fun j : Fin n => Step.gate (clusterSeqOneBitB n j.succ Hadamard)) ++
    (List.ofFn fun j : Fin n => Step.gate (clusterSeqCzB n j))) = 2 * n
  rw [gateCount_append, gateCount_ofFn_gate, gateCount_ofFn_gate]
  ring

theorem queryCount_resourceCircuitB (n : ℕ) :
    QueryCount (clusterSeqResourceCircuitB n) = 0 := by
  show QueryCount ((List.ofFn fun j : Fin n => Step.gate (clusterSeqOneBitB n j.succ Hadamard)) ++
    (List.ofFn fun j : Fin n => Step.gate (clusterSeqCzB n j))) = 0
  rw [queryCount_append, queryCount_ofFn_gate, queryCount_ofFn_gate]

theorem isUnitaryCircuit_resourceCircuitB (n : ℕ) :
    IsUnitaryCircuit (clusterSeqResourceCircuitB n) := by
  intro U hU
  rw [clusterSeqResourceCircuitB, List.mem_append] at hU
  rcases hU with hU | hU
  · rw [clusterSeqResourceHB, List.mem_ofFn] at hU
    obtain ⟨j, hj⟩ := hU
    rw [Step.gate.injEq] at hj
    rw [← hj]
    exact clusterSeqOneBitB_unitary n j.succ hadamard_unitary
  · rw [clusterSeqResourceCzB, List.mem_ofFn] at hU
    obtain ⟨j, hj⟩ := hU
    rw [Step.gate.injEq] at hj
    rw [← hj]
    exact clusterSeqCzB_unitary n j

theorem isUnitaryCircuit_shiftCircuitB (m : ℕ) (C : Circuit (Reg (m + 1)))
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (clusterSeqShiftCircuitB m C) := by
  intro U hU
  rw [clusterSeqShiftCircuitB, List.mem_map] at hU
  obtain ⟨s, hs, hsg⟩ := hU
  cases s with
  | query =>
    rw [clusterSeqShiftStep] at hsg
    contradiction
  | gate V =>
    rw [clusterSeqShiftStep, Step.gate.injEq] at hsg
    rw [← hsg]
    exact clusterSeqShiftOp_unitary m (hC V hs)

noncomputable def clusterSeqResourceGateB (n : ℕ) : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ :=
  clusterSeqCircuitGate (clusterSeqResourceCircuitB n)

theorem clusterSeqResourceGateB_unitary (n : ℕ) :
    clusterSeqResourceGateB n ∈ Matrix.unitaryGroup (Reg (n + 1)) ℂ :=
  clusterSeqCircuitGate_unitary _ (isUnitaryCircuit_resourceCircuitB n)

theorem clusterSeqCzB_zero_mul_shiftHB (n : ℕ) :
    clusterSeqCzB (n + 1) (0 : Fin (n + 1)) *
        clusterSeqShiftOp n (clusterSeqCircuitGate (clusterSeqResourceHB n)) =
      clusterSeqShiftOp n (clusterSeqCircuitGate (clusterSeqResourceHB n)) *
        clusterSeqCzB (n + 1) (0 : Fin (n + 1)) := by
  rw [← clusterSeqCircuitGate_shiftCircuitB]
  apply clusterSeqCircuitGate_commute
  intro U hU
  have hU' : Step.gate U ∈ List.map (clusterSeqShiftStep n) (List.ofFn fun j : Fin n =>
      Step.gate (clusterSeqOneBitB n j.succ Hadamard)) := hU
  rw [List.mem_map] at hU'
  obtain ⟨s, hs, hsg⟩ := hU'
  have hs' : s ∈ List.ofFn fun j : Fin n =>
      Step.gate (clusterSeqOneBitB n j.succ Hadamard) := hs
  rw [List.mem_ofFn] at hs'
  obtain ⟨j, rfl⟩ := hs'
  have hsg' : Step.gate (clusterSeqShiftOp n (clusterSeqOneBitB n j.succ Hadamard)) =
      Step.gate U := hsg
  rw [Step.gate.injEq] at hsg'
  rw [← hsg', clusterSeqShiftOp_oneBitB]
  show Matrix.diagonal (fun x : Reg (n + 2) =>
      if x (Fin.castSucc (0 : Fin (n + 1))) && x (Fin.succ (0 : Fin (n + 1)))
        then (-1 : ℂ) else 1) * _ = _
  apply clusterSeqDiagonal_oneBitB_commute
  intro x y hxy
  have h0 : x (Fin.castSucc (0 : Fin (n + 1))) = y (Fin.castSucc (0 : Fin (n + 1))) := by
    apply hxy
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_succ] at hv
  have h1 : x (Fin.succ (0 : Fin (n + 1))) = y (Fin.succ (0 : Fin (n + 1))) := by
    apply hxy
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_succ] at hv
  rw [h0, h1]

theorem clusterSeqMatShuffle {I : Type*} [Fintype I] (A B c d : Matrix I I ℂ)
    (h : c * B = B * c) : (A * c) * (B * d) = (A * B) * (c * d) := by
  rw [Matrix.mul_assoc A c, ← Matrix.mul_assoc c B d, h, Matrix.mul_assoc B c d,
    ← Matrix.mul_assoc A B (c * d)]

theorem clusterSeqResourceGateB_succ (n : ℕ) :
    clusterSeqResourceGateB (n + 1) =
      clusterSeqShiftOp n (clusterSeqResourceGateB n) *
        clusterSeqCzB (n + 1) (0 : Fin (n + 1)) *
          clusterSeqOneBitB (n + 1) (0 : Fin (n + 1)).succ Hadamard := by
  show clusterSeqCircuitGate (clusterSeqResourceCircuitB (n + 1)) = _
  rw [clusterSeqResourceCircuitB, clusterSeqCircuitGate_append, clusterSeqResourceHB_succ,
    clusterSeqResourceCzB_succ]
  show (clusterSeqCircuitGate (clusterSeqShiftCircuitB n (clusterSeqResourceCzB n)) *
      clusterSeqCzB (n + 1) (0 : Fin (n + 1))) *
    (clusterSeqCircuitGate (clusterSeqShiftCircuitB n (clusterSeqResourceHB n)) *
      clusterSeqOneBitB (n + 1) (0 : Fin (n + 1)).succ Hadamard) = _
  rw [clusterSeqCircuitGate_shiftCircuitB, clusterSeqCircuitGate_shiftCircuitB,
    clusterSeqMatShuffle _ _ (clusterSeqCzB (n + 1) (0 : Fin (n + 1))) _
      (clusterSeqCzB_zero_mul_shiftHB n),
    ← clusterSeqShiftOp_mul, ← clusterSeqCircuitGate_append, Matrix.mul_assoc]
  rfl

noncomputable def clusterSequenceResourceCircuit (n : ℕ) : Circuit (Fin (2 ^ (n + 1))) :=
  relabelCircuit (bitVecEquiv (n + 1)) (clusterSeqResourceCircuitB n)

noncomputable def clusterSequenceResourceGate (n : ℕ) : Operator (2 ^ (n + 1)) :=
  clusterSeqCircuitGate (clusterSequenceResourceCircuit n)

noncomputable def clusterSequencePreparedFrame (n : ℕ) : Matrix (Fin (2 ^ (n + 1))) (Fin 2) ℂ :=
  clusterSequenceResourceGate n * clusterSequenceInitialFrame n

theorem clusterSequenceResourceGate_eq_relabel (n : ℕ) :
    clusterSequenceResourceGate n =
      relabelGate (bitVecEquiv (n + 1)) (clusterSeqResourceGateB n) := by
  show clusterSeqCircuitGate
      (relabelCircuit (bitVecEquiv (n + 1)) (clusterSeqResourceCircuitB n)) = _
  rw [clusterSeqCircuitGate_relabel]
  rfl

theorem cluster_sequence_actual_resource_preparation :
    ∀ (n : ℕ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (clusterSequenceInitialFrame n) ∧
      clusterSequenceResourceGate n ∈ Matrix.unitaryGroup (Fin (2 ^ (n + 1))) ℂ ∧
      clusterSequencePreparedFrame n =
        clusterSequenceResourceGate n * clusterSequenceInitialFrame n ∧
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (clusterSequencePreparedFrame n) ∧
      QueryCount (clusterSequenceResourceCircuit n) = 0 ∧
      GateCount (clusterSequenceResourceCircuit n) = 2 * n ∧
      (∀ ψ : QState (Fin 2), Run (1 : Operator (2 ^ (n + 1))) (clusterSequenceResourceCircuit n)
        ((clusterSequenceInitialFrame n) *ᵥ ψ) = (clusterSequencePreparedFrame n) *ᵥ ψ) := by
  intro n
  have hgateU : clusterSequenceResourceGate n ∈ Matrix.unitaryGroup (Fin (2 ^ (n + 1))) ℂ := by
    rw [clusterSequenceResourceGate_eq_relabel]
    exact (relabelGate_mem_unitaryGroup _ _).mpr (clusterSeqResourceGateB_unitary n)
  refine ⟨clusterSequenceInitialFrame_isometry n, hgateU, rfl, ?_, ?_, ?_, ?_⟩
  · show (clusterSequencePreparedFrame n)ᴴ * clusterSequencePreparedFrame n = 1
    have hU : (clusterSequenceResourceGate n)ᴴ * clusterSequenceResourceGate n = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').mp hgateU
      rwa [Matrix.star_eq_conjTranspose] at h
    show ((clusterSequenceResourceGate n * clusterSequenceInitialFrame n)ᴴ) *
        (clusterSequenceResourceGate n * clusterSequenceInitialFrame n) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (clusterSequenceResourceGate n)ᴴ (clusterSequenceResourceGate n)
        (clusterSequenceInitialFrame n), hU, Matrix.one_mul]
    exact clusterSequenceInitialFrame_isometry n
  · show QueryCount (relabelCircuit (bitVecEquiv (n + 1)) (clusterSeqResourceCircuitB n)) = 0
    rw [(relabelCircuit_legality_resources _ _).2.1, queryCount_resourceCircuitB]
  · show GateCount (relabelCircuit (bitVecEquiv (n + 1)) (clusterSeqResourceCircuitB n)) = 2 * n
    rw [(relabelCircuit_legality_resources _ _).2.2.1, gateCount_resourceCircuitB]
  · intro ψ
    have hrun := (run_relabelCircuit_readout (bitVecEquiv (n + 1))
      (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (clusterSeqResourceCircuitB n) (clusterSeqInitialFrameB n *ᵥ ψ) Finset.univ).1
    rw [CircuitRelabel.relabelGate_one] at hrun
    show Run (1 : Operator (2 ^ (n + 1)))
        (relabelCircuit (bitVecEquiv (n + 1)) (clusterSeqResourceCircuitB n))
        (clusterSequenceInitialFrame n *ᵥ ψ) = _
    rw [clusterSequenceInitialFrame_mulVec, hrun,
      run_clusterSeqCircuitGate _ _ (queryCount_resourceCircuitB n), ← applyGate_relabelGate,
      ← clusterSeqCircuitGate_relabel, ← clusterSequenceInitialFrame_mulVec]
    show clusterSequenceResourceGate n *ᵥ (clusterSequenceInitialFrame n *ᵥ ψ) =
      clusterSequencePreparedFrame n *ᵥ ψ
    simp only [clusterSequencePreparedFrame, Matrix.mulVec_mulVec]

def clusterSeqLabelFin (m : ℕ) : Fin (2 ^ (m + 1)) → Fin 2 :=
  fun r => boolEquivFin2 ((bitVecEquiv (m + 1)).symm r 0)

noncomputable def clusterSeqOneBitFin (m : ℕ) (j : Fin (m + 1)) (U : Matrix Bool Bool ℂ) :
    Operator (2 ^ (m + 1)) :=
  relabelGate (bitVecEquiv (m + 1)) (clusterSeqOneBitB m j U)

theorem clusterSeqOneBitFin_unitary (m : ℕ) (j : Fin (m + 1)) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    clusterSeqOneBitFin m j U ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).mpr (clusterSeqOneBitB_unitary m j hU)

noncomputable def clusterSeqPhaseB (z : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a : Bool => if a then z else 1

theorem clusterSeqPhaseB_unitary {z : ℂ} (hz : ‖z‖ = 1) :
    clusterSeqPhaseB z ∈ Matrix.unitaryGroup Bool ℂ :=
  diagonal_mem_unitaryGroup _ fun a => by cases a <;> simp [hz]

noncomputable def clusterSeqPhaseFin (m : ℕ) (z : ℂ) : Operator (2 ^ (m + 1)) :=
  clusterSeqOneBitFin m 0 (clusterSeqPhaseB z)

theorem clusterSeqPhaseFin_unitary {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    clusterSeqPhaseFin m z ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ :=
  clusterSeqOneBitFin_unitary m 0 _ (clusterSeqPhaseB_unitary hz)

noncomputable def clusterSeqHFin (m : ℕ) : Operator (2 ^ (m + 1)) :=
  clusterSeqOneBitFin m 0 Hadamard

theorem clusterSeqHFin_unitary (m : ℕ) :
    clusterSeqHFin m ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ :=
  clusterSeqOneBitFin_unitary m 0 _ hadamard_unitary

noncomputable def clusterSeqXFin (m : ℕ) (hm : 0 < m) (k : Fin 2) : Operator (2 ^ (m + 1)) :=
  clusterSeqOneBitFin m ⟨1, by omega⟩ (if boolEquivFin2.symm k then PauliX else 1)

theorem clusterSeqXFin_unitary (m : ℕ) (hm : 0 < m) (k : Fin 2) :
    clusterSeqXFin m hm k ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ := by
  unfold clusterSeqXFin
  refine clusterSeqOneBitFin_unitary _ _ _ ?_
  by_cases hk : boolEquivFin2.symm k
  · simp only [if_pos hk]
    exact pauliX_unitary
  · simp only [if_neg hk]
    exact Submonoid.one_mem _

noncomputable def clusterSeqZFin (m : ℕ) (hm : 1 < m) (k : Fin 2) : Operator (2 ^ (m + 1)) :=
  clusterSeqOneBitFin m ⟨2, by omega⟩ (if boolEquivFin2.symm k then PauliZ else 1)

theorem clusterSeqZFin_unitary (m : ℕ) (hm : 1 < m) (k : Fin 2) :
    clusterSeqZFin m hm k ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ := by
  unfold clusterSeqZFin
  refine clusterSeqOneBitFin_unitary _ _ _ ?_
  by_cases hk : boolEquivFin2.symm k
  · simp only [if_pos hk]
    exact pauliZ_unitary
  · simp only [if_neg hk]
    exact Submonoid.one_mem _

noncomputable def clusterSeqShiftGateFin (m : ℕ) (U : Operator (2 ^ (m + 1))) :
    Operator (2 ^ (m + 2)) :=
  relabelGate (bitVecEquiv (m + 2))
    (clusterSeqShiftOp m (relabelGate (bitVecEquiv (m + 1)).symm U))

def clusterSeqShiftLabelFin (m : ℕ) {k : ℕ} (l : Fin (2 ^ (m + 1)) → Fin k) :
    Fin (2 ^ (m + 2)) → Fin k :=
  fun r => l (bitVecEquiv (m + 1) (Fin.tail ((bitVecEquiv (m + 2)).symm r)))

noncomputable def clusterSeqShiftObservedFin (m : ℕ) :
    ObservedCircuit (Fin (2 ^ (m + 1))) → ObservedCircuit (Fin (2 ^ (m + 2)))
  | .halt b => .halt b
  | .step (.gate U) next =>
      .step (.gate (clusterSeqShiftGateFin m U)) (clusterSeqShiftObservedFin m next)
  | .step .query next => .step .query (clusterSeqShiftObservedFin m next)
  | .measure k l next =>
      .measure k (clusterSeqShiftLabelFin m l)
        (fun o => clusterSeqShiftObservedFin m (next o))
  | .project P onFalse onTrue =>
      .project (clusterSeqShiftGateFin m P)
        (clusterSeqShiftObservedFin m onFalse) (clusterSeqShiftObservedFin m onTrue)

theorem clusterSeqShiftGateFin_relabel (m : ℕ) (W : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ) :
    clusterSeqShiftGateFin m (relabelGate (bitVecEquiv (m + 1)) W)
      = relabelGate (bitVecEquiv (m + 2)) (clusterSeqShiftOp m W) := by
  unfold clusterSeqShiftGateFin
  rw [relabelGate_relabelGate]

theorem clusterSeqShiftGateFin_mul (m : ℕ) (A B : Operator (2 ^ (m + 1))) :
    clusterSeqShiftGateFin m (A * B) = clusterSeqShiftGateFin m A * clusterSeqShiftGateFin m B := by
  unfold clusterSeqShiftGateFin
  rw [CircuitRelabel.relabelGate_mul, clusterSeqShiftOp_mul,
    ← CircuitRelabel.relabelGate_mul]

theorem clusterSeqShiftGateFin_one (m : ℕ) :
    clusterSeqShiftGateFin m 1 = 1 := by
  unfold clusterSeqShiftGateFin
  rw [CircuitRelabel.relabelGate_one, clusterSeqShiftOp_one, CircuitRelabel.relabelGate_one]

theorem clusterSeqShiftGateFin_unitary (m : ℕ) {U : Operator (2 ^ (m + 1))}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 1))) ℂ) :
    clusterSeqShiftGateFin m U ∈ Matrix.unitaryGroup (Fin (2 ^ (m + 2))) ℂ := by
  unfold clusterSeqShiftGateFin
  exact (relabelGate_mem_unitaryGroup _ _).mpr
    (clusterSeqShiftOp_unitary m ((relabelGate_mem_unitaryGroup _ _).mpr hU))

theorem clusterSeqShiftLabelFin_labelFin (m : ℕ) (r : Fin (2 ^ (m + 2))) :
    clusterSeqShiftLabelFin m (clusterSeqLabelFin m) r
      = boolEquivFin2 ((bitVecEquiv (m + 2)).symm r (Fin.succ (0 : Fin (m + 1)))) := by
  unfold clusterSeqShiftLabelFin clusterSeqLabelFin
  rw [Equiv.symm_apply_apply]
  rfl

theorem clusterSeqShiftGateFin_projector (m : ℕ) {k : ℕ} (l : Fin (2 ^ (m + 1)) → Fin k)
    (o : Fin k) :
    clusterSeqShiftGateFin m (Projector (Finset.univ.filter (fun r => l r = o)))
      = Projector (Finset.univ.filter (fun r => clusterSeqShiftLabelFin m l r = o)) := by
  ext r r'
  unfold clusterSeqShiftGateFin relabelGate
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, clusterSeqShiftOp_entry,
    Projector, Matrix.diagonal_apply, Matrix.diagonal_apply, Equiv.symm_symm]
  by_cases hrr' : r' = r
  · rw [hrr', if_pos rfl, one_mul, if_pos rfl, if_pos rfl]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold clusterSeqShiftLabelFin
    by_cases hl : l (bitVecEquiv (m + 1) (Fin.tail ((bitVecEquiv (m + 2)).symm r))) = o
    · simp only [if_pos hl]
    · simp only [if_neg hl]
  · have hne : (bitVecEquiv (m + 2)).symm r' ≠ (bitVecEquiv (m + 2)).symm r :=
      fun h => hrr' (Equiv.injective ((bitVecEquiv (m + 2)).symm) h)
    by_cases h0 : (bitVecEquiv (m + 2)).symm r 0 = (bitVecEquiv (m + 2)).symm r' 0
    · have htail : Fin.tail ((bitVecEquiv (m + 2)).symm r)
          ≠ Fin.tail ((bitVecEquiv (m + 2)).symm r') := fun ht => hne (by
        rw [← Fin.cons_self_tail ((bitVecEquiv (m + 2)).symm r),
          ← Fin.cons_self_tail ((bitVecEquiv (m + 2)).symm r'), h0, ht])
      rw [if_pos h0,
        if_neg (fun hc : (bitVecEquiv (m + 1)) (Fin.tail ((bitVecEquiv (m + 2)).symm r))
            = (bitVecEquiv (m + 1)) (Fin.tail ((bitVecEquiv (m + 2)).symm r')) =>
          htail (Equiv.injective (bitVecEquiv (m + 1)) hc)),
        mul_zero, if_neg (fun h : r = r' => hrr' h.symm)]
    · rw [if_neg h0, zero_mul, if_neg (fun h : r = r' => hrr' h.symm)]

theorem clusterSeqOfFn_congr {α : Type*} {n : ℕ} {f g : Fin n → α} (h : ∀ i, f i = g i) :
    List.ofFn f = List.ofFn g := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact List.map_congr_left (fun a _ => h a)

theorem clusterSeqOfFn_fin1 {α : Type*} (f : Fin 1 → α) : List.ofFn f = [f 0] := by
  have h0 : List.ofFn (fun i : Fin 0 => f i.succ) = [] :=
    List.eq_nil_of_length_eq_zero (by simp)
  rw [List.ofFn_succ, h0]

theorem clusterSeqOfFn_fin2 {α : Type*} (f : Fin 2 → α) : List.ofFn f = [f 0, f 1] := by
  have h0 : List.ofFn (fun i : Fin 0 => f i.succ.succ) = [] :=
    List.eq_nil_of_length_eq_zero (by simp)
  rw [List.ofFn_succ, List.ofFn_succ, h0]
  rfl

theorem clusterSeqOfFn_append {α : Type*} (k : ℕ) (F : Fin (2 ^ k + 2 ^ k) → α) :
    List.ofFn F =
      List.ofFn (fun i : Fin (2 ^ k) => F (Fin.castAdd (2 ^ k) i)) ++
        List.ofFn (fun i : Fin (2 ^ k) => F (Fin.natAdd (2 ^ k) i)) := by
  have hl1 : (List.ofFn F).length = 2 ^ k + 2 ^ k := by simp
  have hl2 : (List.ofFn (fun i : Fin (2 ^ k) => F (Fin.castAdd (2 ^ k) i))).length = 2 ^ k := by
    simp
  have hl3 : (List.ofFn (fun i : Fin (2 ^ k) => F (Fin.natAdd (2 ^ k) i))).length = 2 ^ k := by
    simp
  have hlapp : ((List.ofFn (fun i : Fin (2 ^ k) => F (Fin.castAdd (2 ^ k) i))) ++
      (List.ofFn (fun i : Fin (2 ^ k) => F (Fin.natAdd (2 ^ k) i)))).length = 2 ^ k + 2 ^ k := by
    rw [List.length_append, hl2, hl3]
  apply List.ext_getElem?'
  intro n _
  by_cases h : n < 2 ^ k
  · have hn1 : n < (List.ofFn F).length := by rw [hl1]; omega
    have hn2 : n < (List.ofFn (fun i : Fin (2 ^ k) => F (Fin.castAdd (2 ^ k) i))).length := by
      rw [hl2]; omega
    rw [List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem (by rw [hlapp]; omega)]
    rw [List.getElem_ofFn hn1, List.getElem_append_left hn2, List.getElem_ofFn hn2]
    congr 1
  · have hn1 : n < (List.ofFn F).length := by rw [hl1]; omega
    have hn2 : (List.ofFn (fun i : Fin (2 ^ k) => F (Fin.castAdd (2 ^ k) i))).length ≤ n := by
      rw [hl2]; omega
    have hn3 : n - (List.ofFn (fun i : Fin (2 ^ k) => F (Fin.castAdd (2 ^ k) i))).length <
        (List.ofFn (fun i : Fin (2 ^ k) => F (Fin.natAdd (2 ^ k) i))).length := by
      rw [hl2, hl3]; omega
    rw [List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem (by rw [hlapp]; omega)]
    rw [List.getElem_ofFn hn1, List.getElem_append_right hn2]
    simp only [List.getElem_ofFn hn3, Option.some.injEq]
    apply congrArg F
    apply Fin.ext
    simp only [Fin.natAdd, Fin.val_mk]
    rw [hl2]
    omega

theorem clusterSeqBitVec_one (x : Reg 1) : bitVecEquiv 1 x = boolEquivFin2 (x 0) := by
  have h := bitVecEquiv_succ_val 0 x
  simp only [bitVecEquiv_zero, mul_zero, add_zero, Fin.val_zero] at h
  have hx : x (Fin.last 0) = x 0 := rfl
  rw [hx] at h
  ext
  simpa using! h.symm

theorem clusterSeqBitVec_one_label (i : Fin 2) :
    boolEquivFin2 ((bitVecEquiv 1).symm i 0) = i := by
  rw [← clusterSeqBitVec_one ((bitVecEquiv 1).symm i), Equiv.apply_symm_apply]

theorem clusterSeqBitVec_symm_castAdd (k : ℕ) (i : Fin (2 ^ k))
    (h : 2 ^ k + 2 ^ k = 2 ^ (k + 1)) :
    (bitVecEquiv (k + 1)).symm (Fin.cast h (Fin.castAdd (2 ^ k) i))
      = Fin.cons false ((bitVecEquiv k).symm i) := by
  apply (bitVecEquiv (k + 1)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.val_injective
  have hsymm := congrArg Fin.val (Equiv.apply_symm_apply (bitVecEquiv k) i)
  rw [bitVecEquiv_cons_val, hsymm, Fin.val_cast, Fin.val_castAdd]
  simp
  rfl

theorem clusterSeqBitVec_symm_natAdd (k : ℕ) (i : Fin (2 ^ k))
    (h : 2 ^ k + 2 ^ k = 2 ^ (k + 1)) :
    (bitVecEquiv (k + 1)).symm (Fin.cast h (Fin.natAdd (2 ^ k) i))
      = Fin.cons true ((bitVecEquiv k).symm i) := by
  apply (bitVecEquiv (k + 1)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.val_injective
  have hsymm := congrArg Fin.val (Equiv.apply_symm_apply (bitVecEquiv k) i)
  rw [bitVecEquiv_cons_val, hsymm, Fin.val_cast, Fin.val_natAdd]
  simp
  rfl

theorem clusterSeqBitVec_symm_low (k : ℕ) (v : ℕ) (h1 : v < 2 ^ (k + 1)) (h2 : v < 2 ^ k) :
    (bitVecEquiv (k + 1)).symm ⟨v, h1⟩
      = Fin.cons false ((bitVecEquiv k).symm ⟨v, h2⟩) := by
  apply (bitVecEquiv (k + 1)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.val_injective
  have hsymm := congrArg Fin.val (Equiv.apply_symm_apply (bitVecEquiv k) ⟨v, h2⟩)
  rw [bitVecEquiv_cons_val, hsymm]
  simp
  rfl

theorem clusterSeqBitVec_symm_high (k : ℕ) (v : ℕ) (h1 : v < 2 ^ (k + 1))
    (hge : 2 ^ k ≤ v) :
    (bitVecEquiv (k + 1)).symm ⟨v, h1⟩
      = Fin.cons true ((bitVecEquiv k).symm ⟨v - 2 ^ k, by omega⟩) := by
  apply (bitVecEquiv (k + 1)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.val_injective
  have hsymm := congrArg Fin.val
    (Equiv.apply_symm_apply (bitVecEquiv k) ⟨v - 2 ^ k, by omega⟩)
  rw [bitVecEquiv_cons_val, hsymm]
  have hb : (boolEquivFin2 true).val = 1 := rfl
  rw [hb, one_mul]
  simp only
  have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [← Nat.mul_two, ← Nat.pow_succ]
  omega

theorem clusterSeqRelabelGate_sub {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A - B) = relabelGate e A - relabelGate e B := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]

theorem clusterSeqShiftOp_sub (m : ℕ) (A B : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ) :
    clusterSeqShiftOp m (A - B) = clusterSeqShiftOp m A - clusterSeqShiftOp m B := by
  ext x y
  have h := clusterSeqShiftOp_entry m (A - B) x y
  have hA := clusterSeqShiftOp_entry m A x y
  have hB := clusterSeqShiftOp_entry m B x y
  rw [Matrix.sub_apply, h, hA, hB, Matrix.sub_apply]
  by_cases hc : x 0 = y 0 <;> ring

theorem clusterSeqShiftGateFin_sub (m : ℕ) (A B : Operator (2 ^ (m + 1))) :
    clusterSeqShiftGateFin m (A - B) = clusterSeqShiftGateFin m A - clusterSeqShiftGateFin m B := by
  unfold clusterSeqShiftGateFin
  rw [clusterSeqRelabelGate_sub, clusterSeqShiftOp_sub, clusterSeqRelabelGate_sub]

noncomputable def clusterSeqShiftLeaf (m : ℕ) (L : ObservedKrausLeaf (2 ^ (m + 1))) :
    ObservedKrausLeaf (2 ^ (m + 2)) where
  operator := clusterSeqShiftGateFin m L.operator
  accepted := L.accepted
  queries := L.queries
  gates := L.gates
  measurements := L.measurements
  outcomes := L.outcomes

theorem clusterSeqShiftLeaf_prepend (m : ℕ) (U : Operator (2 ^ (m + 1))) (q g c : ℕ)
    (outcomes : List (ℕ × ℕ)) (L : ObservedKrausLeaf (2 ^ (m + 1))) :
    ObservedKrausLeaf.prepend (clusterSeqShiftGateFin m U) q g c outcomes (clusterSeqShiftLeaf m L)
      = clusterSeqShiftLeaf m (ObservedKrausLeaf.prepend U q g c outcomes L) := by
  simp only [ObservedKrausLeaf.prepend, clusterSeqShiftLeaf, clusterSeqShiftGateFin_mul]

theorem clusterSeqShiftLeaf_prepend_query (m : ℕ)
    (L : ObservedKrausLeaf (2 ^ (m + 1))) :
    ObservedKrausLeaf.prepend (1 : Operator (2 ^ (m + 2))) 1 0 0 []
        (clusterSeqShiftLeaf m L)
      = clusterSeqShiftLeaf m (ObservedKrausLeaf.prepend (1 : Operator (2 ^ (m + 1))) 1 0 0 [] L) := by
  simp only [ObservedKrausLeaf.prepend, clusterSeqShiftLeaf, Matrix.mul_one]

theorem clusterSeqShiftLeaf_prepend_projector (m : ℕ) {k : ℕ} (l : Fin (2 ^ (m + 1)) → Fin k)
    (o : Fin k) (L : ObservedKrausLeaf (2 ^ (m + 1))) :
    ObservedKrausLeaf.prepend
        (Projector (Finset.univ.filter (fun r => clusterSeqShiftLabelFin m l r = o))) 0 0 1
        [(k, o.val)] (clusterSeqShiftLeaf m L)
      = clusterSeqShiftLeaf m
        (ObservedKrausLeaf.prepend (Projector (Finset.univ.filter (fun r => l r = o))) 0 0 1
          [(k, o.val)] L) := by
  rw [← clusterSeqShiftGateFin_projector]
  simp only [ObservedKrausLeaf.prepend, clusterSeqShiftLeaf, clusterSeqShiftGateFin_mul]

theorem observedKrausLeaves_shiftObservedFin (m : ℕ) :
    ∀ P : ObservedCircuit (Fin (2 ^ (m + 1))),
      observedKrausLeaves 1 (clusterSeqShiftObservedFin m P)
        = (observedKrausLeaves 1 P).map (clusterSeqShiftLeaf m) := by
  intro P
  induction P with
  | halt b =>
    simp only [clusterSeqShiftObservedFin, observedKrausLeaves, List.map_cons, List.map_nil,
      clusterSeqShiftLeaf, clusterSeqShiftGateFin_one]
  | step s next ih =>
    cases s with
    | gate U =>
      simp only [clusterSeqShiftObservedFin, observedKrausLeaves, ih, List.map_map,
        Function.comp_def]
      exact List.map_congr_left (fun L _ => clusterSeqShiftLeaf_prepend m U 0 1 0 [] L)
    | query =>
      simp only [clusterSeqShiftObservedFin, observedKrausLeaves, ih, List.map_map,
        Function.comp_def]
      exact List.map_congr_left (fun L _ => clusterSeqShiftLeaf_prepend_query m L)
  | measure k l nexts ih =>
    simp only [clusterSeqShiftObservedFin, observedKrausLeaves, List.map_flatten,
      List.map_ofFn, List.map_map, Function.comp_def, ih]
    congr 1
    apply clusterSeqOfFn_congr
    intro o
    exact List.map_congr_left (fun L _ => clusterSeqShiftLeaf_prepend_projector m l o L)
  | project P onFalse onTrue ihFalse ihTrue =>
    simp only [clusterSeqShiftObservedFin, observedKrausLeaves, List.map_append,
      List.map_map, Function.comp_def, ihFalse, ihTrue]
    congr 1
    · refine List.map_congr_left (fun L _ => ?_)
      rw [← clusterSeqShiftGateFin_one, ← clusterSeqShiftGateFin_sub]
      exact clusterSeqShiftLeaf_prepend m (1 - P) 0 0 1 [(2, 0)] L
    · exact List.map_congr_left (fun L _ => clusterSeqShiftLeaf_prepend m P 0 0 1 [(2, 1)] L)

noncomputable def clusterSeqFullGate {I : Type*} [Fintype I] [DecidableEq I]
    (oracle : Matrix I I ℂ) : Circuit I → Matrix I I ℂ
  | [] => 1
  | Step.gate U :: C => clusterSeqFullGate oracle C * U
  | Step.query :: C => clusterSeqFullGate oracle C * oracle

theorem clusterSeqFullGate_one {I : Type*} [Fintype I] [DecidableEq I] (C : Circuit I) :
    clusterSeqFullGate (1 : Matrix I I ℂ) C = clusterSeqCircuitGate C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [clusterSeqFullGate, ih, clusterSeqCircuitGate]
    | query => rw [clusterSeqFullGate, ih, Matrix.mul_one, clusterSeqCircuitGate]

noncomputable def clusterSeqPrependSteps {D : ℕ} (oracle : Operator D) :
    Circuit (Fin D) → ObservedCircuit (Fin D) → ObservedCircuit (Fin D)
  | [], P => P
  | Step.gate U :: C, P => .step (.gate U) (clusterSeqPrependSteps oracle C P)
  | Step.query :: C, P => .step .query (clusterSeqPrependSteps oracle C P)

theorem observedKrausLeaves_prependSteps {D : ℕ} (oracle : Operator D) (C : Circuit (Fin D))
    (P : ObservedCircuit (Fin D)) :
    observedKrausLeaves oracle (clusterSeqPrependSteps oracle C P)
      = (observedKrausLeaves oracle P).map
        (ObservedKrausLeaf.prepend (clusterSeqFullGate oracle C) (QueryCount C) (GateCount C)
          0 []) := by
  induction C generalizing P with
  | nil =>
    have h : (observedKrausLeaves oracle P).map
        (ObservedKrausLeaf.prepend (1 : Operator D) 0 0 0 []) = observedKrausLeaves oracle P := by
      exact (List.map_congr_left fun L _ => by
        simp only [id_eq, ObservedKrausLeaf.prepend, Matrix.mul_one, Nat.add_zero,
          List.nil_append]).trans (List.map_id _)
    show observedKrausLeaves oracle P =
      (observedKrausLeaves oracle P).map
        (ObservedKrausLeaf.prepend (1 : Operator D) 0 0 0 [])
    exact h.symm
  | cons s C ih =>
    cases s with
    | gate U =>
      show observedKrausLeaves oracle
          (.step (.gate U) (clusterSeqPrependSteps oracle C P)) = _
      rw [observedKrausLeaves, ih, List.map_map, Function.comp_def, clusterSeqFullGate,
        queryCount_gate, gateCount_gate]
      exact List.map_congr_left fun L _ => by
        simp only [ObservedKrausLeaf.prepend, Matrix.mul_assoc, Nat.add_assoc, Nat.add_zero,
          List.nil_append]
    | query =>
      show observedKrausLeaves oracle
          (.step .query (clusterSeqPrependSteps oracle C P)) = _
      rw [observedKrausLeaves, ih, List.map_map, Function.comp_def, clusterSeqFullGate,
        queryCount_query, gateCount_query]
      exact List.map_congr_left fun L _ => by
        simp only [ObservedKrausLeaf.prepend, Matrix.mul_assoc, Nat.add_assoc, Nat.add_zero,
          List.nil_append]

noncomputable def clusterSeqLoopFin :
    (zs : List ℂ) → ObservedCircuit (Fin (2 ^ (zs.length + 1)))
  | [] => .halt true
  | [z] =>
      .step (.gate (clusterSeqPhaseFin 1 z)) (.step (.gate (clusterSeqHFin 1))
        (.measure 2 (clusterSeqLabelFin 1)
          (fun k => .step (.gate (clusterSeqXFin 1 (by omega) k)) (.halt true))))
  | z :: w :: ws =>
      .step (.gate (clusterSeqPhaseFin _ z)) (.step (.gate (clusterSeqHFin _))
        (.measure 2 (clusterSeqLabelFin _)
          (fun k => .step (.gate (clusterSeqXFin _ (by simp only [List.length_cons]; omega) k))
            (.step (.gate (clusterSeqZFin _ (by simp only [List.length_cons]; omega) k))
              (clusterSeqShiftObservedFin _ (clusterSeqLoopFin (w :: ws)))))))

noncomputable def clusterSeqLoopLeafGen :
    (zs : List ℂ) → Reg zs.length → ObservedKrausLeaf (2 ^ (zs.length + 1))
  | [], _ => ⟨1, true, 0, 0, 0, []⟩
  | [z], ω =>
      ⟨clusterSeqXFin 1 (by omega) (boolEquivFin2 (ω 0))
          * Projector (Finset.univ.filter
              (fun r : Fin (2 ^ (1 + 1)) => clusterSeqLabelFin 1 r = boolEquivFin2 (ω 0)))
          * clusterSeqHFin 1 * clusterSeqPhaseFin 1 z,
        true, 0, 3, 1, [(2, (boolEquivFin2 (ω 0)).val)]⟩
  | z :: w :: ws, ω =>
      ⟨clusterSeqShiftGateFin _ ((clusterSeqLoopLeafGen (w :: ws) (Fin.tail ω)).operator)
          * clusterSeqZFin (z :: w :: ws).length
              (by simp only [List.length_cons]; omega) (boolEquivFin2 (ω 0))
          * clusterSeqXFin (z :: w :: ws).length
              (by simp only [List.length_cons]; omega) (boolEquivFin2 (ω 0))
          * Projector (Finset.univ.filter
              (fun r : Fin (2 ^ ((z :: w :: ws).length + 1)) =>
                clusterSeqLabelFin (z :: w :: ws).length r = boolEquivFin2 (ω 0)))
          * clusterSeqHFin (z :: w :: ws).length
          * clusterSeqPhaseFin (z :: w :: ws).length z,
        true, 0,
        (clusterSeqLoopLeafGen (w :: ws) (Fin.tail ω)).gates + 4,
        (clusterSeqLoopLeafGen (w :: ws) (Fin.tail ω)).measurements + 1,
        (2, (boolEquivFin2 (ω 0)).val) :: (clusterSeqLoopLeafGen (w :: ws) (Fin.tail ω)).outcomes⟩

theorem observedLeafCount_shiftObservedFin (m : ℕ) :
    ∀ P : ObservedCircuit (Fin (2 ^ (m + 1))),
      observedLeafCount (clusterSeqShiftObservedFin m P) = observedLeafCount P := by
  intro P
  induction P with
  | halt b => rfl
  | step s next ih => cases s <;> exact ih
  | measure k l nexts ih =>
    show ∑ o : Fin k, observedLeafCount (clusterSeqShiftObservedFin m (nexts o))
      = ∑ o : Fin k, observedLeafCount (nexts o)
    exact Finset.sum_congr rfl fun o _ => ih o
  | project P onFalse onTrue ihFalse ihTrue =>
    show observedLeafCount (clusterSeqShiftObservedFin m onFalse)
        + observedLeafCount (clusterSeqShiftObservedFin m onTrue)
      = observedLeafCount onFalse + observedLeafCount onTrue
    rw [ihFalse, ihTrue]

theorem observedLeafCount_loopFin (zs : List ℂ) :
    observedLeafCount (clusterSeqLoopFin zs) = 2 ^ zs.length := by
  induction zs with
  | nil => rfl
  | cons z L ih =>
    cases L with
    | nil =>
      show ∑ o : Fin 2, observedLeafCount (ObservedCircuit.halt true : ObservedCircuit (Fin 4))
        = 2 ^ 1
      rw [Fin.sum_univ_two]
      rfl
    | cons w ws =>
      rw [show clusterSeqLoopFin (z :: w :: ws) =
        .step (.gate (clusterSeqPhaseFin _ z)) (.step (.gate (clusterSeqHFin _))
          (.measure 2 (clusterSeqLabelFin _)
            (fun k => .step (.gate (clusterSeqXFin _
                (by simp only [List.length_cons]; omega) k))
              (.step (.gate (clusterSeqZFin _
                (by simp only [List.length_cons]; omega) k))
                (clusterSeqShiftObservedFin _ (clusterSeqLoopFin (w :: ws))))))) from rfl]
      show ∑ o : Fin 2, observedLeafCount
          (clusterSeqShiftObservedFin (w :: ws).length (clusterSeqLoopFin (w :: ws)))
        = 2 ^ (z :: w :: ws).length
      rw [observedLeafCount_shiftObservedFin, Fin.sum_univ_two, ih, ← Nat.mul_two,
        ← Nat.pow_succ]
      simp only [List.length_cons]

theorem clusterSeqLoopLeafGen_accepted (zs : List ℂ) (ω : Reg zs.length) :
    (clusterSeqLoopLeafGen zs ω).accepted = true := by
  match zs, ω with
  | [], _ => rfl
  | [z], _ => rfl
  | z :: w :: ws, _ => rfl

theorem clusterSeqLoopLeafGen_queries (zs : List ℂ) (ω : Reg zs.length) :
    (clusterSeqLoopLeafGen zs ω).queries = 0 := by
  match zs, ω with
  | [], _ => rfl
  | [z], _ => rfl
  | z :: w :: ws, _ => rfl

theorem clusterSeqLoopElem_low (z w : ℂ) (ws : List ℂ) (j : Fin (2 ^ (w :: ws).length)) :
    ObservedKrausLeaf.prepend (clusterSeqPhaseFin (z :: w :: ws).length z) 0 1 0 []
      (ObservedKrausLeaf.prepend (clusterSeqHFin (z :: w :: ws).length) 0 1 0 []
        (ObservedKrausLeaf.prepend
          (Projector (Finset.univ.filter
            (fun r => clusterSeqLabelFin (z :: w :: ws).length r = 0))) 0 0 1 [(2, (0 : Fin 2).val)]
          (ObservedKrausLeaf.prepend (clusterSeqXFin (z :: w :: ws).length
            (by simp only [List.length_cons]; omega) 0) 0 1 0 []
            (ObservedKrausLeaf.prepend (clusterSeqZFin (z :: w :: ws).length
              (by simp only [List.length_cons]; omega) 0) 0 1 0 []
              (clusterSeqShiftLeaf (w :: ws).length
                (clusterSeqLoopLeafGen (w :: ws)
                  ((bitVecEquiv (w :: ws).length).symm j)))))))
      = clusterSeqLoopLeafGen (z :: w :: ws)
          (Fin.cons false ((bitVecEquiv (w :: ws).length).symm j)) := by
  simp only [clusterSeqLoopLeafGen, Fin.tail_cons, Fin.cons_zero,
    ObservedKrausLeaf.prepend, clusterSeqShiftLeaf]
  simp [boolEquivFin2, clusterSeqLoopLeafGen_accepted, clusterSeqLoopLeafGen_queries]

theorem clusterSeqLoopElem_high (z w : ℂ) (ws : List ℂ) (j : Fin (2 ^ (w :: ws).length)) :
    ObservedKrausLeaf.prepend (clusterSeqPhaseFin (z :: w :: ws).length z) 0 1 0 []
      (ObservedKrausLeaf.prepend (clusterSeqHFin (z :: w :: ws).length) 0 1 0 []
        (ObservedKrausLeaf.prepend
          (Projector (Finset.univ.filter
            (fun r => clusterSeqLabelFin (z :: w :: ws).length r = 1))) 0 0 1 [(2, (1 : Fin 2).val)]
          (ObservedKrausLeaf.prepend (clusterSeqXFin (z :: w :: ws).length
            (by simp only [List.length_cons]; omega) 1) 0 1 0 []
            (ObservedKrausLeaf.prepend (clusterSeqZFin (z :: w :: ws).length
              (by simp only [List.length_cons]; omega) 1) 0 1 0 []
              (clusterSeqShiftLeaf (w :: ws).length
                (clusterSeqLoopLeafGen (w :: ws)
                  ((bitVecEquiv (w :: ws).length).symm j)))))))
      = clusterSeqLoopLeafGen (z :: w :: ws)
          (Fin.cons true ((bitVecEquiv (w :: ws).length).symm j)) := by
  simp only [clusterSeqLoopLeafGen, Fin.tail_cons, Fin.cons_zero,
    ObservedKrausLeaf.prepend, clusterSeqShiftLeaf]
  simp [boolEquivFin2, clusterSeqLoopLeafGen_accepted, clusterSeqLoopLeafGen_queries]

set_option maxHeartbeats 1000000 in

theorem clusterSeqLoopFin_leaves (zs : List ℂ) :
    observedKrausLeaves 1 (clusterSeqLoopFin zs)
      = List.ofFn fun i : Fin (2 ^ zs.length) =>
          clusterSeqLoopLeafGen zs ((bitVecEquiv zs.length).symm i) := by
  induction zs with
  | nil =>
    rw [show clusterSeqLoopFin ([] : List ℂ) = ObservedCircuit.halt true from rfl,
      observedKrausLeaves, clusterSeqOfFn_fin1]
    rfl
  | cons z L ih =>
    cases L with
    | nil =>
      have hprog : clusterSeqLoopFin [z] =
          .step (.gate (clusterSeqPhaseFin 1 z)) (.step (.gate (clusterSeqHFin 1))
            (.measure 2 (clusterSeqLabelFin 1)
              (fun k => .step (.gate (clusterSeqXFin 1 (by omega) k)) (.halt true)))) := rfl
      rw [hprog]
      simp only [observedKrausLeaves]
      rw [List.map_flatten, List.map_ofFn, List.map_flatten, List.map_ofFn,
        Function.comp_def]
      have hR : List.ofFn (fun i : Fin (2 ^ ([z] : List ℂ).length) =>
          clusterSeqLoopLeafGen [z] ((bitVecEquiv [z].length).symm i))
        = List.ofFn (fun i : Fin 2 =>
          clusterSeqLoopLeafGen [z] ((bitVecEquiv 1).symm i)) := rfl
      rw [hR]
      simp only [clusterSeqLoopLeafGen, clusterSeqBitVec_one_label, clusterSeqOfFn_fin2,
        List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.nil_append, List.cons_append, ObservedKrausLeaf.prepend, Matrix.one_mul,
        Function.comp_apply]
      rfl
    | cons w ws =>
      have hL2 : (z :: w :: ws).length = (w :: ws).length + 1 := by
        simp only [List.length_cons]
      have hlenT : (observedKrausLeaves 1 (clusterSeqLoopFin (w :: ws))).length
          = 2 ^ (w :: ws).length := by
        rw [observedKrausLeaves_length, observedLeafCount_loopFin]
      have hprog : clusterSeqLoopFin (z :: w :: ws) =
          .step (.gate (clusterSeqPhaseFin _ z)) (.step (.gate (clusterSeqHFin _))
            (.measure 2 (clusterSeqLabelFin _)
              (fun k => .step (.gate (clusterSeqXFin _
                  (by simp only [List.length_cons]; omega) k))
                (.step (.gate (clusterSeqZFin _
                  (by simp only [List.length_cons]; omega) k))
                  (clusterSeqShiftObservedFin _ (clusterSeqLoopFin (w :: ws))))))) := rfl
      have hlenL : (observedKrausLeaves 1 (clusterSeqLoopFin (z :: w :: ws))).length
          = 2 ^ (z :: w :: ws).length := by
        rw [observedKrausLeaves_length, observedLeafCount_loopFin]
      apply List.ext_getElem?'
      intro n hn
      rw [hlenL, List.length_ofFn] at hn
      have hn2 : n < 2 ^ (z :: w :: ws).length := by omega
      have hbL : n < (observedKrausLeaves 1 (clusterSeqLoopFin (z :: w :: ws))).length := by
        rw [hlenL]; omega
      rw [List.getElem?_eq_getElem hbL, List.getElem?_eq_getElem (by simp; omega)]
      simp only [Option.some.injEq]
      rw [List.getElem_ofFn (by rw [List.length_ofFn]; omega)]
      simp only [hprog, observedKrausLeaves]
      simp only [observedKrausLeaves_shiftObservedFin, ih,
        List.map_ofFn, Function.comp_def,
        clusterSeqOfFn_fin2, List.flatten_cons, List.flatten_nil]
      have hpow : 2 ^ (z :: w :: ws).length
          = 2 ^ (w :: ws).length + 2 ^ (w :: ws).length := by
        rw [hL2, ← Nat.mul_two, ← Nat.pow_succ]
      have hn1 : n < 2 ^ (z :: w :: ws).length := hn2
      simp only [List.append_nil]
      by_cases h : n < 2 ^ (w :: ws).length
      · rw [List.getElem_map, List.getElem_map,
          List.getElem_append_left (by rw [List.length_ofFn]; omega),
          List.getElem_ofFn (by rw [List.length_ofFn]; omega),
          clusterSeqLoopElem_low z w ws ⟨n, h⟩]
        exact congrArg (clusterSeqLoopLeafGen (z :: w :: ws))
          (clusterSeqBitVec_symm_low (w :: ws).length n hn1 h).symm
      · rw [List.getElem_map, List.getElem_map,
          List.getElem_append_right (by rw [List.length_ofFn]; omega)]
        simp only [List.length_ofFn]
        rw [List.getElem_ofFn (by rw [List.length_ofFn]; omega),
          clusterSeqLoopElem_high z w ws ⟨n - 2 ^ (w :: ws).length, by omega⟩]
        exact congrArg (clusterSeqLoopLeafGen (z :: w :: ws))
          (clusterSeqBitVec_symm_high (w :: ws).length n hn1 (by omega)).symm

noncomputable def clusterSequenceProgram (zs : List ℂ) :
    ObservedCircuit (Fin (2 ^ (zs.length + 1))) :=
  clusterSeqPrependSteps 1 (clusterSequenceResourceCircuit zs.length) (clusterSeqLoopFin zs)

theorem observedLeafCount_prependSteps {D : ℕ} (oracle : Operator D) (C : Circuit (Fin D))
    (P : ObservedCircuit (Fin D)) :
    observedLeafCount (clusterSeqPrependSteps oracle C P) = observedLeafCount P := by
  induction C generalizing P with
  | nil => rfl
  | cons s C ih => cases s <;> exact ih P

theorem observedLeafCount_program (zs : List ℂ) :
    observedLeafCount (clusterSequenceProgram zs) = 2 ^ zs.length := by
  rw [clusterSequenceProgram, observedLeafCount_prependSteps, observedLeafCount_loopFin]

noncomputable def clusterSeqProgramLeafGen (zs : List ℂ) (ω : Reg zs.length) :
    ObservedKrausLeaf (2 ^ (zs.length + 1)) :=
  ObservedKrausLeaf.prepend (clusterSequenceResourceGate zs.length) 0 (2 * zs.length) 0 []
    (clusterSeqLoopLeafGen zs ω)

theorem clusterSequenceProgram_leaves (zs : List ℂ) :
    observedKrausLeaves 1 (clusterSequenceProgram zs)
      = List.ofFn fun i : Fin (2 ^ zs.length) =>
          clusterSeqProgramLeafGen zs ((bitVecEquiv zs.length).symm i) := by
  rw [clusterSequenceProgram, observedKrausLeaves_prependSteps, clusterSeqLoopFin_leaves,
    clusterSeqFullGate_one, List.map_ofFn]
  have hqc : QueryCount (clusterSequenceResourceCircuit zs.length) = 0 := by
    show QueryCount (relabelCircuit (bitVecEquiv (zs.length + 1))
      (clusterSeqResourceCircuitB zs.length)) = 0
    rw [(relabelCircuit_legality_resources _ _).2.1, queryCount_resourceCircuitB]
  have hgc : GateCount (clusterSequenceResourceCircuit zs.length) = 2 * zs.length := by
    show GateCount (relabelCircuit (bitVecEquiv (zs.length + 1))
      (clusterSeqResourceCircuitB zs.length)) = 2 * zs.length
    rw [(relabelCircuit_legality_resources _ _).2.2.1, gateCount_resourceCircuitB]
  apply clusterSeqOfFn_congr
  intro i
  simp only [clusterSeqProgramLeafGen, hqc, hgc,
    show clusterSeqCircuitGate (clusterSequenceResourceCircuit zs.length)
      = clusterSequenceResourceGate zs.length from rfl]
  simp only [Function.comp_apply, ObservedKrausLeaf.prepend, Nat.add_zero,
    List.nil_append]

noncomputable def clusterSequenceLeaf (zs : List ℂ) (ω : Reg zs.length) :
    Fin (observedLeafCount (clusterSequenceProgram zs)) :=
  Fin.cast (observedLeafCount_program zs).symm (bitVecEquiv zs.length ω)

theorem clusterSequenceLeaf_eq (zs : List ℂ) (ω : Reg zs.length) :
    observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)
      = clusterSeqProgramLeafGen zs ω := by
  have hcount : observedLeafCount (clusterSequenceProgram zs) = 2 ^ zs.length :=
    observedLeafCount_program zs
  have hisLt := (bitVecEquiv zs.length ω).isLt
  show (observedKrausLeaves 1 (clusterSequenceProgram zs)).get
      (Fin.cast (observedKrausLeaves_length 1 (clusterSequenceProgram zs)).symm
        (Fin.cast hcount.symm (bitVecEquiv zs.length ω))) = _
  have hv : ((Fin.cast (observedKrausLeaves_length 1 (clusterSequenceProgram zs)).symm
        (Fin.cast hcount.symm (bitVecEquiv zs.length ω))) : ℕ)
      = (bitVecEquiv zs.length ω).val := by simp
  simp only [List.get_eq_getElem, clusterSequenceProgram_leaves]
  rw [List.getElem_ofFn (by simp only [List.length_ofFn]; omega)]
  apply congrArg (clusterSeqProgramLeafGen zs)
  refine Eq.trans ?_ (Equiv.symm_apply_apply (bitVecEquiv zs.length) ω)
  apply congrArg ((bitVecEquiv zs.length).symm)
  apply Fin.val_injective
  simp

theorem clusterSeqLoopLeafGen_gates : ∀ (zs : List ℂ) (ω : Reg zs.length),
    (clusterSeqLoopLeafGen zs ω).gates = 4 * zs.length - 1
  | [], _ => rfl
  | [z], _ => rfl
  | z :: w :: ws, ω => by
      have ih := clusterSeqLoopLeafGen_gates (w :: ws) (Fin.tail ω)
      simp only [clusterSeqLoopLeafGen]
      have hlen : (z :: w :: ws).length = (w :: ws).length + 1 := by
        simp only [List.length_cons]
      have hpos : 1 ≤ (w :: ws).length := by simp
      rw [ih, hlen, Nat.mul_add]
      omega

theorem clusterSeqLoopLeafGen_measurements : ∀ (zs : List ℂ) (ω : Reg zs.length),
    (clusterSeqLoopLeafGen zs ω).measurements = zs.length
  | [], _ => rfl
  | [z], _ => rfl
  | z :: w :: ws, ω => by
      have ih := clusterSeqLoopLeafGen_measurements (w :: ws) (Fin.tail ω)
      simp only [clusterSeqLoopLeafGen]
      have hlen : (z :: w :: ws).length = (w :: ws).length + 1 := by
        simp only [List.length_cons]
      omega

theorem clusterSeqLoopLeafGen_outcomes : ∀ (zs : List ℂ) (ω : Reg zs.length),
    (clusterSeqLoopLeafGen zs ω).outcomes
      = List.ofFn fun j : Fin zs.length => (2, (boolEquivFin2 (ω j)).val)
  | [], _ => rfl
  | [z], ω => by
      simp only [clusterSeqLoopLeafGen, clusterSeqOfFn_fin1]
  | z :: w :: ws, ω => by
      have ih := clusterSeqLoopLeafGen_outcomes (w :: ws) (Fin.tail ω)
      simp only [clusterSeqLoopLeafGen, ih, List.ofFn_succ]
      rfl

theorem clusterSeqRelabelGate_conjTranspose {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) :
    (relabelGate e A)ᴴ = relabelGate e Aᴴ := Matrix.conjTranspose_reindex e e A

theorem clusterSeqShiftGateFin_conjTranspose (m : ℕ) (U : Operator (2 ^ (m + 1))) :
    (clusterSeqShiftGateFin m U)ᴴ = clusterSeqShiftGateFin m Uᴴ := by
  unfold clusterSeqShiftGateFin clusterSeqShiftOp
  rw [clusterSeqRelabelGate_conjTranspose, clusterSeqRelabelGate_conjTranspose,
    tensorGate_conjTranspose, Matrix.conjTranspose_one,
    clusterSeqRelabelGate_conjTranspose]

theorem observedWellFormed_shiftObservedFin (m : ℕ) :
    ∀ P : ObservedCircuit (Fin (2 ^ (m + 1))), observedWellFormed P →
      observedWellFormed (clusterSeqShiftObservedFin m P)
  | .halt _, _ => trivial
  | .step (.gate _) next, h =>
      ⟨clusterSeqShiftGateFin_unitary m h.1, observedWellFormed_shiftObservedFin m next h.2⟩
  | .step .query next, h => observedWellFormed_shiftObservedFin m next h
  | .measure _ _ nexts, h =>
      fun o => observedWellFormed_shiftObservedFin m _ (h o)
  | .project P onFalse onTrue, h => by
      obtain ⟨hself, hidem⟩ := h.1
      refine ⟨⟨?_, ?_⟩, observedWellFormed_shiftObservedFin m _ h.2.1,
        observedWellFormed_shiftObservedFin m _ h.2.2⟩
      · show clusterSeqShiftGateFin m P * clusterSeqShiftGateFin m P = clusterSeqShiftGateFin m P
        rw [← clusterSeqShiftGateFin_mul, hself]
      · show (clusterSeqShiftGateFin m P)ᴴ = clusterSeqShiftGateFin m P
        rw [clusterSeqShiftGateFin_conjTranspose,
          show Pᴴ = star P from (Matrix.star_eq_conjTranspose P).symm, hidem]

theorem observedWellFormed_prependSteps {D : ℕ} (oracle : Operator D) (C : Circuit (Fin D))
    (P : ObservedCircuit (Fin D)) (hP : observedWellFormed P) (hC : IsUnitaryCircuit C) :
    observedWellFormed (clusterSeqPrependSteps oracle C P) := by
  induction C generalizing P with
  | nil => exact hP
  | cons s C ih =>
    cases s with
    | gate U =>
      exact ⟨hC U List.mem_cons_self,
        ih P hP fun V hV => hC V (List.mem_cons_of_mem _ hV)⟩
    | query => exact ih P hP fun V hV => hC V (List.mem_cons_of_mem _ hV)

theorem observedWellFormed_loopFin : ∀ (zs : List ℂ), (∀ z ∈ zs, ‖z‖ = 1) →
    observedWellFormed (clusterSeqLoopFin zs)
  | [], _ => trivial
  | [z], hzs =>
      ⟨clusterSeqPhaseFin_unitary (hzs z (by simp)) 1, clusterSeqHFin_unitary 1,
        fun _ => ⟨clusterSeqXFin_unitary 1 _ _, trivial⟩⟩
  | z :: w :: ws, hzs =>
      ⟨clusterSeqPhaseFin_unitary (hzs z (by simp)) _,
        clusterSeqHFin_unitary _,
        fun k => ⟨clusterSeqXFin_unitary _ _ _,
          ⟨clusterSeqZFin_unitary _ _ _,
            observedWellFormed_shiftObservedFin _ _
              (observedWellFormed_loopFin (w :: ws)
                (fun y hy => hzs y (by simp [hy])))⟩⟩⟩

theorem observedWellFormed_program {zs : List ℂ} (hzs : ∀ z ∈ zs, ‖z‖ = 1) :
    observedWellFormed (clusterSequenceProgram zs) := by
  refine observedWellFormed_prependSteps 1 _ _ (observedWellFormed_loopFin zs hzs) ?_
  show IsUnitaryCircuit (relabelCircuit (bitVecEquiv (zs.length + 1))
    (clusterSeqResourceCircuitB zs.length))
  exact (relabelCircuit_legality_resources (bitVecEquiv (zs.length + 1))
    (clusterSeqResourceCircuitB zs.length)).1.mpr (isUnitaryCircuit_resourceCircuitB zs.length)

theorem clusterSequenceLeaf_bijective (zs : List ℂ) :
    Function.Bijective (clusterSequenceLeaf zs) := by
  constructor
  · intro ω₁ ω₂ h
    have hv := congrArg
      (fun i : Fin (observedLeafCount (clusterSequenceProgram zs)) => (i : ℕ)) h
    simp only [clusterSequenceLeaf, Fin.val_cast] at hv
    exact (bitVecEquiv zs.length).injective (Fin.ext hv)
  · intro i
    have hc := observedLeafCount_program zs
    refine ⟨(bitVecEquiv zs.length).symm ⟨i.val, by omega⟩, ?_⟩
    apply Fin.val_injective
    simp only [clusterSequenceLeaf, Fin.val_cast, Equiv.apply_symm_apply]

theorem cluster_sequence_actual_program_and_feedback_cost :
    ∀ (zs : List ℂ), (∀ z ∈ zs, ‖z‖ = 1) →
      observedWellFormed (clusterSequenceProgram zs) ∧
      observedLeafCount (clusterSequenceProgram zs) = 2 ^ zs.length ∧
      Function.Bijective (clusterSequenceLeaf zs) ∧
      (∀ ω : Reg zs.length,
        (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).accepted = true ∧
        (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).queries = 0 ∧
        (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).gates
          = 6 * zs.length - 1 ∧
        (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).measurements
          = zs.length ∧
        (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).outcomes =
          List.ofFn fun j : Fin zs.length => (2, (boolEquivFin2 (ω j)).val)) := by
  intro zs hzs
  refine ⟨observedWellFormed_program hzs, observedLeafCount_program zs,
    clusterSequenceLeaf_bijective zs, fun ω => ?_⟩
  rw [clusterSequenceLeaf_eq]
  refine ⟨clusterSeqLoopLeafGen_accepted zs ω, clusterSeqLoopLeafGen_queries zs ω, ?_,
    clusterSeqLoopLeafGen_measurements zs ω, clusterSeqLoopLeafGen_outcomes zs ω⟩
  show (clusterSeqLoopLeafGen zs ω).gates + 2 * zs.length = 6 * zs.length - 1
  rw [clusterSeqLoopLeafGen_gates zs ω]
  omega

def clusterSequenceMessage {n : ℕ} (ω : Reg n) : List Bool := List.ofFn ω

theorem cluster_sequence_classical_message_history :
    (∀ (n : ℕ) (ω : Reg n), clusterSequenceMessage ω = List.ofFn ω ∧
      (clusterSequenceMessage ω).length = n) ∧
    (∀ n : ℕ, Function.Injective (clusterSequenceMessage (n := n))) ∧
    (∀ (zs : List ℂ) (ω : Reg zs.length),
      (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).outcomes =
        (clusterSequenceMessage ω).map (fun b => (2, (boolEquivFin2 b).val))) := by
  refine ⟨fun n ω => ⟨rfl, List.length_ofFn⟩, fun n => ?_, fun zs ω => ?_⟩
  · intro ω₁ ω₂ h
    simp only [clusterSequenceMessage] at h
    funext j
    have hj1 : j.val < (List.ofFn ω₁).length := by simp
    have hj2 : j.val < (List.ofFn ω₂).length := by simp
    simp only [← List.getElem_ofFn hj1, ← List.getElem_ofFn hj2, h]
  · show (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).outcomes
        = (List.ofFn ω).map (fun b => (2, (boolEquivFin2 b).val))
    rw [clusterSequenceLeaf_eq, List.map_ofFn]
    simp only [clusterSeqProgramLeafGen, ObservedKrausLeaf.prepend, List.nil_append]
    exact clusterSeqLoopLeafGen_outcomes zs ω

noncomputable def clusterSeqLeafOpLoopB : (zs : List ℂ) → ∀ _ω : Reg zs.length,
    Matrix (Reg (zs.length + 1)) (Reg (zs.length + 1)) ℂ
  | [], _ => 1
  | [z], ω =>
      clusterSeqOneBitB 1 ⟨1, by omega⟩ (if ω 0 then PauliX else 1)
        * Projector (Finset.univ.filter (fun x : Reg 2 => x 0 = ω 0))
        * clusterSeqOneBitB 1 0 Hadamard * clusterSeqOneBitB 1 0 (clusterSeqPhaseB z)
  | z :: w :: ws, ω =>
      clusterSeqShiftOp ((w :: ws).length) (clusterSeqLeafOpLoopB (w :: ws) (Fin.tail ω))
        * clusterSeqOneBitB (z :: w :: ws).length
            ⟨2, by simp only [List.length_cons]; omega⟩ (if ω 0 then PauliZ else 1)
        * clusterSeqOneBitB (z :: w :: ws).length
            ⟨1, by simp only [List.length_cons]; omega⟩ (if ω 0 then PauliX else 1)
        * Projector (Finset.univ.filter (fun x : Reg ((z :: w :: ws).length + 1) => x 0 = ω 0))
        * clusterSeqOneBitB (z :: w :: ws).length 0 Hadamard
        * clusterSeqOneBitB (z :: w :: ws).length 0 (clusterSeqPhaseB z)

theorem clusterSeqProjectorFin_eq (m : ℕ) (b : Bool) :
    Projector (Finset.univ.filter (fun r : Fin (2 ^ (m + 1)) =>
        clusterSeqLabelFin m r = boolEquivFin2 b))
      = relabelGate (bitVecEquiv (m + 1))
        (Projector (Finset.univ.filter (fun x : Reg (m + 1) => x 0 = b))) := by
  ext r r'
  have hiff : ∀ q : Fin (2 ^ (m + 1)),
      (q ∈ Finset.univ.filter (fun r => clusterSeqLabelFin m r = boolEquivFin2 b)
        ↔ (bitVecEquiv (m + 1)).symm q
            ∈ Finset.univ.filter (fun x : Reg (m + 1) => x 0 = b)) := by
    intro q
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    show clusterSeqLabelFin m q = boolEquivFin2 b ↔ _ = b
    unfold clusterSeqLabelFin
    constructor
    · intro hh
      have := congrArg (boolEquivFin2.symm) hh
      simpa using! this
    · intro hh
      simpa using! congrArg boolEquivFin2 hh
  unfold relabelGate Projector
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases h : r' = r
  · subst h
    by_cases hh : r' ∈ Finset.univ.filter (fun r => clusterSeqLabelFin m r = boolEquivFin2 b)
    · rw [if_pos hh, if_pos rfl, if_pos ((hiff r').mp hh), if_pos rfl]
    · rw [if_neg hh, if_pos rfl, if_neg (fun hb => hh ((hiff r').mpr hb)), if_pos rfl]
  · rw [if_neg (fun hc => h hc.symm),
      if_neg (fun hc => h (Equiv.injective ((bitVecEquiv (m + 1)).symm) hc).symm)]

theorem clusterSeqRelabelGate_merge6 {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B C D F G : Matrix I I ℂ) :
    relabelGate e A * relabelGate e B * relabelGate e C * relabelGate e D
        * relabelGate e F * relabelGate e G
      = relabelGate e (A * B * C * D * F * G) := by
  rw [← CircuitRelabel.relabelGate_mul, ← CircuitRelabel.relabelGate_mul,
    ← CircuitRelabel.relabelGate_mul, ← CircuitRelabel.relabelGate_mul,
    ← CircuitRelabel.relabelGate_mul]

theorem clusterSeqRelabelGate_merge4 {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B C D : Matrix I I ℂ) :
    relabelGate e A * relabelGate e B * relabelGate e C * relabelGate e D
      = relabelGate e (A * B * C * D) := by
  rw [← CircuitRelabel.relabelGate_mul, ← CircuitRelabel.relabelGate_mul,
    ← CircuitRelabel.relabelGate_mul]

set_option maxHeartbeats 1000000 in

theorem clusterSeqLoopLeafGen_operator : ∀ (zs : List ℂ) (ω : Reg zs.length),
    (clusterSeqLoopLeafGen zs ω).operator
      = relabelGate (bitVecEquiv (zs.length + 1)) (clusterSeqLeafOpLoopB zs ω)
  | [], _ => by
      simp only [clusterSeqLoopLeafGen, clusterSeqLeafOpLoopB, CircuitRelabel.relabelGate_one]
  | [z], ω => by
      simp only [clusterSeqLoopLeafGen, clusterSeqXFin, clusterSeqHFin, clusterSeqPhaseFin,
        clusterSeqOneBitFin, clusterSeqLeafOpLoopB]
      rw [clusterSeqProjectorFin_eq 1 (ω 0), clusterSeqRelabelGate_merge4]
      congr 1
      rw [Equiv.symm_apply_apply]
  | z :: w :: ws, ω => by
      simp only [clusterSeqLoopLeafGen, clusterSeqXFin, clusterSeqZFin, clusterSeqHFin,
        clusterSeqPhaseFin, clusterSeqOneBitFin, clusterSeqLeafOpLoopB]
      rw [clusterSeqLoopLeafGen_operator (w :: ws) (Fin.tail ω),
        clusterSeqShiftGateFin_relabel, clusterSeqProjectorFin_eq _ (ω 0)]
      have hE : ∀ M : Matrix (Reg ((z :: w :: ws).length + 1))
            (Reg ((z :: w :: ws).length + 1)) ℂ,
          relabelGate (bitVecEquiv ((w :: ws).length + 2)) M
            = relabelGate (bitVecEquiv ((z :: w :: ws).length + 1)) M := fun _ => rfl
      rw [hE _, clusterSeqRelabelGate_merge6, Equiv.symm_apply_apply]

def clusterSequenceRegisterEquiv (n : ℕ) : Reg n × Bool ≃ Fin (2 ^ (n + 1)) :=
  (regSuccEquiv n).symm.trans (bitVecEquiv (n + 1))

theorem clusterSeqResourceGateB_zero : clusterSeqResourceGateB 0 = 1 := by
  show clusterSeqCircuitGate (clusterSeqResourceCircuitB 0) = 1
  simp only [clusterSeqResourceCircuitB, clusterSeqResourceHB, clusterSeqResourceCzB]
  show clusterSeqCircuitGate (List.ofFn (fun j : Fin 0 => _) ++ List.ofFn (fun j : Fin 0 => _)) = 1
  show clusterSeqCircuitGate ([] : Circuit (Reg 1)) = 1
  rfl

theorem clusterSeqProgramLeaf_operator {zs : List ℂ} (ω : Reg zs.length) :
    (clusterSeqProgramLeafGen zs ω).operator
      = relabelGate (bitVecEquiv (zs.length + 1))
        (clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length) := by
  show (clusterSeqLoopLeafGen zs ω).operator * clusterSequenceResourceGate zs.length = _
  rw [clusterSeqLoopLeafGen_operator zs ω]
  show relabelGate (bitVecEquiv (zs.length + 1)) (clusterSeqLeafOpLoopB zs ω)
      * clusterSeqCircuitGate (clusterSequenceResourceCircuit zs.length) = _
  rw [show clusterSeqCircuitGate (clusterSequenceResourceCircuit zs.length)
      = relabelGate (bitVecEquiv (zs.length + 1)) (clusterSeqResourceGateB zs.length) from by
      show clusterSeqCircuitGate (relabelCircuit (bitVecEquiv (zs.length + 1))
        (clusterSeqResourceCircuitB zs.length))
        = relabelGate (bitVecEquiv (zs.length + 1)) (clusterSeqCircuitGate (clusterSeqResourceCircuitB zs.length))
      rw [clusterSeqCircuitGate_relabel]]
  rw [← CircuitRelabel.relabelGate_mul]

theorem clusterSeqSum_cons {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Reg (m + 2) → M) :
    ∑ y : Reg (m + 2), g y = ∑ b : Bool, ∑ t : Reg (m + 1), g (Fin.cons b t) := by
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 2) => Bool)).symm g
      (fun p => g (Fin.cons p.1 p.2)) (fun y => by
        show g y = g (Fin.cons (y 0) (Fin.tail y))
        rw [Fin.cons_self_tail])]
  rw [Fintype.sum_prod_type]

theorem clusterSeqSupport_zero {m : ℕ} (y : Reg (m + 2)) (b : Bool) (t : Reg (m + 1)) :
    (∀ k : Fin (m + 2), k ≠ (0 : Fin (m + 2)) → y k = (Fin.cons b t : Reg (m + 2)) k) ↔
      Fin.tail y = t := by
  constructor
  · intro h
    funext k'
    exact h k'.succ (by simp)
  · intro h k hk
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · exact absurd rfl hk
    · rw [Fin.cons_succ]
      exact congrFun h k'

theorem clusterSeqSupport_one {m : ℕ} (y : Reg (m + 2)) (b : Bool) (t : Reg (m + 1)) :
    (∀ k : Fin (m + 2), k ≠ (1 : Fin (m + 2)) → y k = (Fin.cons b t : Reg (m + 2)) k) ↔
      (y (0 : Fin (m + 2)) = b ∧ Fin.tail (Fin.tail y) = Fin.tail t) := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), ?_⟩
    funext k'
    exact h k'.succ.succ
      (fun hc => Fin.succ_ne_zero k'
        (Fin.succ_injective _ (show k'.succ.succ = (0 : Fin (m + 1)).succ from hc)))
  · rintro ⟨hy0, htt⟩ k hk
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · exact hy0
    · rcases Fin.eq_zero_or_eq_succ k' with rfl | ⟨k'', rfl⟩
      · exact absurd rfl hk
      · rw [Fin.cons_succ]
        exact congrFun htt k''

theorem clusterSeqOneBitB_permMatrix (n : ℕ) (j : Fin (n + 1)) (σ : Bool → Bool) :
    clusterSeqOneBitB n j (permMatrix σ)
      = permMatrix (fun x : Reg (n + 1) => Function.update x j (σ (x j))) := by
  ext x y
  simp only [clusterSeqOneBitB, Matrix.of_apply, permMatrix, Matrix.of_apply]
  by_cases hoff : ∀ k : Fin (n + 1), k ≠ j → x k = y k
  · rw [if_pos hoff]
    by_cases hxj : x j = σ (y j)
    · have hxe : x = Function.update y j (σ (y j)) := by
        funext k
        by_cases hkj : k = j
        · rw [hkj, hxj, Function.update_self]
        · rw [Function.update_of_ne hkj, hoff k hkj]
      rw [hxj, hxe]
      simp
    · have hxn : x ≠ Function.update y j (σ (y j)) := by
        intro hc
        exact hxj ((congrFun hc j).trans (by simp))
      rw [if_neg hxj, if_neg hxn]
  · rw [if_neg hoff, if_neg]
    intro hc
    apply hoff
    intro k hkj
    have hkc := congrFun hc k
    rw [Function.update_of_ne hkj] at hkc
    exact hkc

theorem clusterSeqOneBitB_Xchoice (n : ℕ) (j : Fin (n + 1)) (a : Bool) :
    clusterSeqOneBitB n j (if a then PauliX else 1)
      = permMatrix (fun x : Reg (n + 1) => if a then Function.update x j !(x j) else x) := by
  cases a
  · show clusterSeqOneBitB n j (1 : Matrix Bool Bool ℂ)
        = permMatrix (fun x : Reg (n + 1) => x)
    rw [clusterSeqOneBitB_one]
    ext x y
    simp [permMatrix, Matrix.one_apply]
  · show clusterSeqOneBitB n j (permMatrix Bool.not)
        = permMatrix (fun x : Reg (n + 1) => Function.update x j !(x j))
    rw [clusterSeqOneBitB_permMatrix]

theorem clusterSeqOneBitB_Zchoice (n : ℕ) (j : Fin (n + 1)) (a : Bool) :
    clusterSeqOneBitB n j (if a then PauliZ else 1)
      = Matrix.diagonal (fun x : Reg (n + 1) => if a && x j then (-1 : ℂ) else 1) := by
  cases a
  · show clusterSeqOneBitB n j (1 : Matrix Bool Bool ℂ)
        = Matrix.diagonal (fun _ : Reg (n + 1) => (1 : ℂ))
    rw [clusterSeqOneBitB_one, Matrix.diagonal_one]
  · show clusterSeqOneBitB n j (Matrix.diagonal fun b : Bool => if b then (-1 : ℂ) else 1)
        = Matrix.diagonal (fun x : Reg (n + 1) => if x j then (-1 : ℂ) else 1)
    rw [clusterSeqOneBitB_diagonal]

theorem clusterSeqOneBitB_Xchoice_mul_self (n : ℕ) (j : Fin (n + 1)) (a : Bool) :
    clusterSeqOneBitB n j (if a then PauliX else 1)
      * clusterSeqOneBitB n j (if a then PauliX else 1) = 1 := by
  rw [clusterSeqOneBitB_mul]
  cases a
  · show clusterSeqOneBitB n j ((1 : Matrix Bool Bool ℂ) * 1) = 1
    rw [Matrix.one_mul, clusterSeqOneBitB_one]
  · show clusterSeqOneBitB n j (PauliX * PauliX) = 1
    have hX : PauliX * PauliX = 1 := by
      show (permMatrix Bool.not : Matrix Bool Bool ℂ) * permMatrix Bool.not = 1
      exact permMatrix_mul_self Bool.not_not
    rw [hX, clusterSeqOneBitB_one]

theorem clusterSeqXZ_czB_transport {m : ℕ} (hm : 1 ≤ m) (a : Bool) :
    clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)
      * clusterSeqOneBitB m ⟨1, by omega⟩ (if a then PauliZ else 1)
      * clusterSeqCzB m ⟨0, by omega⟩
      = clusterSeqCzB m ⟨0, by omega⟩
        * clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1) := by
  have h4 : clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)
      * clusterSeqOneBitB m ⟨1, by omega⟩ (if a then PauliZ else 1)
      * clusterSeqCzB m ⟨0, by omega⟩
      * clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)
      = clusterSeqCzB m ⟨0, by omega⟩ := by
    cases a
    · show clusterSeqOneBitB m ⟨0, by omega⟩ (1 : Matrix Bool Bool ℂ)
          * clusterSeqOneBitB m ⟨1, by omega⟩ (1 : Matrix Bool Bool ℂ)
          * clusterSeqCzB m ⟨0, by omega⟩
          * clusterSeqOneBitB m ⟨0, by omega⟩ (1 : Matrix Bool Bool ℂ) = _
      simp only [clusterSeqOneBitB_one, Matrix.one_mul, Matrix.mul_one]
    · show clusterSeqOneBitB m ⟨0, by omega⟩ PauliX
          * clusterSeqOneBitB m ⟨1, by omega⟩ PauliZ * clusterSeqCzB m ⟨0, by omega⟩
          * clusterSeqOneBitB m ⟨0, by omega⟩ PauliX = _
      have hX : clusterSeqOneBitB m ⟨0, by omega⟩ PauliX
          = permMatrix (fun x : Reg (m + 1) =>
              Function.update x ⟨0, by omega⟩ !(x ⟨0, by omega⟩)) :=
        clusterSeqOneBitB_permMatrix m ⟨0, by omega⟩ Bool.not
      have hZ : clusterSeqOneBitB m ⟨1, by omega⟩ PauliZ
          = Matrix.diagonal (fun x : Reg (m + 1) => if x ⟨1, by omega⟩ then (-1 : ℂ) else 1) :=
        clusterSeqOneBitB_Zchoice m ⟨1, by omega⟩ true
      have hinv : Function.Involutive
          (fun x : Reg (m + 1) => Function.update x ⟨0, by omega⟩ !(x ⟨0, by omega⟩)) := by
        intro x
        simp
      have hCz : clusterSeqCzB m ⟨0, by omega⟩ = Matrix.diagonal
          (fun x : Reg (m + 1) => if x ⟨0, by omega⟩ && x ⟨1, by omega⟩ then (-1 : ℂ) else 1) :=
        rfl
      have hZC : clusterSeqOneBitB m ⟨1, by omega⟩ PauliZ
          * Matrix.diagonal (fun x : Reg (m + 1) =>
              if x ⟨0, by omega⟩ && x ⟨1, by omega⟩ then (-1 : ℂ) else 1)
          = Matrix.diagonal (fun x : Reg (m + 1) =>
              (if x ⟨1, by omega⟩ then (-1 : ℂ) else 1)
                * (if x ⟨0, by omega⟩ && x ⟨1, by omega⟩ then (-1 : ℂ) else 1)) := by
        rw [hZ, Matrix.diagonal_mul_diagonal]
      rw [Matrix.mul_assoc (clusterSeqOneBitB m ⟨0, by omega⟩ PauliX)
          (clusterSeqOneBitB m ⟨1, by omega⟩ PauliZ) (clusterSeqCzB m ⟨0, by omega⟩),
        hCz, hX, hZC, permMatrix_mul_diagonal_permMatrix _ hinv _]
      have h1 : ∀ x : Reg (m + 1),
          (Function.update x ⟨0, by omega⟩ !(x ⟨0, by omega⟩)) ⟨1, by omega⟩ = x ⟨1, by omega⟩ :=
        fun x => by simp
      have h0 : ∀ x : Reg (m + 1),
          (Function.update x ⟨0, by omega⟩ !(x ⟨0, by omega⟩)) ⟨0, by omega⟩
            = !(x ⟨0, by omega⟩) :=
        fun x => by simp
      have hcomp : (fun x : Reg (m + 1) =>
            (if x ⟨1, by omega⟩ then (-1 : ℂ) else 1)
              * (if x ⟨0, by omega⟩ && x ⟨1, by omega⟩ then (-1 : ℂ) else 1))
          ∘ (fun x : Reg (m + 1) =>
              Function.update x ⟨0, by omega⟩ !(x ⟨0, by omega⟩))
          = fun x : Reg (m + 1) =>
            if x ⟨0, by omega⟩ && x ⟨1, by omega⟩ then (-1 : ℂ) else 1 := by
        funext x
        simp only [Function.comp_apply]
        rw [h1 x, h0 x]
        cases hx0 : x ⟨0, by omega⟩ <;> cases hx1 : x ⟨1, by omega⟩ <;> simp
      rw [hcomp]

  have key : (clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)
      * clusterSeqOneBitB m ⟨1, by omega⟩ (if a then PauliZ else 1)
      * clusterSeqCzB m ⟨0, by omega⟩
      * clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1))
    * clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)
      = clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)
        * clusterSeqOneBitB m ⟨1, by omega⟩ (if a then PauliZ else 1)
        * clusterSeqCzB m ⟨0, by omega⟩ := by
    rw [Matrix.mul_assoc _ _ _, clusterSeqOneBitB_Xchoice_mul_self, Matrix.mul_one]
  conv_rhs => rw [← h4]
  rw [key]

theorem clusterSeqOneBitB_diagonal_mul_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → ℂ) (e : I → ℂ) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem clusterSeqZchoice_mul_diagonal (n : ℕ) (j : Fin (n + 1)) (a : Bool)
    (d : Reg (n + 1) → ℂ) :
    clusterSeqOneBitB n j (if a then PauliZ else 1) * Matrix.diagonal d
      = Matrix.diagonal d * clusterSeqOneBitB n j (if a then PauliZ else 1) := by
  rw [clusterSeqOneBitB_Zchoice, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem clusterSeqFin01_ne (n : ℕ) : (0 : Fin (n + 2)) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

theorem clusterSeqComm3 {I : Type*} [Fintype I] [DecidableEq I] (Z P Q R : Matrix I I ℂ)
    (h1 : Z * P = P * Z) (h2 : Z * Q = Q * Z) (h3 : Z * R = R * Z) :
    Z * (P * Q * R) = P * Q * R * Z := by
  rw [← Matrix.mul_assoc Z (P * Q) R, ← Matrix.mul_assoc Z P Q, h1,
    Matrix.mul_assoc P Z Q, h2, Matrix.mul_assoc P (Q * Z) R,
    Matrix.mul_assoc Q Z R, h3, ← Matrix.mul_assoc P Q (R * Z),
    Matrix.mul_assoc (P * Q) R Z]

theorem clusterSeqTransportChain {I : Type*} [Fintype I] [DecidableEq I]
    (X Z S C H : Matrix I I ℂ)
    (hZS : Z * S = S * Z) (hXS : X * S = S * X)
    (hXZC : X * Z * C = C * X) (hXH : X * H = H * X) :
    X * Z * (S * C * H) = S * C * H * X := by
  rw [← Matrix.mul_assoc (X * Z) (S * C) H, ← Matrix.mul_assoc (X * Z) S C,
    Matrix.mul_assoc X Z S, hZS, ← Matrix.mul_assoc X S Z, hXS,
    Matrix.mul_assoc S X Z, Matrix.mul_assoc S (X * Z) C, hXZC,
    ← Matrix.mul_assoc S C X, Matrix.mul_assoc (S * C) X H, hXH,
    ← Matrix.mul_assoc (S * C) H X]

theorem clusterSeqZa0_commute_resource : ∀ (n : ℕ) (a : Bool),
    clusterSeqOneBitB n (0 : Fin (n + 1)) (if a then PauliZ else 1)
      * clusterSeqResourceGateB n
      = clusterSeqResourceGateB n
        * clusterSeqOneBitB n ⟨0, by omega⟩ (if a then PauliZ else 1)
  | 0, a => by
      rw [clusterSeqResourceGateB_zero]
      simp only [Matrix.one_mul, Matrix.mul_one]
      rfl
  | n + 1, a => by
      simp only [clusterSeqResourceGateB_succ]
      exact clusterSeqComm3 _ _ _ _
        (clusterSeqOneBitB_zero_mul_shiftOp n _ _)
        (clusterSeqZchoice_mul_diagonal (n + 1) (0 : Fin (n + 2)) a _)
        (clusterSeqOneBitB_commute (n + 1) (0 : Fin (n + 2)) (1 : Fin (n + 2))
          (clusterSeqFin01_ne n) _ Hadamard)

theorem clusterSeqXZ_resource_transport (n : ℕ) (a : Bool) :
    clusterSeqOneBitB (n + 1) (0 : Fin (n + 2)) (if a then PauliX else 1)
      * clusterSeqOneBitB (n + 1) (1 : Fin (n + 2)) (if a then PauliZ else 1)
      * clusterSeqResourceGateB (n + 1)
      = clusterSeqResourceGateB (n + 1)
        * clusterSeqOneBitB (n + 1) (0 : Fin (n + 2)) (if a then PauliX else 1) := by
  have hZSh : clusterSeqOneBitB (n + 1) (1 : Fin (n + 2)) (if a then PauliZ else 1)
      * clusterSeqShiftOp n (clusterSeqResourceGateB n)
      = clusterSeqShiftOp n (clusterSeqResourceGateB n)
        * clusterSeqOneBitB (n + 1) (1 : Fin (n + 2)) (if a then PauliZ else 1) := by
    rw [show clusterSeqOneBitB (n + 1) (1 : Fin (n + 2)) (if a then PauliZ else 1)
          = clusterSeqShiftOp n (clusterSeqOneBitB n (0 : Fin (n + 1)) (if a then PauliZ else 1))
          from (clusterSeqShiftOp_oneBitB n (0 : Fin (n + 1)) (if a then PauliZ else 1)).symm,
      ← clusterSeqShiftOp_mul,
      congrArg (clusterSeqShiftOp n) (clusterSeqZa0_commute_resource n a)]
    exact clusterSeqShiftOp_mul n _ _
  simp only [clusterSeqResourceGateB_succ]
  exact clusterSeqTransportChain _ _ _ _ _ hZSh
    (clusterSeqOneBitB_zero_mul_shiftOp n _ _)
    (show clusterSeqOneBitB (n + 1) (0 : Fin (n + 2)) (if a then PauliX else 1)
        * clusterSeqOneBitB (n + 1) (1 : Fin (n + 2)) (if a then PauliZ else 1)
        * clusterSeqCzB (n + 1) (0 : Fin (n + 1))
      = clusterSeqCzB (n + 1) (0 : Fin (n + 1))
        * clusterSeqOneBitB (n + 1) (0 : Fin (n + 2)) (if a then PauliX else 1)
      from clusterSeqXZ_czB_transport (m := n + 1) (by omega) a)
    (clusterSeqOneBitB_commute (n + 1) (0 : Fin (n + 2)) (1 : Fin (n + 2))
      (clusterSeqFin01_ne n) _ Hadamard)

theorem clusterSeqInitialFrameB_val (n : ℕ) (ψ : QState (Fin 2)) (y : Reg (n + 1)) :
    (clusterSeqInitialFrameB n *ᵥ ψ) y
      = ψ (boolEquivFin2 (y 0)) * (if Fin.tail y = ZeroStr n then (1 : ℂ) else 0) := by
  rw [clusterSeqInitialFrameB_mulVec]
  rfl

theorem clusterSeqRelabelFin2_back (U : Matrix Bool Bool ℂ) (ψ : QState (Fin 2)) :
    relabelState boolEquivFin2.symm (ApplyGate (relabelGate boolEquivFin2 U) ψ)
      = ApplyGate U (relabelState boolEquivFin2.symm ψ) := by
  have h := applyGate_relabelGate boolEquivFin2 U (relabelState boolEquivFin2.symm ψ)
  rw [show relabelState boolEquivFin2 (relabelState boolEquivFin2.symm ψ) = ψ
      from relabelState_relabelState boolEquivFin2.symm ψ] at h
  rw [h]
  exact relabelState_relabelState boolEquivFin2 _

theorem clusterSeqFrameX (n : ℕ) (a : Bool) (ψ : QState (Fin 2)) :
    clusterSeqOneBitB n (0 : Fin (n + 1)) (if a then PauliX else 1) *ᵥ
        (clusterSeqInitialFrameB n *ᵥ ψ)
      = clusterSeqInitialFrameB n *ᵥ
          ((relabelGate boolEquivFin2 (if a then PauliX else 1)) *ᵥ ψ) := by
  show ApplyGate (clusterSeqOneBitB n (0 : Fin (n + 1)) (if a then PauliX else 1))
      (clusterSeqInitialFrameB n *ᵥ ψ) = _
  have hDrop : clusterSeqDropEquiv n (0 : Fin (n + 1))
      = Fin.consEquiv (fun _ : Fin (n + 1) => Bool) := Fin.insertNthEquiv_zero _
  rw [clusterSeqOneBitB_eq_tensor, hDrop, clusterSeqInitialFrameB_mulVec,
    applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one, clusterSeqInitialFrameB_mulVec]
  rw [show relabelGate boolEquivFin2 (if a then PauliX else 1) *ᵥ ψ
      = ApplyGate (relabelGate boolEquivFin2 (if a then PauliX else 1)) ψ from rfl,
    clusterSeqRelabelFin2_back]

theorem clusterSeqMulVecAssoc {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq J]
    (M : Matrix I J ℂ) (N : Matrix J K ℂ) (v : QState K) :
    (M * N) *ᵥ v = M *ᵥ (N *ᵥ v) := by
  funext i
  show (∑ k : K, (M * N) i k * v k) = ∑ j : J, M i j * (∑ k : K, N j k * v k)
  rw [show (∑ k : K, (M * N) i k * v k) = ∑ k : K, ∑ j : J, M i j * N j k * v k from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.mul_apply, Finset.sum_mul],
    Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring))

theorem clusterSeqCzB0_mulVec (m : ℕ) (w : QState (Reg (m + 2))) (y : Reg (m + 2)) :
    (clusterSeqCzB (m + 1) (0 : Fin (m + 1)) *ᵥ w) y
      = (if y (0 : Fin (m + 2)) && y (1 : Fin (m + 2)) then (-1 : ℂ) else 1) * w y := by
  show (Matrix.diagonal (fun z : Reg (m + 2) => if z (0 : Fin (m + 2)) && z (1 : Fin (m + 2))
      then (-1 : ℂ) else 1) *ᵥ w) y = _
  rw [mulVec_diagonal]

theorem clusterSeqShiftOp_mulVec (m : ℕ) (W : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ)
    (v : QState (Reg (m + 2))) (x : Reg (m + 2)) :
    (clusterSeqShiftOp m W *ᵥ v) x
      = ∑ t : Reg (m + 1), W (Fin.tail x) t * v (Fin.cons (x 0) t) := by
  show (∑ y : Reg (m + 2), clusterSeqShiftOp m W x y * v y) = _
  simp only [clusterSeqShiftOp_entry]
  rw [clusterSeqSum_cons m]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [Finset.sum_eq_single (x (0 : Fin (m + 2)))]
  · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg (Ne.symm hb), zero_mul, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem clusterSeqH1Frame (m : ℕ) (φ : QState (Fin 2)) (y : Reg (m + 2)) :
    (clusterSeqOneBitB (m + 1) (1 : Fin (m + 2)) Hadamard
        *ᵥ (clusterSeqInitialFrameB (m + 1) *ᵥ φ)) y
      = (Real.sqrt 2 : ℂ)⁻¹ * φ (boolEquivFin2 (y 0))
        * (if Fin.tail (Fin.tail y) = ZeroStr m then (1 : ℂ) else 0) := by
  show (∑ z : Reg (m + 2),
      (if (∀ k : Fin (m + 2), k ≠ ⟨1, by omega⟩ → y k = z k)
        then Hadamard (y ⟨1, by omega⟩) (z ⟨1, by omega⟩) else 0)
      * ((clusterSeqInitialFrameB (m + 1) *ᵥ φ) z)) = _
  rw [clusterSeqSum_cons m]
  simp only [clusterSeqInitialFrameB_val, Fin.cons_zero, Fin.tail_cons]
  by_cases hcond : Fin.tail (Fin.tail y) = ZeroStr m
  · rw [if_pos hcond]
    rw [Finset.sum_eq_single (y (0 : Fin (m + 2)))]
    · rw [Finset.sum_eq_single (ZeroStr (m + 1))]
      · have hsupp : ∀ k : Fin (m + 2), k ≠ ⟨1, by omega⟩ →
            y k = (Fin.cons (y 0) (ZeroStr (m + 1)) : Reg (m + 2)) k :=
          (clusterSeqSupport_one y (y 0) (ZeroStr (m + 1))).mpr ⟨rfl, hcond⟩
        rw [if_pos hsupp,
          show (Fin.cons (y 0) (ZeroStr (m + 1)) : Reg (m + 2)) ⟨1, by omega⟩ = false
            from rfl,
          show Hadamard (y ⟨1, by omega⟩) false = (Real.sqrt 2 : ℂ)⁻¹ from by
            simp [Hadamard]]
        simp
      · intro t _ ht
        rw [if_neg ht, mul_zero, mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro t _
      have hns : ¬ (∀ k : Fin (m + 2), k ≠ ⟨1, by omega⟩ →
          y k = (Fin.cons b t : Reg (m + 2)) k) := by
        intro hs
        exact hb ((clusterSeqSupport_one y b t).mp hs).1.symm
      rw [if_neg hns, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hcond, mul_zero]
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t = ZeroStr (m + 1)
    · subst ht
      have hns : ¬ (∀ k : Fin (m + 2), k ≠ ⟨1, by omega⟩ →
          y k = (Fin.cons b (ZeroStr (m + 1)) : Reg (m + 2)) k) := by
        intro hs
        exact hcond ((clusterSeqSupport_one y b (ZeroStr (m + 1))).mp hs).2
      rw [if_neg hns, zero_mul]
    · rw [if_neg ht, mul_zero, mul_zero]

theorem clusterSeqResourceFirstStep (m : ℕ) (φ : QState (Fin 2)) (x : Reg (m + 2)) :
    (clusterSeqShiftOp m (clusterSeqResourceGateB m)
        *ᵥ (clusterSeqCzB (m + 1) (0 : Fin (m + 1))
          *ᵥ (clusterSeqOneBitB (m + 1) (1 : Fin (m + 2)) Hadamard
            *ᵥ (clusterSeqInitialFrameB (m + 1) *ᵥ φ)))) x
      = φ (boolEquivFin2 (x 0))
        * ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
            (fun j : Fin 2 => Hadamard (x 0) (boolEquivFin2.symm j))) (Fin.tail x) := by
  rw [clusterSeqShiftOp_mulVec]
  have hcz : ∀ t : Reg (m + 1),
      (clusterSeqCzB (m + 1) (0 : Fin (m + 1)) *ᵥ (clusterSeqOneBitB (m + 1) (1 : Fin (m + 2)) Hadamard
          *ᵥ (clusterSeqInitialFrameB (m + 1) *ᵥ φ))) (Fin.cons (x 0) t)
        = Hadamard (x 0) (t (0 : Fin (m + 1))) * φ (boolEquivFin2 (x 0))
          * (if Fin.tail t = ZeroStr m then (1 : ℂ) else 0) := by
    intro t
    rw [clusterSeqCzB0_mulVec, clusterSeqH1Frame, Fin.cons_zero, Fin.tail_cons,
      show (Fin.cons (x 0) t : Reg (m + 2)) (1 : Fin (m + 2)) = t (0 : Fin (m + 1))
        from rfl,
      show Hadamard (x (0 : Fin (m + 2))) (t (0 : Fin (m + 1)))
        = (Real.sqrt 2 : ℂ)⁻¹
          * (if x (0 : Fin (m + 2)) && t (0 : Fin (m + 1)) then (-1 : ℂ) else 1) from rfl]
    ring
  simp only [hcz]
  rw [clusterSeqMulVecAssoc,
    show (clusterSeqResourceGateB m *ᵥ
        (clusterSeqInitialFrameB m *ᵥ (fun j : Fin 2 => Hadamard (x 0) (boolEquivFin2.symm j))))
        (Fin.tail x)
      = ∑ t : Reg (m + 1), clusterSeqResourceGateB m (Fin.tail x) t
        * ((clusterSeqInitialFrameB m *ᵥ (fun j : Fin 2 => Hadamard (x 0) (boolEquivFin2.symm j))) t)
        from rfl,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [clusterSeqInitialFrameB_val]
  simp only [Equiv.symm_apply_apply]
  ring

theorem clusterSeqMulVec_sum_smul {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℂ)
    (cs : Bool → ℂ) (vs : Bool → QState J) (x : I) :
    (M *ᵥ (∑ b : Bool, cs b • vs b)) x = ∑ b : Bool, cs b * (M *ᵥ vs b) x := by
  show (∑ j : J, M x j * (∑ b : Bool, cs b • vs b) j)
      = ∑ b : Bool, cs b * (∑ j : J, M x j * vs b j)
  simp only [QState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => by
    exact Finset.sum_congr rfl (fun j _ => by ring))

theorem clusterSeqJ_mulVec (z : ℂ) (φ : QState (Fin 2)) (j : Fin 2) :
    (clusterJ z *ᵥ φ) j
      = (Real.sqrt 2 : ℂ)⁻¹ * (φ 0 + (if j = 0 then (1 : ℂ) else -1) * z * φ 1) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two, clusterJ_entry z j 0, clusterJ_entry z j 1]
  fin_cases j <;> simp <;> ring

theorem clusterSeqXchoiceFin_mulVec (a : Bool) (χ : QState (Fin 2)) (j : Fin 2) :
    (relabelGate boolEquivFin2 (if a then PauliX else 1) *ᵥ χ) j
      = χ (if a then (if j = 0 then (1 : Fin 2) else 0) else j) := by
  cases a
  · show (relabelGate boolEquivFin2 (1 : Matrix Bool Bool ℂ) *ᵥ χ) j = χ j
    rw [CircuitRelabel.relabelGate_one, Matrix.one_mulVec]
  · show (relabelGate boolEquivFin2 PauliX *ᵥ χ) j
        = χ (if j = 0 then (1 : Fin 2) else 0)
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, relabelGate,
        Matrix.reindex_apply, Matrix.submatrix_apply, PauliX, permMatrix,
        Matrix.of_apply, boolEquivFin2, mul_comm]

theorem clusterSeqFrameX' (n : ℕ) (a : Bool) (ψ : QState (Fin 2)) :
    clusterSeqOneBitB n ⟨0, by omega⟩ (if a then PauliX else 1) *ᵥ
        (clusterSeqInitialFrameB n *ᵥ ψ)
      = clusterSeqInitialFrameB n *ᵥ
          ((relabelGate boolEquivFin2 (if a then PauliX else 1)) *ᵥ ψ) :=
  clusterSeqFrameX n a ψ

theorem clusterSeqMeasureQ0_input (z : ℂ) (a : Bool) (φ : QState (Fin 2)) :
    (∑ b : Bool, (Hadamard a b * (if b then z else 1) * φ (boolEquivFin2 b)) •
        (fun j : Fin 2 => Hadamard b (boolEquivFin2.symm j)))
      = (Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2 (if a then PauliX else 1)
          *ᵥ (clusterJ z *ᵥ φ)) := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [clusterSeqXchoiceFin_mulVec, clusterSeqJ_mulVec]
  simp only [Fintype.sum_bool, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hadamard]
  cases a <;> fin_cases j <;>
    simp [boolEquivFin2, Fin.isValue] <;> ring

theorem clusterSeqMeasureQ0 (m : ℕ) (z : ℂ) (a : Bool) (φ : QState (Fin 2)) :
    (Projector (Finset.univ.filter (fun y : Reg (m + 2) => y (0 : Fin (m + 2)) = a))
        *ᵥ (clusterSeqOneBitB (m + 1) (0 : Fin (m + 2)) Hadamard
          *ᵥ (clusterSeqOneBitB (m + 1) (0 : Fin (m + 2)) (clusterSeqPhaseB z)
            *ᵥ (clusterSeqShiftOp m (clusterSeqResourceGateB m)
              *ᵥ (clusterSeqCzB (m + 1) (0 : Fin (m + 1))
                *ᵥ (clusterSeqOneBitB (m + 1) (1 : Fin (m + 2)) Hadamard
                  *ᵥ (clusterSeqInitialFrameB (m + 1) *ᵥ φ)))))))
      = relabelState (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
            ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
              ((Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2 (if a then PauliX else 1)
                *ᵥ (clusterJ z *ᵥ φ))))) := by
  funext x
  have hph : ∀ w : QState (Reg (m + 2)), ∀ y : Reg (m + 2),
      (clusterSeqOneBitB (m + 1) (0 : Fin (m + 2)) (clusterSeqPhaseB z) *ᵥ w) y
        = (if y (0 : Fin (m + 2)) then z else 1) * w y := by
    intro w y
    show (clusterSeqOneBitB (m + 1) (0 : Fin (m + 2))
        (Matrix.diagonal fun b : Bool => if b then z else 1) *ᵥ w) y = _
    rw [clusterSeqOneBitB_diagonal, mulVec_diagonal]
  have hH0 : ∀ w : QState (Reg (m + 2)),
      (clusterSeqOneBitB (m + 1) (0 : Fin (m + 2)) Hadamard *ᵥ w) x
        = ∑ b : Bool, Hadamard (x (0 : Fin (m + 2))) b
            * w (Fin.cons b (Fin.tail x)) := by
    intro w
    show (∑ y : Reg (m + 2),
        (if (∀ k : Fin (m + 2), k ≠ (0 : Fin (m + 2)) → x k = y k)
          then Hadamard (x (0 : Fin (m + 2))) (y (0 : Fin (m + 2))) else 0) * w y) = _
    rw [clusterSeqSum_cons m]
    simp only [Fin.cons_zero]
    have hinner : ∀ b : Bool,
        (∑ t : Reg (m + 1),
            (if (∀ k : Fin (m + 2), k ≠ (0 : Fin (m + 2)) →
                x k = (Fin.cons b t : Reg (m + 2)) k)
              then Hadamard (x (0 : Fin (m + 2))) b else 0)
            * w (Fin.cons b t))
        = Hadamard (x (0 : Fin (m + 2))) b * w (Fin.cons b (Fin.tail x)) := by
      intro b
      rw [Finset.sum_eq_single (Fin.tail x)]
      · simp only [clusterSeqSupport_zero x b (Fin.tail x)]
        simp
      · intro t _ ht
        simp only [clusterSeqSupport_zero x b t]
        rw [if_neg (fun hc => ht hc.symm), zero_mul]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    simp only [hinner]
  have hP : ∀ u : QState (Reg (m + 2)),
      (Projector (Finset.univ.filter (fun y : Reg (m + 2) => y 0 = a)) *ᵥ u) x
        = (if x (0 : Fin (m + 2)) = a then u x else 0) := by
    intro u
    have hd : ∀ y : Reg (m + 2),
        (if y ∈ Finset.univ.filter (fun y' : Reg (m + 2) => y' (0 : Fin (m + 2)) = a)
          then (1 : ℂ) else 0)
          = (if y (0 : Fin (m + 2)) = a then (1 : ℂ) else 0) := by
      intro y
      by_cases hy : y (0 : Fin (m + 2)) = a
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_pos hy]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg hy]
    show (Matrix.diagonal (fun i : Reg (m + 2) =>
        if i ∈ Finset.univ.filter (fun y' => y' (0 : Fin (m + 2)) = a)
          then (1 : ℂ) else 0) *ᵥ u) x = _
    rw [mulVec_diagonal, hd x]
    by_cases hx : x (0 : Fin (m + 2)) = a
    · rw [if_pos hx, one_mul, if_pos hx]
    · rw [if_neg hx, zero_mul, if_neg hx]
  have hv1 : ∀ b : Bool,
      (clusterSeqShiftOp m (clusterSeqResourceGateB m)
          *ᵥ (clusterSeqCzB (m + 1) (0 : Fin (m + 1))
            *ᵥ (clusterSeqOneBitB (m + 1) (1 : Fin (m + 2)) Hadamard
              *ᵥ (clusterSeqInitialFrameB (m + 1) *ᵥ φ)))) (Fin.cons b (Fin.tail x))
        = φ (boolEquivFin2 b)
          * ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
              (fun j : Fin 2 => Hadamard b (boolEquivFin2.symm j))) (Fin.tail x) := by
    intro b
    rw [clusterSeqResourceFirstStep m φ (Fin.cons b (Fin.tail x))]
    simp only [Fin.cons_zero, Fin.tail_cons]
  rw [hP, hH0]
  simp only [hph, hv1]
  by_cases hx : x (0 : Fin (m + 2)) = a
  · rw [if_pos hx, hx]
    show (∑ b : Bool, Hadamard a b
          * ((if b then z else 1)
            * (φ (boolEquivFin2 b)
              * ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
                  (fun j : Fin 2 => Hadamard b (boolEquivFin2.symm j))) (Fin.tail x))))
        = relabelState (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
            (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
              ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
                ((Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2 (if a then PauliX else 1)
                  *ᵥ (clusterJ z *ᵥ φ))))) x
    rw [show (∑ b : Bool, Hadamard a b
          * ((if b then z else 1)
            * (φ (boolEquivFin2 b)
              * ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
                  (fun j : Fin 2 => Hadamard b (boolEquivFin2.symm j))) (Fin.tail x))))
        = ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
            (∑ b : Bool, (Hadamard a b * (if b then z else 1) * φ (boolEquivFin2 b)) •
              (fun j : Fin 2 => Hadamard b (boolEquivFin2.symm j)))) (Fin.tail x) from by
        rw [clusterSeqMulVec_sum_smul]
        exact Finset.sum_congr rfl (fun b _ => by ring),
      clusterSeqMeasureQ0_input]
    show ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
        ((Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2 (if a then PauliX else 1)
          *ᵥ (clusterJ z *ᵥ φ)))) (Fin.tail x)
      = (if (x (0 : Fin (m + 2))) = a then (1 : ℂ) else 0)
        * ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
            ((Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2 (if a then PauliX else 1)
              *ᵥ (clusterJ z *ᵥ φ)))) (Fin.tail x)
    rw [if_pos hx]
    ring
  · rw [if_neg hx]
    show (0 : ℂ)
      = (if (x (0 : Fin (m + 2))) = a then (1 : ℂ) else 0)
        * ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
            ((Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2 (if a then PauliX else 1)
              *ᵥ (clusterJ z *ᵥ φ)))) (Fin.tail x)
    rw [if_neg hx, zero_mul]

theorem clusterSeqShiftOp_mulVec_tensor (m : ℕ) (W : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ)
    (v : QState (Reg (m + 1))) (b : Bool) :
    clusterSeqShiftOp m W *ᵥ relabelState (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket b) v)
      = relabelState (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket b) (W *ᵥ v)) := by
  show ApplyGate (relabelGate (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
      (TensorGate (1 : Matrix Bool Bool ℂ) W))
      (relabelState (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket b) v)) = _
  rw [applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  rfl

theorem clusterSeqTensorState_smul {I J : Type*} (c : ℂ) (ψ : QState I) (χ : QState J) :
    TensorState ψ (c • χ) = c • TensorState ψ χ := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

theorem clusterSeqXchoiceFin_mul_self (a : Bool) :
    relabelGate boolEquivFin2 (if a then PauliX else 1)
      * relabelGate boolEquivFin2 (if a then PauliX else 1) = 1 := by
  rw [← CircuitRelabel.relabelGate_mul]
  cases a
  · show relabelGate boolEquivFin2 ((1 : Matrix Bool Bool ℂ) * 1) = 1
    rw [Matrix.one_mul, CircuitRelabel.relabelGate_one]
  · show relabelGate boolEquivFin2 (PauliX * PauliX) = 1
    have hX : PauliX * PauliX = 1 := by
      show (permMatrix Bool.not : Matrix Bool Bool ℂ) * permMatrix Bool.not = 1
      exact permMatrix_mul_self Bool.not_not
    rw [hX, CircuitRelabel.relabelGate_one]

theorem clusterSeqXZ_resource_transport_m {m : ℕ} (hm : 1 ≤ m) (a : Bool) :
    clusterSeqOneBitB m (0 : Fin (m + 1)) (if a then PauliX else 1)
      * clusterSeqOneBitB m (1 : Fin (m + 1)) (if a then PauliZ else 1)
      * clusterSeqResourceGateB m
      = clusterSeqResourceGateB m
        * clusterSeqOneBitB m (0 : Fin (m + 1)) (if a then PauliX else 1) := by
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst hk
  exact clusterSeqXZ_resource_transport k a

theorem clusterSeqCorrectTail {m : ℕ} (hm : 1 ≤ m) (a : Bool) (ψ : QState (Fin 2)) :
    clusterSeqOneBitB (m + 1) ⟨2, by omega⟩ (if a then PauliZ else 1)
        *ᵥ (clusterSeqOneBitB (m + 1) ⟨1, by omega⟩ (if a then PauliX else 1)
          *ᵥ relabelState (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
              (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
                ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
                  ((Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2 (if a then PauliX else 1)
                    *ᵥ ψ)))))
      = relabelState (Fin.consEquiv (fun _ : Fin (m + 2) => Bool))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
            ((clusterSeqResourceGateB m * clusterSeqInitialFrameB m) *ᵥ
              ((Real.sqrt 2 : ℂ)⁻¹ • ψ))) := by
  have hX : clusterSeqOneBitB (m + 1) ⟨1, by omega⟩ (if a then PauliX else 1)
      = clusterSeqShiftOp m (clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)) :=
    (clusterSeqShiftOp_oneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)).symm
  have hZ : clusterSeqOneBitB (m + 1) ⟨2, by omega⟩ (if a then PauliZ else 1)
      = clusterSeqShiftOp m (clusterSeqOneBitB m ⟨1, by omega⟩ (if a then PauliZ else 1)) := by
    have h := clusterSeqShiftOp_oneBitB m ⟨1, by omega⟩ (if a then PauliZ else 1)
    exact h.symm
  have hmat : (clusterSeqOneBitB m ⟨1, by omega⟩ (if a then PauliZ else 1)
        * clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1))
        * (clusterSeqResourceGateB m * clusterSeqInitialFrameB m)
      = clusterSeqResourceGateB m
        * (clusterSeqOneBitB m ⟨0, by omega⟩ (if a then PauliX else 1)
          * clusterSeqInitialFrameB m) := by
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst hk
    rw [← Matrix.mul_assoc,
      clusterSeqOneBitB_commute (k + 1) ⟨1, by omega⟩ ⟨0, by omega⟩
        (Ne.symm (clusterSeqFin01_ne k)) _ _]
    rw [show clusterSeqOneBitB (k + 1) ⟨0, by omega⟩ (if a then PauliX else 1)
            * clusterSeqOneBitB (k + 1) ⟨1, by omega⟩ (if a then PauliZ else 1)
            * clusterSeqResourceGateB (k + 1)
          = clusterSeqResourceGateB (k + 1)
            * clusterSeqOneBitB (k + 1) ⟨0, by omega⟩ (if a then PauliX else 1)
          from clusterSeqXZ_resource_transport_m hm a, Matrix.mul_assoc]
  rw [hZ, hX, clusterSeqShiftOp_mulVec_tensor m _ _ a, clusterSeqShiftOp_mulVec_tensor m _ _ a,
    ← clusterSeqMulVecAssoc, ← clusterSeqMulVecAssoc, hmat, clusterSeqMulVecAssoc,
    clusterSeqMulVecAssoc,
    clusterSeqFrameX' m a ((Real.sqrt 2 : ℂ)⁻¹ • (relabelGate boolEquivFin2
      (if a then PauliX else 1) *ᵥ ψ)), ← clusterSeqMulVecAssoc,
    applyGate_smul', ← clusterSeqMulVecAssoc, clusterSeqXchoiceFin_mul_self, Matrix.one_mulVec]

theorem clusterSeqStep : ∀ (zs : List ℂ) (z : ℂ) (a : Bool) (ω' : Reg zs.length)
    (φ : QState (Fin 2)),
    (clusterSeqLeafOpLoopB (z :: zs) (Fin.cons a ω')
        * clusterSeqResourceGateB (zs.length + 1)) *ᵥ
      (clusterSeqInitialFrameB (zs.length + 1) *ᵥ φ)
      = relabelState (Fin.consEquiv (fun _ : Fin (zs.length + 2) => Bool))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
            ((clusterSeqLeafOpLoopB zs ω' * clusterSeqResourceGateB zs.length)
              *ᵥ (clusterSeqInitialFrameB zs.length *ᵥ
                ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ)))))
  | [], z, a, ω', φ => by
      have hR0 : clusterSeqResourceGateB 0 = 1 := clusterSeqResourceGateB_zero
      have hX1 : clusterSeqOneBitB 1 ⟨1, by omega⟩ (if a then PauliX else 1)
          = clusterSeqShiftOp 0 (clusterSeqOneBitB 0 (0 : Fin 1)
              (if a then PauliX else 1)) :=
        (clusterSeqShiftOp_oneBitB 0 (0 : Fin 1) (if a then PauliX else 1)).symm
      simp only [clusterSeqLeafOpLoopB, Fin.cons_zero, clusterSeqResourceGateB_succ,
        List.length_nil, Fin.succ_zero_eq_one]
      conv_lhs => repeat rw [clusterSeqMulVecAssoc]
      simp only [clusterSeqMeasureQ0]
      rw [hX1, clusterSeqShiftOp_mulVec_tensor 0 _ _ a,
        clusterSeqMulVecAssoc, ← clusterSeqMulVecAssoc, hR0, Matrix.mul_one, Matrix.one_mul,
        clusterSeqFrameX, applyGate_smul', ← clusterSeqMulVecAssoc,
        clusterSeqXchoiceFin_mul_self, Matrix.one_mulVec, Matrix.one_mulVec]
  | w :: ws, z, a, ω', φ => by
      simp only [clusterSeqLeafOpLoopB, Fin.cons_zero, Fin.tail_cons, List.length_cons]
      conv_lhs => repeat rw [clusterSeqMulVecAssoc]
      have hRdecomp : (clusterSeqResourceGateB (ws.length + 1 + 1)) *ᵥ
          (clusterSeqInitialFrameB (ws.length + 1 + 1) *ᵥ φ)
          = (clusterSeqShiftOp (ws.length + 1) (clusterSeqResourceGateB (ws.length + 1))
            *ᵥ (clusterSeqCzB (ws.length + 1 + 1) (0 : Fin (ws.length + 1 + 1))
              *ᵥ (clusterSeqOneBitB (ws.length + 1 + 1) (1 : Fin (ws.length + 1 + 2)) Hadamard
                *ᵥ (clusterSeqInitialFrameB (ws.length + 1 + 1) *ᵥ φ)))) := by
        rw [clusterSeqResourceGateB_succ (ws.length + 1), clusterSeqMulVecAssoc,
          clusterSeqMulVecAssoc, Fin.succ_zero_eq_one]
      rw [hRdecomp]
      have hB := clusterSeqMeasureQ0 (ws.length + 1) z a φ
      have hC := clusterSeqCorrectTail (m := ws.length + 1) (by omega) a (clusterJ z *ᵥ φ)
      have step2 := congrArg (fun u : QState (Reg ((w :: ws).length + 2)) =>
          clusterSeqOneBitB ((z :: w :: ws).length)
            ⟨1, by simp only [List.length_cons]; omega⟩ (if a then PauliX else 1) *ᵥ u) hB
      have step3 := congrArg (fun u : QState (Reg ((z :: w :: ws).length + 1)) =>
          clusterSeqOneBitB ((z :: w :: ws).length)
            ⟨2, by simp only [List.length_cons]; omega⟩ (if a then PauliZ else 1) *ᵥ u) step2
      have step5 : (clusterSeqShiftOp (ws.length + 1) (clusterSeqLeafOpLoopB (w :: ws) ω')
            *ᵥ relabelState (Fin.consEquiv (fun _ : Fin (ws.length + 1 + 2) => Bool))
              (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
                ((clusterSeqResourceGateB (ws.length + 1)
                  * clusterSeqInitialFrameB (ws.length + 1)) *ᵥ
                  ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ)))))
          = relabelState (Fin.consEquiv (fun _ : Fin (ws.length + 1 + 2) => Bool))
              (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
                ((clusterSeqLeafOpLoopB (w :: ws) ω'
                  * clusterSeqResourceGateB (ws.length + 1))
                  *ᵥ (clusterSeqInitialFrameB (ws.length + 1) *ᵥ
                    ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ))))) := by
        rw [clusterSeqShiftOp_mulVec_tensor, ← clusterSeqMulVecAssoc,
          ← Matrix.mul_assoc, clusterSeqMulVecAssoc]
      rw [hB, hC, clusterSeqShiftOp_mulVec_tensor, ← clusterSeqMulVecAssoc,
        ← Matrix.mul_assoc, clusterSeqMulVecAssoc]

theorem clusterSeqFrame0_val (χ : QState (Fin 2)) (y : Reg 1) :
    (clusterSeqInitialFrameB 0 *ᵥ χ) y = χ (boolEquivFin2 (y (0 : Fin 1))) := by
  rw [clusterSeqInitialFrameB_val]
  have ht : Fin.tail y = ZeroStr 0 := by
    funext j
    exact Fin.elim0 j
  rw [ht, if_pos rfl, mul_one]

theorem clusterSeqLeafPhysics : ∀ (zs : List ℂ), (∀ z ∈ zs, ‖z‖ = 1) →
    ∀ (ω : Reg zs.length) (φ : QState (Fin 2)),
      ApplyGate (clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length)
        (clusterSeqInitialFrameB zs.length *ᵥ φ)
        = fun x : Reg (zs.length + 1) =>
          if (fun j => x (Fin.castSucc j)) = ω then
            ((Real.sqrt 2 : ℂ)⁻¹) ^ zs.length
              * (clusterSequenceUnitary zs *ᵥ φ) (boolEquivFin2 (x (Fin.last zs.length)))
          else 0
  | [], _, ω, φ => by
      simp only [clusterSeqLeafOpLoopB, List.length_nil, clusterSeqResourceGateB_zero,
        applyGate_one, pow_zero, one_mul, clusterSequenceUnitary]
      rw [clusterSeqInitialFrameB_mulVec]
      funext x
      have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
      rw [hx]
      have hω : (fun j : Fin 0 => Fin.cons (x 0) (Fin.tail x) (Fin.castSucc j)) = ω :=
        funext fun j => Fin.elim0 j
      rw [if_pos hω]
      show TensorState (relabelState boolEquivFin2.symm φ) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0))
          ((Fin.consEquiv (fun _ : Fin 1 => Bool)).symm (Fin.cons (x 0) (Fin.tail x))) = _
      have hpair : (Fin.consEquiv (fun _ : Fin 1 => Bool)).symm (Fin.cons (x 0) (Fin.tail x))
          = (x 0, Fin.tail x) := rfl
      rw [hpair]
      show (relabelState boolEquivFin2.symm φ) (x 0)
          * (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0)) (Fin.tail x) = _
      have hz : (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0)) (Fin.tail x) = 1 := by
        show (if Fin.tail x = ZeroStr 0 then (1 : ℂ) else 0) = _
        rw [if_pos (funext fun j => Fin.elim0 j)]
      rw [hz, mul_one]
      show φ (boolEquivFin2 (x 0)) = (1 *ᵥ φ) (boolEquivFin2
          (Fin.cons (x 0) (Fin.tail x) (Fin.last 0)))
      rw [Matrix.one_mulVec, show Fin.last 0 = (0 : Fin 1) from rfl, Fin.cons_zero]
  | [z], hzs, ω, φ => by
      have hstep := clusterSeqStep [] z (ω (0 : Fin 1)) (Fin.tail ω) φ
      have hstep2 : (clusterSeqLeafOpLoopB [z] (Fin.cons (ω (0 : Fin 1)) (Fin.tail ω))
            * clusterSeqResourceGateB ([z].length))
            *ᵥ (clusterSeqInitialFrameB ([z].length) *ᵥ φ)
          = relabelState (Fin.consEquiv (fun _ : Fin ([z].length + 1) => Bool))
              (TensorState (Qatlib.Foundations.PureStateMath.Ket (ω (0 : Fin 1)))
                ((1 * clusterSeqResourceGateB ([] : List ℂ).length) *ᵥ
                  (clusterSeqInitialFrameB ([] : List ℂ).length *ᵥ
                    ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ))))) := hstep
      rw [show (ω : Reg ([z]).length) = Fin.cons (ω (0 : Fin 1)) (Fin.tail ω)
          from (Fin.cons_self_tail ω).symm]
      show ((clusterSeqLeafOpLoopB [z] (Fin.cons (ω (0 : Fin 1)) (Fin.tail ω))
            * clusterSeqResourceGateB ([z].length))
            *ᵥ (clusterSeqInitialFrameB ([z].length) *ᵥ φ)
          = fun x : Reg ([z].length + 1) =>
            if (fun j => x (Fin.castSucc j)) = Fin.cons (ω (0 : Fin 1)) (Fin.tail ω) then
              ((Real.sqrt 2 : ℂ)⁻¹) ^ ([z]).length
                * (clusterSequenceUnitary [z] *ᵥ φ)
                    (boolEquivFin2 (x (Fin.last ([z]).length)))
            else 0)
      rw [hstep2]
      funext x
      simp only [List.length_nil]
      rw [clusterSeqResourceGateB_zero, Matrix.one_mul]
      have hx : x = Fin.cons (x (0 : Fin 2)) (Fin.tail x) := (Fin.cons_self_tail x).symm
      rw [hx]
      show TensorState (Qatlib.Foundations.PureStateMath.Ket (ω (0 : Fin 1))) ((1 : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ
          (clusterSeqInitialFrameB 0 *ᵥ ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ))))
          ((Fin.consEquiv (fun _ : Fin 2 => Bool)).symm
            (Fin.cons (x (0 : Fin 2)) (Fin.tail x))) = _
      have hpair : (Fin.consEquiv (fun _ : Fin 2 => Bool)).symm
          (Fin.cons (x (0 : Fin 2)) (Fin.tail x)) = (x (0 : Fin 2), Fin.tail x) := rfl
      rw [hpair]
      show Qatlib.Foundations.PureStateMath.Ket (ω (0 : Fin 1)) (x (0 : Fin 2))
          * ((1 : Matrix (Reg 1) (Reg 1) ℂ) *ᵥ (clusterSeqInitialFrameB 0 *ᵥ
            ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ)))) (Fin.tail x) = _
      rw [Matrix.one_mulVec, clusterSeqFrame0_val, Pi.smul_apply, smul_eq_mul]
      have hk : Qatlib.Foundations.PureStateMath.Ket (ω (0 : Fin 1)) (x (0 : Fin 2))
          = if (x (0 : Fin 2)) = ω (0 : Fin 1) then (1 : ℂ) else 0 := rfl
      rw [hk]
      show ((if (x (0 : Fin 2)) = ω (0 : Fin 1) then (1 : ℂ) else 0)
          * ((Real.sqrt 2 : ℂ)⁻¹ * (clusterJ z *ᵥ φ)
            (boolEquivFin2 (Fin.tail x (0 : Fin 1)))))
        = (if (fun j : Fin 1 => Fin.cons (x (0 : Fin 2)) (Fin.tail x) (Fin.castSucc j))
              = Fin.cons (ω (0 : Fin 1)) (Fin.tail ω) then
            ((Real.sqrt 2 : ℂ)⁻¹) ^ ([z]).length * ((clusterSequenceUnitary [z]) *ᵥ φ)
              (boolEquivFin2 (Fin.cons (x (0 : Fin 2)) (Fin.tail x) (Fin.last 1)))
          else 0)
      have hfront : (fun j : Fin 1 => Fin.cons (x (0 : Fin 2)) (Fin.tail x) (Fin.castSucc j))
          = Fin.cons (ω (0 : Fin 1)) (Fin.tail ω) ↔ (x (0 : Fin 2)) = ω (0 : Fin 1) := by
        constructor
        · intro hc
          have h0 := congrFun hc (0 : Fin 1)
          simpa using! h0
        · intro hc
          funext j
          fin_cases j; simp [hc]
      by_cases hx0 : (x (0 : Fin 2)) = ω (0 : Fin 1)
      · rw [if_pos hx0, if_pos (hfront.mpr hx0), one_mul,
        show ((Real.sqrt 2 : ℂ)⁻¹) ^ ([z]).length = (Real.sqrt 2 : ℂ)⁻¹ from by
          rw [show ([z]).length = 1 from rfl, pow_one],
        show (clusterSequenceUnitary [z] : Operator 2) = 1 * clusterJ z from rfl,
        Matrix.one_mul]
        rfl
      · rw [if_neg hx0, if_neg (fun hc => hx0 (hfront.mp hc)), zero_mul]
  | z :: w :: ws, hzs, ω, φ => by
      have hstep := clusterSeqStep (w :: ws) z (ω (0 : Fin ((z :: w :: ws).length)))
        (Fin.tail ω) φ
      have hstep2 : (clusterSeqLeafOpLoopB (z :: w :: ws)
            (Fin.cons (ω (0 : Fin ((z :: w :: ws).length))) (Fin.tail ω))
            * clusterSeqResourceGateB ((z :: w :: ws).length))
            *ᵥ (clusterSeqInitialFrameB ((z :: w :: ws).length) *ᵥ φ)
          = relabelState (Fin.consEquiv (fun _ : Fin ((z :: w :: ws).length + 1) => Bool))
              (TensorState (Qatlib.Foundations.PureStateMath.Ket (ω (0 : Fin ((z :: w :: ws).length))))
                ((clusterSeqLeafOpLoopB (w :: ws) (Fin.tail ω)
                  * clusterSeqResourceGateB (w :: ws).length)
                  *ᵥ (clusterSeqInitialFrameB (w :: ws).length *ᵥ
                    ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ))))) := hstep
      rw [show (ω : Reg ((z :: w :: ws).length))
            = Fin.cons (ω (0 : Fin ((z :: w :: ws).length))) (Fin.tail ω)
          from (Fin.cons_self_tail ω).symm]
      show ((clusterSeqLeafOpLoopB (z :: w :: ws)
              (Fin.cons (ω (0 : Fin ((z :: w :: ws).length))) (Fin.tail ω))
              * clusterSeqResourceGateB ((z :: w :: ws).length))
            *ᵥ (clusterSeqInitialFrameB ((z :: w :: ws).length) *ᵥ φ)
          = fun x : Reg ((z :: w :: ws).length + 1) =>
            if (fun j => x (Fin.castSucc j))
                = Fin.cons (ω (0 : Fin ((z :: w :: ws).length))) (Fin.tail ω) then
              ((Real.sqrt 2 : ℂ)⁻¹) ^ ((z :: w :: ws).length)
                * ((clusterSequenceUnitary (z :: w :: ws)) *ᵥ φ)
                  (boolEquivFin2 (x (Fin.last ((z :: w :: ws).length))))
            else 0)
      rw [hstep2]
      have ih := clusterSeqLeafPhysics (w :: ws)
        (fun y hy => hzs y (List.mem_cons_of_mem _ hy))
        (Fin.tail ω) ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ))
      funext x
      have hx : x = Fin.cons (x (0 : Fin ((z :: w :: ws).length + 1))) (Fin.tail x) :=
        (Fin.cons_self_tail x).symm
      rw [hx]
      show (Qatlib.Foundations.PureStateMath.Ket (ω (0 : Fin ((z :: w :: ws).length)))
            (x (0 : Fin ((z :: w :: ws).length + 1)))
            * ((clusterSeqLeafOpLoopB (w :: ws) (Fin.tail ω)
                * clusterSeqResourceGateB (w :: ws).length)
                *ᵥ (clusterSeqInitialFrameB (w :: ws).length *ᵥ
                  ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ)))) (Fin.tail x)) = _
      rw [show ((clusterSeqLeafOpLoopB (w :: ws) (Fin.tail ω)
              * clusterSeqResourceGateB (w :: ws).length)
            *ᵥ (clusterSeqInitialFrameB (w :: ws).length *ᵥ
              ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ)))) (Fin.tail x)
          = (if (fun j : Fin (w :: ws).length => (Fin.tail x) (Fin.castSucc j)) = Fin.tail ω then
              ((Real.sqrt 2 : ℂ)⁻¹) ^ (w :: ws).length
                * ((clusterSequenceUnitary (w :: ws)) *ᵥ
                    ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ)))
                  (boolEquivFin2 ((Fin.tail x) (Fin.last (w :: ws).length)))
            else 0) from congrFun ih (Fin.tail x)]
      have hk : Qatlib.Foundations.PureStateMath.Ket (ω (0 : Fin ((z :: w :: ws).length)))
          (x (0 : Fin ((z :: w :: ws).length + 1)))
          = if (x (0 : Fin ((z :: w :: ws).length + 1)))
              = ω (0 : Fin ((z :: w :: ws).length)) then (1 : ℂ) else 0 := rfl
      rw [hk]
      show ((if (x (0 : Fin ((z :: w :: ws).length + 1)))
              = ω (0 : Fin ((z :: w :: ws).length)) then (1 : ℂ) else 0)
          * (if (fun j : Fin (w :: ws).length => (Fin.tail x) (Fin.castSucc j)) = Fin.tail ω then
              ((Real.sqrt 2 : ℂ)⁻¹) ^ (w :: ws).length
                * ((clusterSequenceUnitary (w :: ws)) *ᵥ
                    ((Real.sqrt 2 : ℂ)⁻¹ • (clusterJ z *ᵥ φ)))
                  (boolEquivFin2 ((Fin.tail x) (Fin.last (w :: ws).length)))
            else 0))
        = (if (fun j : Fin ((z :: w :: ws).length)
                => (Fin.cons (x (0 : Fin ((z :: w :: ws).length + 1))) (Fin.tail x))
                    (Fin.castSucc j))
              = Fin.cons (ω (0 : Fin ((z :: w :: ws).length))) (Fin.tail ω) then
            ((Real.sqrt 2 : ℂ)⁻¹) ^ ((z :: w :: ws).length)
              * ((clusterSequenceUnitary (z :: w :: ws)) *ᵥ φ)
                (boolEquivFin2 ((Fin.cons (x (0 : Fin ((z :: w :: ws).length + 1))) (Fin.tail x))
                  (Fin.last ((z :: w :: ws).length))))
          else 0)
      rw [show (clusterSequenceUnitary (z :: w :: ws))
          = clusterSequenceUnitary (w :: ws) * clusterJ z from rfl,
        show ((Real.sqrt 2 : ℂ)⁻¹) ^ ((z :: w :: ws).length)
          = ((Real.sqrt 2 : ℂ)⁻¹) ^ (w :: ws).length * (Real.sqrt 2 : ℂ)⁻¹ from by
            rw [show (z :: w :: ws).length = (w :: ws).length + 1 from rfl, pow_succ],
        clusterSeqMulVecAssoc, applyGate_smul']
      have hfront : (fun j : Fin ((z :: w :: ws).length)
                => (Fin.cons (x (0 : Fin ((z :: w :: ws).length + 1))) (Fin.tail x))
                  (Fin.castSucc j))
            = Fin.cons (ω (0 : Fin ((z :: w :: ws).length))) (Fin.tail ω)
            ↔ ((x (0 : Fin ((z :: w :: ws).length + 1)))
                = ω (0 : Fin ((z :: w :: ws).length))
              ∧ (fun j : Fin (w :: ws).length => (Fin.tail x) (Fin.castSucc j)) = Fin.tail ω) := by
          constructor
          · intro hc
            refine ⟨?_, ?_⟩
            · have h0 := congrFun hc (0 : Fin ((z :: w :: ws).length))
              simpa using! h0
            · funext j
              have hj := congrFun hc j.succ
              simpa using! hj
          · rintro ⟨h0, h1⟩
            funext j
            rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
            · simpa using! h0
            · simpa using! congrFun h1 j'
      by_cases hx0 : (x (0 : Fin ((z :: w :: ws).length + 1)))
          = ω (0 : Fin ((z :: w :: ws).length))
      · rw [if_pos hx0, one_mul]
        by_cases hf : (fun j : Fin (w :: ws).length => (Fin.tail x) (Fin.castSucc j))
            = Fin.tail ω
        · rw [if_pos hf, if_pos (hfront.mpr ⟨hx0, hf⟩), Pi.smul_apply, smul_eq_mul,
            mul_assoc]
          rfl
        · rw [if_neg hf, if_neg (fun hc => hf (hfront.mp hc).2)]
      · rw [if_neg hx0, zero_mul,
        if_neg (fun hc => hx0 (hfront.mp hc).1)]

theorem clusterSeqRegSucc_symm_front (n : ℕ) (v : Reg n) (c : Bool) (j : Fin n) :
    (regSuccEquiv n).symm (v, c) (Fin.castSucc j) = v j := by
  have h : regSuccEquiv n ((regSuccEquiv n).symm (v, c)) = (v, c) := Equiv.apply_symm_apply _ _
  rw [show regSuccEquiv n ((regSuccEquiv n).symm (v, c))
      = ((fun j => (regSuccEquiv n).symm (v, c) (Fin.castSucc j)),
          (regSuccEquiv n).symm (v, c) (Fin.last n)) from rfl] at h
  exact congrArg (fun p => (p.1 : Reg n) j) h

theorem clusterSeqRegSucc_symm_last (n : ℕ) (v : Reg n) (c : Bool) :
    (regSuccEquiv n).symm (v, c) (Fin.last n) = c := by
  have h : regSuccEquiv n ((regSuccEquiv n).symm (v, c)) = (v, c) := Equiv.apply_symm_apply _ _
  rw [show regSuccEquiv n ((regSuccEquiv n).symm (v, c))
      = ((fun j => (regSuccEquiv n).symm (v, c) (Fin.castSucc j)),
          (regSuccEquiv n).symm (v, c) (Fin.last n)) from rfl] at h
  exact congrArg (fun p => (p.2 : Bool)) h

theorem clusterSeqSum_col (f : Fin 2 → ℂ) (i : Fin 2) :
    (∑ k : Fin 2, f k * (if i = k then (1 : ℂ) else 0)) = f i := by
  fin_cases i <;> simp

theorem cluster_sequence_actual_leaf_full_amplitude :
    ∀ (zs : List ℂ), (∀ z ∈ zs, ‖z‖ = 1) →
      ∀ (ω v : Reg zs.length) (c i : Fin 2),
        ((observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).operator
            * clusterSequenceInitialFrame zs.length)
          (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c)) i =
        if v = ω then ((Real.sqrt 2 : ℂ)⁻¹) ^ zs.length * clusterSequenceUnitary zs c i
        else 0 := by
  intro zs hzs ω v c i
  have hphys := clusterSeqLeafPhysics zs hzs ω
    (fun j => if i = j then (1 : ℂ) else 0)
  set ecol : QState (Fin 2) := (fun j => if i = j then (1 : ℂ) else 0) with hecol
  set r := clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c) with hr
  have hop : (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).operator
      = relabelGate (bitVecEquiv (zs.length + 1))
          (clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length) := by
    rw [clusterSequenceLeaf_eq zs ω]
    exact clusterSeqProgramLeaf_operator (zs := zs) ω
  rw [hop]
  have hentry : ((relabelGate (bitVecEquiv (zs.length + 1))
          (clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length)
          * clusterSequenceInitialFrame zs.length) *ᵥ ecol) r
      = ((relabelGate (bitVecEquiv (zs.length + 1))
          (clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length)
          * clusterSequenceInitialFrame zs.length) r i) := by
    show (∑ k : Fin 2, (relabelGate (bitVecEquiv (zs.length + 1))
          (clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length)
          * clusterSequenceInitialFrame zs.length) r k
        * (if i = k then (1 : ℂ) else 0)) = _
    exact clusterSeqSum_col _ i
  rw [← hentry]
  set r := clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c) with hr
  have hrval : (bitVecEquiv (zs.length + 1)).symm r
      = (regSuccEquiv zs.length).symm (v, boolEquivFin2.symm c) := by
    unfold clusterSequenceRegisterEquiv at hr
    exact Equiv.symm_apply_apply _ _
  rw [clusterSeqMulVecAssoc, clusterSequenceInitialFrame_mulVec,
    show (relabelGate (bitVecEquiv (zs.length + 1))
          (clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length) *ᵥ
        relabelState (bitVecEquiv (zs.length + 1))
          (clusterSeqInitialFrameB zs.length *ᵥ ecol))
      = relabelState (bitVecEquiv (zs.length + 1))
          ((clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length) *ᵥ
            (clusterSeqInitialFrameB zs.length *ᵥ ecol))
      from applyGate_relabelGate _ _ _,
    relabelState_apply, hrval,
    show ((clusterSeqLeafOpLoopB zs ω * clusterSeqResourceGateB zs.length) *ᵥ
        (clusterSeqInitialFrameB zs.length *ᵥ ecol))
      = fun x : Reg (zs.length + 1) =>
        if (fun j => x (Fin.castSucc j)) = ω then
          ((Real.sqrt 2 : ℂ)⁻¹) ^ zs.length
            * (clusterSequenceUnitary zs *ᵥ ecol)
                (boolEquivFin2 (x (Fin.last zs.length)))
        else 0 from hphys]
  have hxfront : (fun j : Fin zs.length =>
      (regSuccEquiv zs.length).symm (v, boolEquivFin2.symm c) (Fin.castSucc j)) = v :=
    funext fun j => clusterSeqRegSucc_symm_front zs.length v _ j
  have hxlast : (regSuccEquiv zs.length).symm (v, boolEquivFin2.symm c)
        (Fin.last zs.length) = boolEquivFin2.symm c :=
    clusterSeqRegSucc_symm_last zs.length v _
  show (if (fun j : Fin zs.length =>
        (regSuccEquiv zs.length).symm (v, boolEquivFin2.symm c) (Fin.castSucc j)) = ω then
      ((Real.sqrt 2 : ℂ)⁻¹) ^ zs.length * (clusterSequenceUnitary zs *ᵥ ecol)
        (boolEquivFin2 ((regSuccEquiv zs.length).symm (v, boolEquivFin2.symm c)
          (Fin.last zs.length)))
    else 0) = _
  rw [hxfront, hxlast]
  by_cases hv : v = ω
  · rw [if_pos hv]
    have hbc : boolEquivFin2 (boolEquivFin2.symm c) = c := by
      fin_cases c <;> rfl
    rw [hbc]
    have hUcol : (clusterSequenceUnitary zs *ᵥ ecol) c = clusterSequenceUnitary zs c i := by
      show (∑ k : Fin 2, clusterSequenceUnitary zs c k
          * (if i = k then (1 : ℂ) else 0)) = _
      exact clusterSeqSum_col _ i
    rw [hUcol, if_pos hv]
  · rw [if_neg hv, if_neg hv]

def clusterSeqSplitEquiv (n : ℕ) : Fin (2 ^ (n + 1)) ≃ Reg n × Bool :=
  (bitVecEquiv (n + 1)).symm.trans (regSuccEquiv n)

theorem clusterSeqSplitEquiv_symm_apply (n : ℕ) (v : Reg n) (c : Bool) :
    (clusterSeqSplitEquiv n).symm (v, c)
      = clusterSequenceRegisterEquiv n (v, c) := rfl

theorem clusterSeqG4_vec (zs : List ℂ) (hzs : ∀ z ∈ zs, ‖z‖ = 1) (ω : Reg zs.length)
    (i : Fin 2) :
    ((observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).operator
        * clusterSequenceInitialFrame zs.length) *ᵥ Qatlib.Foundations.PureStateMath.Ket i
      = relabelState (clusterSeqSplitEquiv zs.length).symm
          (fun p : Reg zs.length × Bool =>
            if p.1 = ω then ((Real.sqrt 2 : ℂ)⁻¹) ^ zs.length
              * clusterSequenceUnitary zs (boolEquivFin2 p.2) i else 0) := by
  funext r
  show (∑ k : Fin 2, ((observedLeaf 1 (clusterSequenceProgram zs)
        (clusterSequenceLeaf zs ω)).operator
        * clusterSequenceInitialFrame zs.length) r k * Qatlib.Foundations.PureStateMath.Ket i k)
      = _
  rw [Finset.sum_eq_single i]
  · rw [ket_apply, if_pos rfl, mul_one]
    have hsplit : ∃ v : Reg zs.length, ∃ c : Fin 2,
        r = clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c) := by
      refine ⟨((clusterSeqSplitEquiv zs.length) r).1,
        boolEquivFin2 ((clusterSeqSplitEquiv zs.length) r).2, ?_⟩
      have h1 : r = (clusterSeqSplitEquiv zs.length).symm
          (((clusterSeqSplitEquiv zs.length) r).1,
            ((clusterSeqSplitEquiv zs.length) r).2) :=
        (Equiv.apply_symm_apply _ r).symm
      rw [h1]
      simp only [Equiv.apply_symm_apply, boolEquivFin2.symm_apply_apply]
      rfl
    obtain ⟨v, c, rfl⟩ := hsplit
    rw [cluster_sequence_actual_leaf_full_amplitude zs hzs ω v c i]
    show (if v = ω then ((Real.sqrt 2 : ℂ)⁻¹) ^ zs.length
          * clusterSequenceUnitary zs c i else 0)
      = (if ((clusterSeqSplitEquiv zs.length)
            (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c))).1 = ω
          then ((Real.sqrt 2 : ℂ)⁻¹) ^ zs.length
            * clusterSequenceUnitary zs
                (boolEquivFin2 ((clusterSeqSplitEquiv zs.length)
                  (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c))).2) i
          else 0)
    have hround : (clusterSeqSplitEquiv zs.length)
        (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c))
      = (v, boolEquivFin2.symm c) := Equiv.apply_symm_apply _ _
    rw [hround, boolEquivFin2.apply_symm_apply]
  · intro k _ hk
    show (((observedLeaf 1 (clusterSequenceProgram zs)
        (clusterSequenceLeaf zs ω)).operator
        * clusterSequenceInitialFrame zs.length) r k * Qatlib.Foundations.PureStateMath.Ket i k) = _
    rw [ket_apply, if_neg hk, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem clusterSeqSqrtPow (n : ℕ) :
    ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n = (1 / 2 : ℂ) ^ n := by
  rw [← mul_pow,
    show ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 from by
      rw [sqrt2_inv_sq]]

noncomputable def clusterSequenceActualBranchCore (zs : List ℂ) (ω : Reg zs.length)
    (ρ : Operator 2) : Operator 2 :=
  relabelGate boolEquivFin2 (Matrix.traceLeft
    (relabelGate (clusterSeqSplitEquiv zs.length)
      ((observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).operator
        * (clusterSequenceInitialFrame zs.length * ρ
            * (clusterSequenceInitialFrame zs.length).conjTranspose)
        * (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).operator.conjTranspose)))

noncomputable def clusterSequenceActualBranchMap (zs : List ℂ) (ω : Reg zs.length) :
    Operator 2 →ₗ[ℂ] Operator 2 where
  toFun := clusterSequenceActualBranchCore zs ω
  map_add' := by
    intro ρ σ
    show clusterSequenceActualBranchCore zs ω (ρ + σ) = _
    rw [show clusterSequenceActualBranchCore zs ω (ρ + σ)
        = clusterSequenceActualBranchCore zs ω ρ + clusterSequenceActualBranchCore zs ω σ from by
      unfold clusterSequenceActualBranchCore
      simp [Matrix.mul_add, Matrix.add_mul, relabelGate_add']]
  map_smul' := by
    intro r ρ
    show clusterSequenceActualBranchCore zs ω (r • ρ) = (RingHom.id ℂ) r • _
    rw [show clusterSequenceActualBranchCore zs ω (r • ρ)
        = r • clusterSequenceActualBranchCore zs ω ρ from by
      unfold clusterSequenceActualBranchCore
      simp [Matrix.mul_smul, Matrix.smul_mul, relabelGate_smul'],
      RingHom.id_apply]

theorem clusterSeqOneBitB_commute01 {m : ℕ} (j : Fin (m + 1))
    (U V : Matrix Bool Bool ℂ) :
    clusterSeqOneBitB (m + 1) 0 U * clusterSeqOneBitB (m + 1) j.succ V
      = clusterSeqOneBitB (m + 1) j.succ V * clusterSeqOneBitB (m + 1) 0 U :=
  clusterSeqOneBitB_commute (m + 1) 0 j.succ (fun h => Fin.succ_ne_zero j h.symm) U V

theorem clusterSequenceActualBranchMap_apply (zs : List ℂ)
    (hzs : ∀ z ∈ zs, ‖z‖ = 1) (ω : Reg zs.length) (ρ : Operator 2) :
    clusterSequenceActualBranchMap zs ω ρ =
      (1 / 2 : ℂ)^zs.length • conjBranch (clusterSequenceUnitary zs) ρ := by
  let L := (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).operator
  let F := clusterSequenceInitialFrame zs.length
  have hsand : L * (F * ρ * F.conjTranspose) * L.conjTranspose =
      (L * F) * ρ * (L * F).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  change relabelGate boolEquivFin2 (Matrix.traceLeft
    (relabelGate (clusterSeqSplitEquiv zs.length)
      (L * (F * ρ * F.conjTranspose) * L.conjTranspose))) = _
  rw [hsand]
  ext c d
  change (∑ v : Reg zs.length,
    ((L * F) * ρ * (L * F).conjTranspose)
      (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c))
      (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm d))) = _
  have hcol (v : Reg zs.length) (c i : Fin 2) :
      (L * F) (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c)) i =
      if v = ω then ((Real.sqrt 2 : ℂ)⁻¹)^zs.length * clusterSequenceUnitary zs c i
      else 0 := cluster_sequence_actual_leaf_full_amplitude zs hzs ω v c i
  rw [Fintype.sum_eq_single ω]
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, if_true,
      Matrix.smul_apply, smul_eq_mul, conjBranch_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hreal : star (((Real.sqrt 2 : ℂ)⁻¹)^zs.length) =
        ((Real.sqrt 2 : ℂ)⁻¹)^zs.length := by simp
    simp only [star_mul, hreal]
    rw [← clusterSeqSqrtPow zs.length]
    ring
  · intro v hv
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, if_neg hv,
      zero_mul, Finset.sum_const_zero]

theorem cluster_sequence_actual_branch_instrument_bridge (zs : List ℂ)
    (hzs : ∀ z ∈ zs, ‖z‖ = 1) (ω : Reg zs.length) :
    clusterSequenceActualBranchMap zs ω = (clusterSequenceInstrument zs hzs).branch ω ∧
    (∀ ρ : Operator 2, clusterSequenceActualBranchMap zs ω ρ =
      (1/2 : ℂ)^zs.length • conjBranch (clusterSequenceUnitary zs) ρ) := by
  refine ⟨?_, clusterSequenceActualBranchMap_apply zs hzs ω⟩
  ext ρ
  rw [clusterSequenceActualBranchMap_apply zs hzs ω,
    (cluster_sequence_instrument_probability_conditioning zs hzs ρ ω).1]

theorem clusterSequenceActualBranchMap_sum (zs : List ℂ)
    (hzs : ∀ z ∈ zs, ‖z‖ = 1) (ρ : Operator 2) :
    (∑ ω : Reg zs.length, clusterSequenceActualBranchMap zs ω ρ) =
      conjBranch (clusterSequenceUnitary zs) ρ := by
  simp_rw [(cluster_sequence_actual_branch_instrument_bridge zs hzs _).1]
  rw [← Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.forget_apply]
  exact (cluster_sequence_instrument_probability_conditioning zs hzs ρ (ZeroStr _)).2.2.1

theorem cluster_sequence_actual_reference_output (zs : List ℂ)
    (hzs : ∀ z ∈ zs, ‖z‖ = 1) (r : ℕ)
    (ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (ω : Reg zs.length) :
    tensorLeft (clusterSequenceActualBranchMap zs ω) ρ =
      (1/2 : ℂ)^zs.length • (TensorGate (clusterSequenceUnitary zs) (1 : Operator r) * ρ *
        (TensorGate (clusterSequenceUnitary zs) (1 : Operator r))ᴴ) ∧
    (∑ v : Reg zs.length, tensorLeft (clusterSequenceActualBranchMap zs v) ρ) =
      TensorGate (clusterSequenceUnitary zs) (1 : Operator r) * ρ *
        (TensorGate (clusterSequenceUnitary zs) (1 : Operator r))ᴴ := by
  constructor
  · rw [← tensorLeft_conjBranch]
    ext x y
    exact congrArg (fun M => M x.1 y.1)
      (clusterSequenceActualBranchMap_apply zs hzs ω (fun i j => ρ (i,x.2) (j,y.2)))
  · rw [← tensorLeft_conjBranch]
    ext x y
    simpa only [Matrix.sum_apply, tensorLeft] using! congrArg (fun M => M x.1 y.1)
      (clusterSequenceActualBranchMap_sum zs hzs (fun i j => ρ (i,x.2) (j,y.2)))

def clusterSequenceAppendOutcome (zs ys : List ℂ) (ω : Reg zs.length) (v : Reg ys.length) :
    Reg (zs ++ ys).length :=
  fun i => (regAppendEquiv zs.length ys.length).symm (ω,v) (Fin.cast (List.length_append ..) i)

theorem clusterSequenceUnitary_append (zs ys : List ℂ) :
    clusterSequenceUnitary (zs ++ ys) = clusterSequenceUnitary ys * clusterSequenceUnitary zs := by
  induction zs with
  | nil => simp [clusterSequenceUnitary]
  | cons z zs ih => simp [clusterSequenceUnitary, ih, Matrix.mul_assoc]

theorem cluster_sequence_append_actual_compilation (zs ys : List ℂ)
    (hzs : ∀ z ∈ zs, ‖z‖ = 1) (hys : ∀ y ∈ ys, ‖y‖ = 1) :
    clusterSequenceUnitary (zs++ys) = clusterSequenceUnitary ys * clusterSequenceUnitary zs ∧
    (∀ (ω : Reg zs.length) (v : Reg ys.length),
      clusterSequenceActualBranchMap (zs++ys) (clusterSequenceAppendOutcome zs ys ω v) =
        (clusterSequenceActualBranchMap ys v).comp (clusterSequenceActualBranchMap zs ω)) := by
  refine ⟨clusterSequenceUnitary_append zs ys, ?_⟩
  have hcat : ∀ z ∈ zs ++ ys, ‖z‖ = 1 := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hzs z hz
    · exact hys z hz
  intro ω v
  ext ρ
  simp only [LinearMap.comp_apply, clusterSequenceActualBranchMap_apply _ hcat,
    clusterSequenceActualBranchMap_apply _ hzs, clusterSequenceActualBranchMap_apply _ hys,
    map_smul, smul_smul, List.length_append, pow_add, clusterSequenceUnitary_append]
  rw [mul_comm ((1/2 : ℂ)^zs.length), ← LinearMap.comp_apply, conjBranch_comp]

end Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
