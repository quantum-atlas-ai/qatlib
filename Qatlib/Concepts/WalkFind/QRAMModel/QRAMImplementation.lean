/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.QRAMModel.OrdinaryGateQRAMFallbackQuan
open Qatlib.Concepts.BlockEncoding.LinearCombination
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.QRAMModel
open Matrix
open scoped Classical BigOperators

theorem naturalBit_sum (n w : ℕ) :
    (∑ j ∈ Finset.range w, if naturalBit n j then 2^j else 0) = n % 2^w := by
  induction w with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]
    have hv := Nat.mod_lt (n / 2^w) (by decide : 0 < 2)
    by_cases h : n / 2^w % 2 = 1
    · simp [naturalBit, h]
    · have hz : n / 2^w % 2 = 0 := by omega
      simp [naturalBit, hz]

theorem addressValue_written {b : ℕ} (ψ : Reg b) (a w n : ℕ) (haw : a+w ≤ b) :
    addressValue (fun i => if a ≤ i.val ∧ i.val < a+w then naturalBit n (i.val-a) else ψ i) a w =
      n % 2^w := by
  unfold addressValue
  convert! naturalBit_sum n w using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hiw := Finset.mem_range.mp hi
  have hib : a+i < b := by omega
  simp [readBit, hib, show a ≤ a+i by omega, show a+i < a+w by omega]

theorem addressValue_bits_injective {b : ℕ} (ψ φ : Reg b) (a w : ℕ)
    (h : addressValue ψ a w = addressValue φ a w) :
    ∀ i < w, readBit ψ (a+i) = readBit φ (a+i) := by
  induction w with
  | zero => intro i hi; omega
  | succ w ih =>
    have hp := addressValue_lt_capacity ψ a w
    have hq := addressValue_lt_capacity φ a w
    have heq : readBit ψ (a+w) = readBit φ (a+w) := by
      simp only [addressValue, Finset.sum_range_succ] at h
      cases hψ : readBit ψ (a+w) <;> cases hφ : readBit φ (a+w) <;>
        simp only [hψ,hφ, Bool.false_eq_true, if_false, if_true, add_zero] at h ⊢
      · change addressValue ψ a w = addressValue φ a w+2^w at h
        omega
      · change addressValue ψ a w+2^w = addressValue φ a w at h
        omega
    have hlow : addressValue ψ a w = addressValue φ a w := by
      simp only [addressValue, Finset.sum_range_succ, heq] at h
      exact Nat.add_right_cancel h
    intro i hi
    by_cases hiw : i < w
    · exact ih hlow i hiw
    · have hie : i = w := by omega
      simpa [hie] using! heq

theorem sourceValueAction_outside {N M k w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (nativeWidth N M k w)) (i : Fin (nativeWidth N M k w))
    (hi : ¬(Nat.clog 2 (N+1) ≤ i.val ∧ i.val < Nat.clog 2 (N+1)+Nat.clog 2 (M+1))) :
    sourceValueAction x ψ i = ψ i := by
  unfold sourceValueAction
  split_ifs <;> simp_all

theorem sourceValueAction_invalid {N M k w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (nativeWidth N M k w))
    (h : N ≤ addressValue ψ 0 (Nat.clog 2 (N+1)) ∨
      M ≤ addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) :
    sourceValueAction x ψ = ψ := by
  unfold sourceValueAction
  (try dsimp only)
  rcases h with h | h
  · simp [show ¬addressValue ψ 0 (Nat.clog 2 (N+1)) < N by omega]
  · simp [show ¬addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M by omega]

theorem sourceValueAction_address {N M k w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (nativeWidth N M k w)) :
    addressValue (sourceValueAction x ψ) 0 (Nat.clog 2 (N+1)) =
      addressValue ψ 0 (Nat.clog 2 (N+1)) := by
  unfold addressValue
  apply Finset.sum_congr rfl
  intro i hi
  have hiw := Finset.mem_range.mp hi
  have hib : i < nativeWidth N M k w := by unfold nativeWidth; omega
  have hbit := sourceValueAction_outside x ψ (⟨i,hib⟩) (by dsimp; omega)
  simpa [readBit,hib] using! congrArg (fun b => if b then 2^i else 0) hbit

theorem sourceValueAction_answer {N M k w : ℕ} (hM : 0 < M) (x : Fin N → ZMod M)
    (ψ : Reg (nativeWidth N M k w))
    (ha : addressValue ψ 0 (Nat.clog 2 (N+1)) < N)
    (hb : addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M) :
    addressValue (sourceValueAction x ψ) (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) =
      (addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))+
        (x ⟨addressValue ψ 0 (Nat.clog 2 (N+1)),ha⟩).val) % M := by
  have hcap := Nat.le_pow_clog (by decide : 1 < 2) (M+1)
  unfold sourceValueAction
  (try dsimp only)
  rw [dif_pos ha,if_pos hb,addressValue_written ψ _ _ _ (by unfold nativeWidth; omega)]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hM) (by omega))

theorem sourceValueAction_injective {N M k w : ℕ} (hM : 0 < M) (x : Fin N → ZMod M) :
    Function.Injective (sourceValueAction (k:=k) (w:=w) x) := by
  letI : NeZero M := ⟨hM.ne'⟩
  intro ψ φ heq
  have had : addressValue ψ 0 (Nat.clog 2 (N+1)) = addressValue φ 0 (Nat.clog 2 (N+1)) := by
    have hh := congrArg (fun z => addressValue z 0 (Nat.clog 2 (N+1))) heq
    (try dsimp only at hh)
    simpa only [sourceValueAction_address] using! hh
  have houtside : ∀ i : Fin (nativeWidth N M k w), ¬((Nat.clog 2 (N+1)) ≤ i.val ∧ i.val < (Nat.clog 2 (N+1))+(Nat.clog 2 (M+1))) → ψ i = φ i := by
    intro i hi
    exact (sourceValueAction_outside x ψ i hi).symm.trans
      ((congrFun heq i).trans (sourceValueAction_outside x φ i hi))
  by_cases ha : addressValue ψ 0 (Nat.clog 2 (N+1)) < N
  · have haφ : addressValue φ 0 (Nat.clog 2 (N+1)) < N := had ▸ ha
    by_cases hb : addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M
    · by_cases hbφ : addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M
      · have hans : addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) = addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) := by
          have hh := congrArg (fun z => addressValue z (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) heq
          (try dsimp only at hh)
          rw [sourceValueAction_answer hM x ψ ha hb, sourceValueAction_answer hM x φ haφ hbφ] at hh
          have hval : (x ⟨addressValue ψ 0 (Nat.clog 2 (N+1)),ha⟩).val = (x ⟨addressValue φ 0 (Nat.clog 2 (N+1)),haφ⟩).val := by
            congr 2
            exact Fin.ext had
          rw [hval] at hh
          have heZ : (addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) : ZMod M) = (addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) : ZMod M) := by
            apply add_right_cancel (b := (x ⟨addressValue φ 0 (Nat.clog 2 (N+1)),haφ⟩))
            apply ZMod.val_injective
            simpa only [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hb,
                Nat.mod_eq_of_lt hbφ] using! hh
          have hhval := congrArg ZMod.val heZ
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hbφ] using! hhval
        funext i
        by_cases hi : (Nat.clog 2 (N+1)) ≤ i.val ∧ i.val < (Nat.clog 2 (N+1))+(Nat.clog 2 (M+1))
        · have hh := addressValue_bits_injective ψ φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) hans (i.val-(Nat.clog 2 (N+1))) (by omega)
          simpa [readBit,show (Nat.clog 2 (N+1))+(i.val-(Nat.clog 2 (N+1))) = i.val by omega,i.isLt] using! hh
        · exact houtside i hi
      · have hfix := sourceValueAction_invalid x φ (Or.inr (by omega))
        have hh := congrArg (fun z => addressValue z (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) heq
        (try dsimp only at hh)
        rw [sourceValueAction_answer hM x ψ ha hb,hfix] at hh
        have hm :=
            Nat.mod_lt (addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))+(x ⟨addressValue ψ 0 (Nat.clog 2 (N+1)),ha⟩).val) hM
        omega
    · have hfix := sourceValueAction_invalid x ψ (Or.inr (by omega))
      by_cases hbφ : addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M
      · have hh := congrArg (fun z => addressValue z (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) heq
        (try dsimp only at hh)
        rw [hfix,sourceValueAction_answer hM x φ haφ hbφ] at hh
        have hm :=
            Nat.mod_lt (addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))+(x ⟨addressValue φ 0 (Nat.clog 2 (N+1)),haφ⟩).val) hM
        omega
      · simpa only [hfix,sourceValueAction_invalid x φ (Or.inr (by omega))] using! heq
  · have hψ := sourceValueAction_invalid x ψ (Or.inl (by omega))
    have hφ := sourceValueAction_invalid x φ (Or.inl (by omega))
    simpa only [hψ,hφ] using! heq

theorem sourceValueOracle_unitary {N M k w : ℕ} (hM : 0 < M) (x : Fin N → ZMod M) :
    sourceValueOracle (k:=k) (w:=w) x ∈ Matrix.unitaryGroup (Reg (nativeWidth N M k w)) ℂ :=
  permMatrix_unitary_of_injective (sourceValueAction_injective hM x)

end Qatlib.Concepts.WalkFind.QRAMModel
