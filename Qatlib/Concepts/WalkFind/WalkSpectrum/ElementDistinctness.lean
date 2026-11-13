/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.ElementDistinctnessDefs
import Qatlib.Concepts.WalkFind.QRAMModel.QRAMImplementation

/-!
# A compact-register value oracle

This module verifies the bit-register action `compactValueAction` and proves that
`compactValueOracle` is unitary for a positive alphabet size. Valid addresses receive the input
value by modular addition in the answer register, while other register fields are preserved
[NielsenChuang2010].

The theorem `clause32` establishes `CompactMemorySpec`, packaging a legal unitary source circuit
with one oracle query, compact width bounds, and the required basis-state semantics for the
collision-search memory model [Ambainis2007ElementDistinctness].

## Main statements

* `compactValueAction_injective`: injectivity of the register action.
* `compactValueAction_ket`: loading an input value into a zero answer field.
* `clause32`: the compact-memory specification.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.WalkFind.QRAMModel

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib
open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Concepts.WalkFind.WalkSpectrum

/-- The compact value action preserves every bit outside the answer-register interval. -/
private theorem compactValueAction_outside {N M r w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (compactWidth N M r w)) (i : Fin (compactWidth N M r w))
    (hi : ¬(Nat.clog 2 (N+1) ≤ i.val ∧ i.val < Nat.clog 2 (N+1)+Nat.clog 2 (M+1))) :
    compactValueAction x ψ i = ψ i := by
  unfold compactValueAction
  split_ifs <;> simp_all

/-- The compact value action is the identity when the decoded address or answer lies outside its
valid range. -/
private theorem compactValueAction_invalid {N M r w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (compactWidth N M r w))
    (h : N ≤ addressValue ψ 0 (Nat.clog 2 (N+1)) ∨
      M ≤ addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) :
    compactValueAction x ψ = ψ := by
  unfold compactValueAction
  (try dsimp only)
  rcases h with h | h
  · simp [show ¬addressValue ψ 0 (Nat.clog 2 (N+1)) < N by omega]
  · simp [show ¬addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M by omega]

/-- The compact value action preserves the decoded address. -/
private theorem compactValueAction_address {N M r w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (compactWidth N M r w)) :
    addressValue (compactValueAction x ψ) 0 (Nat.clog 2 (N+1)) =
      addressValue ψ 0 (Nat.clog 2 (N+1)) := by
  unfold addressValue
  apply Finset.sum_congr rfl
  intro i hi
  have hiw := Finset.mem_range.mp hi
  have hib : i < compactWidth N M r w := by unfold compactWidth; omega
  have hbit := compactValueAction_outside x ψ (⟨i,hib⟩) (by dsimp; omega)
  simpa [readBit,hib] using! congrArg (fun b => if b then 2^i else 0) hbit

/-- For a valid address and answer, the decoded new answer is the old answer plus the addressed
input value modulo `M`. -/
private theorem compactValueAction_answer {N M r w : ℕ} (hM : 0 < M) (x : Fin N → ZMod M)
    (ψ : Reg (compactWidth N M r w))
    (ha : addressValue ψ 0 (Nat.clog 2 (N+1)) < N)
    (hb : addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M) :
    addressValue (compactValueAction x ψ) (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) =
      (addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))+
        (x ⟨addressValue ψ 0 (Nat.clog 2 (N+1)),ha⟩).val) % M := by
  have hcap := Nat.le_pow_clog (by decide : 1 < 2) (M+1)
  unfold compactValueAction
  (try dsimp only)
  rw [dif_pos ha,if_pos hb,addressValue_written ψ _ _ _ (by unfold compactWidth; omega)]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hM) (by omega))

/-- For positive `M`, the compact value action is injective on register labels. -/
private theorem compactValueAction_injective {N M r w : ℕ} (hM : 0 < M) (x : Fin N → ZMod M) :
    Function.Injective (compactValueAction (N := N) (M := M) (r := r) (w := w) x) := by
  letI : NeZero M := ⟨hM.ne'⟩
  intro ψ φ heq
  have had : addressValue ψ 0 (Nat.clog 2 (N+1)) = addressValue φ 0 (Nat.clog 2 (N+1)) := by
    have hh := congrArg (fun z => addressValue z 0 (Nat.clog 2 (N+1))) heq
    (try dsimp only at hh)
    simpa only [compactValueAction_address] using! hh
  have houtside : ∀ i : Fin (compactWidth N M r w),
      ¬((Nat.clog 2 (N+1)) ≤ i.val ∧ i.val < (Nat.clog 2 (N+1))+(Nat.clog 2 (M+1))) →
      ψ i = φ i := by
    intro i hi
    exact (compactValueAction_outside x ψ i hi).symm.trans
      ((congrFun heq i).trans (compactValueAction_outside x φ i hi))
  by_cases ha : addressValue ψ 0 (Nat.clog 2 (N+1)) < N
  · have haφ : addressValue φ 0 (Nat.clog 2 (N+1)) < N := had ▸ ha
    by_cases hb : addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M
    · by_cases hbφ : addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M
      · have hans : addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) =
            addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) := by
          have hh := congrArg (fun z => addressValue z (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) heq
          (try dsimp only at hh)
          rw [compactValueAction_answer hM x ψ ha hb,
            compactValueAction_answer hM x φ haφ hbφ] at hh
          have hval : (x ⟨addressValue ψ 0 (Nat.clog 2 (N+1)),ha⟩).val =
              (x ⟨addressValue φ 0 (Nat.clog 2 (N+1)),haφ⟩).val := by
            congr 2
            exact Fin.ext had
          rw [hval] at hh
          have heZ : (addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) : ZMod M) =
              (addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) : ZMod M) := by
            apply add_right_cancel (b := (x ⟨addressValue φ 0 (Nat.clog 2 (N+1)),haφ⟩))
            apply ZMod.val_injective
            simpa only [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hb,
              Nat.mod_eq_of_lt hbφ] using! hh
          have hhval := congrArg ZMod.val heZ
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hbφ] using! hhval
        funext i
        by_cases hi : (Nat.clog 2 (N+1)) ≤ i.val ∧ i.val < (Nat.clog 2 (N+1))+(Nat.clog 2 (M+1))
        · have hh := addressValue_bits_injective ψ φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) hans
              (i.val-(Nat.clog 2 (N+1))) (by omega)
          simpa [readBit,show (Nat.clog 2 (N+1))+(i.val-(Nat.clog 2 (N+1))) = i.val by omega,
            i.isLt] using! hh
        · exact houtside i hi
      · have hfix := compactValueAction_invalid x φ (Or.inr (by omega))
        have hh := congrArg (fun z => addressValue z (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) heq
        (try dsimp only at hh)
        rw [compactValueAction_answer hM x ψ ha hb,hfix] at hh
        have hm := Nat.mod_lt (addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))+
          (x ⟨addressValue ψ 0 (Nat.clog 2 (N+1)),ha⟩).val) hM
        omega
    · have hfix := compactValueAction_invalid x ψ (Or.inr (by omega))
      by_cases hbφ : addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) < M
      · have hh := congrArg (fun z => addressValue z (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))) heq
        (try dsimp only at hh)
        rw [hfix,compactValueAction_answer hM x φ haφ hbφ] at hh
        have hm := Nat.mod_lt (addressValue φ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1))+
          (x ⟨addressValue φ 0 (Nat.clog 2 (N+1)),haφ⟩).val) hM
        omega
      · simpa only [hfix,compactValueAction_invalid x φ (Or.inr (by omega))] using! heq
  · have hψ := compactValueAction_invalid x ψ (Or.inl (by omega))
    have hφ := compactValueAction_invalid x φ (Or.inl (by omega))
    simpa only [hψ,hφ] using! heq

/-- For positive `M`, the compact value oracle belongs to the unitary group. -/
private theorem compactValueOracle_unitary {N M r w : ℕ} (hM : 0 < M) (x : Fin N → ZMod M) :
    compactValueOracle (N := N) (M := M) (r := r) (w := w) x ∈
      Matrix.unitaryGroup (Reg (compactWidth N M r w)) ℂ :=
  permMatrix_unitary_of_injective (compactValueAction_injective hM x)

/-- Decoding the address field of `compactKet` gives the supplied address modulo the
address-field capacity. -/
private theorem compactKet_address (N M r w : ℕ) (addr v : ℕ) (work data : ℕ → Bool) :
    addressValue (compactKet N M r w addr v work data) 0 (Nat.clog 2 (N+1)) =
      addr % 2^(Nat.clog 2 (N+1)) := by
  unfold addressValue
  rw [← naturalBit_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : j < Nat.clog 2 (N+1) := Finset.mem_range.mp hj
  have hib : j < compactWidth N M r w := by unfold compactWidth; omega
  have hbit : readBit (compactKet N M r w addr v work data) j = naturalBit addr j := by
    simp [readBit, compactKet, hib, hjb]
  simpa using! congrArg (fun b => if b then 2^j else 0) hbit

/-- Decoding the answer field of `compactKet` gives the supplied value modulo the answer-field
capacity. -/
private theorem compactKet_answer (N M r w : ℕ) (addr v : ℕ) (work data : ℕ → Bool) :
    addressValue (compactKet N M r w addr v work data) (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) =
      v % 2^(Nat.clog 2 (M+1)) := by
  unfold addressValue
  rw [← naturalBit_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : j < Nat.clog 2 (M+1) := Finset.mem_range.mp hj
  have hib : Nat.clog 2 (N+1)+j < compactWidth N M r w := by unfold compactWidth; omega
  have hbit : readBit (compactKet N M r w addr v work data) (Nat.clog 2 (N+1)+j)
      = naturalBit v j := by
    simp [readBit, compactKet, hib, hjb,
      show ¬(Nat.clog 2 (N+1)+j < Nat.clog 2 (N+1)) by omega,
      show Nat.clog 2 (N+1)+j-(Nat.clog 2 (N+1)) = j by omega]
  simpa using! congrArg (fun b => if b then 2^j else 0) hbit

/-- For valid decoded address and answer fields, the compact value action writes the modular-sum
result into the answer bits and preserves all other bits. -/
private theorem compactValueAction_valid (N M r w : ℕ) (_hM : 0 < M) (x : Fin N → ZMod M)
    (ψ : Reg (compactWidth N M r w)) (addr ans result : ℕ)
    (ha : addr < N) (hb : ans < M)
    (hr : result = (ans+(x ⟨addr,ha⟩).val) % M)
    (hA : addressValue ψ 0 (Nat.clog 2 (N+1)) = addr)
    (hB : addressValue ψ (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) = ans) :
    compactValueAction x ψ =
      fun k => if Nat.clog 2 (N+1) ≤ k.val ∧ k.val < Nat.clog 2 (N+1)+Nat.clog 2 (M+1)
        then naturalBit result (k.val-(Nat.clog 2 (N+1))) else ψ k := by
  unfold compactValueAction
  (try dsimp only)
  rw [hA, hB, dif_pos ha, if_pos hb]
  simp only [hr]

/-- On a compact label with valid address `i` and zero answer, the value action writes `(x
i).val` and preserves the work and data fields. -/
private theorem compactValueAction_ket {N M r w : ℕ} (hM : 0 < M) (x : Fin N → ZMod M)
    (i : Fin N) (work data : ℕ → Bool) :
    compactValueAction x (compactKet N M r w i.val 0 work data) =
      compactKet N M r w i.val (x i).val work data := by
  have hNlt : N < 2^(Nat.clog 2 (N+1)) := by
    have hh := Nat.le_pow_clog (by decide : 1 < 2) (N+1)
    omega
  have hA : addressValue (compactKet N M r w i.val 0 work data) 0 (Nat.clog 2 (N+1)) =
      i.val := by
    rw [compactKet_address, Nat.mod_eq_of_lt (lt_trans i.isLt hNlt)]
  have hB : addressValue (compactKet N M r w i.val 0 work data)
      (Nat.clog 2 (N+1)) (Nat.clog 2 (M+1)) = 0 := by
    rw [compactKet_answer]
    simp
  have hr : (x i).val = (0+(x ⟨i.val,i.isLt⟩).val) % M := by
    haveI : NeZero M := ⟨hM.ne'⟩
    rw [Nat.zero_add]
    exact (Nat.mod_eq_of_lt (ZMod.val_lt (x i))).symm
  rw [compactValueAction_valid N M r w hM x (compactKet N M r w i.val 0 work data)
    i.val 0 (x i).val i.isLt hM hr hA hB]
  funext k
  by_cases h1 : Nat.clog 2 (N+1) ≤ k.val ∧ k.val < Nat.clog 2 (N+1)+Nat.clog 2 (M+1)
  · simp only [h1]
    simp [compactKet, show ¬(k.val < Nat.clog 2 (N+1)) by omega,
      show k.val < Nat.clog 2 (N+1)+Nat.clog 2 (M+1) by omega]
  · rcases Nat.lt_or_ge k.val (Nat.clog 2 (N+1)) with hk | hk
    · simp [compactKet, show k.val < Nat.clog 2 (N+1) from hk,
        show ¬(Nat.clog 2 (N+1) ≤ k.val) by omega]
    · have hk2 : Nat.clog 2 (N+1)+Nat.clog 2 (M+1) ≤ k.val := by omega
      simp [compactKet, show ¬(k.val < Nat.clog 2 (N+1)) by omega,
        show ¬(k.val < Nat.clog 2 (N+1)+Nat.clog 2 (M+1)) by omega]

/-- Applying the compact value oracle to a basis ket gives the basis ket at the label
transformed by `compactValueAction`. -/
private theorem compactValueOracle_apply_ket {N M r w : ℕ} (x : Fin N → ZMod M)
    (v : Reg (compactWidth N M r w)) :
    ApplyGate (compactValueOracle (N := N) (M := M) (r := r) (w := w) x) (Qatlib.Foundations.PureStateMath.Ket v) =
      Qatlib.Foundations.PureStateMath.Ket (compactValueAction x v) := by
  funext z
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket,
      compactValueOracle]
  rw [Finset.sum_eq_single v]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The compact one-query value-loading construction satisfies `CompactMemorySpec`
[Ambainis2007ElementDistinctness]. -/
theorem clause32 : Qatlib.Concepts.WalkFind.WalkSpectrum.CompactMemorySpec := by
  intro k _hk
  refine ⟨1, 1, by norm_num, ?_⟩
  intro N M r _ _hN hM _hkr _hrN
  refine ⟨0, [SourceCode.query], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hab : (0:ℝ) ≤ ((Nat.clog 2 (N+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmb : (0:ℝ) ≤ ((Nat.clog 2 (M+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrr : (0:ℝ) ≤ ((r : ℕ) : ℝ) := Nat.cast_nonneg _
    have hprod : (0:ℝ) ≤ ((r : ℕ) : ℝ)*((Nat.clog 2 (N+1) : ℕ) : ℝ) :=
      mul_nonneg hrr hab
    unfold compactWidth dataBits
    push_cast
    nlinarith [hprod, hrr, hmb]
  · simp [sourceWordLegal, sourceCodeLegal]
  · simp [sourceCircuit]
  · simp [sourceCircuit]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, codeBits, pow_one,
      one_mul]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dataBits N M))
  · intro x
    refine ⟨compactValueOracle_unitary hM x, ?_⟩
    intro i work data
    have hket := compactValueAction_ket (N := N) (M := M) (r := r) (w := 0) hM x i work data
    show ApplyGate (compactValueOracle (N := N) (M := M) (r := r) (w := 0) x)
        (Qatlib.Foundations.PureStateMath.Ket (compactKet N M r 0 i.val 0 work data)) = _
    rw [compactValueOracle_apply_ket, hket]

end Qatlib.Concepts.WalkFind.WalkSpectrum
