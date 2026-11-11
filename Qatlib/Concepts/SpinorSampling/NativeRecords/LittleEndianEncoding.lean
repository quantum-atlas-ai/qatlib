/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBornBridge

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
/-!
# Executable little-endian source address encoding

Integer test bits reconstruct the exact original finite address and source
wire order. The implementation uses no inverse chosen by finite cardinality.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib
/-- Actual low-endian address bits, computed by reading the finite integer's bits. -/
def littleBits (r : ℕ) (x : Fin (2^r)) : Reg r := fun i => x.val.testBit i.val
/-- Computing the low-endian bits and reading their integer value returns the supplied finite address. -/
theorem littleAddress_littleBits (r : ℕ) (x : Fin (2^r)) :
    littleAddress r (littleBits r x)=x := by
  apply Fin.ext
  change axisValue (List.ofFn (littleBits r x))=x.val
  induction r with
  | zero =>
    have hx := x.isLt
    simp at hx
    simp [List.ofFn_zero,axisValue]
  | succ r ih =>
    have hx : x.val/2<2^r := by
      have h : x.val<2^r*2 := by simpa only [Nat.pow_succ] using x.isLt
      omega
    let y : Fin (2^r) := ⟨x.val/2,hx⟩
    rw [List.ofFn_succ,axisValue]
    have ht : (fun i : Fin r => littleBits (r+1) x i.succ)=littleBits r y := by
      funext i
      simp only [littleBits,Fin.val_succ,Nat.testBit_succ,y]
    rw [ht,ih y]
    change (x.val.testBit 0).toNat+2*(x.val/2)=x.val
    have hmod := Nat.mod_lt x.val (by decide : 0<2)
    by_cases h : x.val%2=1
    · simp only [Nat.testBit_zero,h,decide_true,Bool.toNat_true]
      omega
    · have hm : x.val%2=0 := by omega
      simp only [Nat.testBit_zero,hm,Nat.zero_ne_one,decide_false,Bool.toNat_false]
      omega
/-- The executable encoder agrees with the original semantic equivalence inverse. -/
theorem littleBits_eq_inverse (r : ℕ) (x : Fin (2^r)) :
    littleBits r x=(littleEndianEquiv r).symm x := by
  apply (littleEndianEquiv r).injective
  simpa only [little_endian_equiv_apply,Equiv.apply_symm_apply] using littleAddress_littleBits r x
end Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
/-- Executable source-address encoder using the actual low-endian bit at each canonical wire. -/
def positionBits (d r : ℕ) (x : Fin d → Fin (2^r)) : Reg (d*r) := fun w =>
  let ji := (finProdFinEquiv : Fin d × Fin r ≃ Fin (d*r)).symm w
  littleBits r (x ji.1) ji.2
/-- The actual source layout reads the executable bits as precisely the original address. -/
theorem positionEquiv_positionBits (d r : ℕ) (x : Fin d → Fin (2^r)) :
    positionEquiv d r (positionBits d r x)=x := by
  funext j
  rw [position_equiv_apply]
  have he : (fun i => positionBits d r x (finProdFinEquiv (j,i)))=littleBits r (x j) := by
    funext i
    simp only [positionBits,Equiv.symm_apply_apply]
  rw [he,littleAddress_littleBits]
/-- Executable source bits agree with the original semantic layout inverse. -/
theorem positionBits_eq_inverse (d r : ℕ) (x : Fin d → Fin (2^r)) :
    positionBits d r x=(positionEquiv d r).symm x := by
  apply (positionEquiv d r).injective
  rw [positionEquiv_positionBits,Equiv.apply_symm_apply]
end Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
