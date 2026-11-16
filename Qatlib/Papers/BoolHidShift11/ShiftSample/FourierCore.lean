/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.GateModel
public import Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier.SourceInfluenceFourier

@[expose] public section


/-! # Fourier amplitudes of the actual XOR sampling circuit

The shift identity is derived by a bijective change of summation variable.
The first two XOR queries and intervening phase retain the answer register;
the final Hadamard produces the signed real Fourier coefficient itself.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.ShiftSample.FourierCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open GateModel
open scoped BigOperators

/-- The actual normalization of the tensor Hadamard. -/
def scale (n : ℕ) : ℂ := ((Real.sqrt 2 : ℂ)⁻¹)^n

/-- Two Hadamard factors give the real uniform counting weight. -/
theorem scaleSquare (n : ℕ) : scale n * scale n = (uniformWeight n : ℂ) := by
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have h : (Real.sqrt (2:ℝ):ℂ)⁻¹*(Real.sqrt (2:ℝ):ℂ)⁻¹=(2:ℂ)⁻¹ := by
    rw [← mul_inv,← pow_two,hs]
  rw [scale,← mul_pow,h,uniformWeight]
  simp

/-- The actual tensor Hadamard entries are normalized Boolean characters. -/
theorem kernel {n : ℕ} (u x : Reg n) :
    HadamardN n u x=scale n*(chi u x:ℂ) := by
  rw [hadamardN_apply]
  simp [scale,chi]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> norm_num

/-- XOR translation is a bijection on the finite Boolean register. -/
def translate {n : ℕ} (s : Reg n) : Reg n ≃ Reg n where
  toFun x := regXor x s
  invFun x := regXor x s
  left_inv x := by
    change regXor (regXor x s) s=x
    rw [regXor_assoc,regXor_self,regXor_zero_right]
  right_inv x := by
    change regXor (regXor x s) s=x
    rw [regXor_assoc,regXor_self,regXor_zero_right]

/-- Translation multiplies an actual Fourier coefficient by its character. -/
theorem shiftedSum {n : ℕ} (F : Reg n → ℝ) (s u : Reg n) :
    (∑ x : Reg n, chi u x * F (regXor x s))=
      chi u s * ∑ x : Reg n, chi u x * F x := by
  calc
    _ = ∑ x : Reg n, chi u (regXor x s) * F x := by
      simpa [translate,regXor_comm,regXor_left_cancel] using
        (Equiv.sum_comp (translate s) (fun x => chi u x * F (regXor x s))).symm
    _ = _ := by simp only [chi_xor]; rw [Finset.mul_sum]; congr 1; funext x; ring

/-- The first input Hadamard prepares a zero answer and a uniform input state. -/
theorem firstHad {n : ℕ} (b : Bool) (x : Reg n) :
    ApplyGate (matrix (.had : Gate n)) (Ket (false,ZeroStr n)) (b,x)=
      if b=false then scale n else 0 := by
  rw [hadApply]
  by_cases hb : b=false
  · subst b
    simp only [Ket,Prod.mk.injEq,true_and,mul_ite,mul_one,mul_zero,ite_true]
    rw [Finset.sum_ite_eq' Finset.univ (ZeroStr n)]
    simp [scale,hadamardN_apply_zero_right]
  · simp [Ket,hb]

/-- The actual state just before the final Hadamard, including its answer bit. -/
theorem beforeLast {n : ℕ} (f g : Reg n → Bool) (b : Bool) (x : Reg n) :
    ApplyGate (oracleGate g)
      (ApplyGate (matrix (.phase : Gate n))
        (ApplyGate (oracleGate f)
          (ApplyGate (matrix (.had : Gate n)) (Ket (false,ZeroStr n))))) (b,x)=
      if b=Bool.xor (f x) (g x) then (signedFun f x:ℂ)*scale n else 0 := by
  rw [oracleApply,phaseApply,oracleApply,firstHad]
  cases b <;> cases hf : f x <;> cases hg : g x <;>
    simp [signedFun,hf]

/-- A masked signed input is the sum or difference of the two shifted signs. -/
theorem splitSign {n : ℕ} (f g : Reg n → Bool) (b : Bool) (x : Reg n) :
    (if b=Bool.xor (f x) (g x) then signedFun f x else 0)=
      (signedFun f x+(if b then -1 else 1)*signedFun g x)/2 := by
  cases b <;> cases hf : f x <;> cases hg : g x <;>
    norm_num [signedFun,hf,hg]

/-- The amplitude of the actual circuit is the Fourier transform of its masked sign. -/
theorem outputSum {n : ℕ} (f g : Reg n → Bool) (b : Bool) (u : Reg n) :
    output f g (b,u)=(uniformWeight n:ℂ)*
      ∑ x : Reg n, (chi u x:ℂ)*(if b=Bool.xor (f x) (g x) then (signedFun f x:ℂ) else 0) := by
  change ApplyGate (matrix (.had : Gate n))
    (ApplyGate (oracleGate g) (ApplyGate (matrix (.phase : Gate n))
      (ApplyGate (oracleGate f) (ApplyGate (matrix (.had : Gate n))
        (Ket (false,ZeroStr n)))))) (b,u)=_
  rw [hadApply]
  simp_rw [beforeLast,kernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← scaleSquare n]
  split_ifs <;> ring

end Qatlib.Papers.BoolHidShift11.ShiftSample.FourierCore
