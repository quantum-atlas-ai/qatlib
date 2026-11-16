/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.FourierCore
public import Qatlib.Papers.BoolHidShift11.ShiftSample.SampleMath

@[expose] public section


/-! # Figure 1 to the actual sampling law of Equation 2

The exact state, including the sign of each Fourier coefficient, is computed
from the unitary five-gate word. Its Born probabilities agree with the literal
legacy sample distribution; that distribution is not substituted for a circuit.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.ShiftSample.SampleCircuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open GateModel FourierCore SampleMath
open scoped BigOperators

/-- The shifted oracle promise determines the relation between the two signed inputs. -/
theorem shiftedSign {n : ℕ} (inst : BHSPInstance n) (x : Reg n) :
    signedFun inst.g x=signedFun inst.f (regXor x inst.shift) := by
  simp only [signedFun,inst.shifted]

/-- The masked Fourier sum is exactly one coefficient on the consistent answer slice. -/
theorem maskedFourier {n : ℕ} (inst : BHSPInstance n) (b : Bool) (u : Reg n) :
    uniformWeight n * ∑ x : Reg n, chi u x *
      (if b=Bool.xor (inst.f x) (inst.g x) then signedFun inst.f x else 0)=
      if b=parityDot inst.shift u then fourierCoef (signedFun inst.f) u else 0 := by
  simp_rw [splitSign,←mul_div_assoc,mul_add]
  rw [← Finset.sum_div,Finset.sum_add_distrib]
  have he : (∑ x : Reg n, chi u x * ((if b then -1 else 1)*signedFun inst.g x))=
      (if b then -1 else 1)*chi u inst.shift*
        ∑ x : Reg n, chi u x * signedFun inst.f x := by
    simp_rw [shiftedSign]
    calc
      _ = (if b then -1 else 1)*∑ x : Reg n, chi u x *
          signedFun inst.f (regXor x inst.shift) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [shiftedSum]; ring
  rw [he,chi_comm u inst.shift,chi_eq_ite]
  cases b <;> cases parityDot inst.shift u <;> simp [fourierCoef,mul_comm]

/-- The actual signed amplitude, not merely a postulated sampling distribution. -/
theorem outputExact {n : ℕ} (inst : BHSPInstance n) (b : Bool) (u : Reg n) :
    output inst.f inst.g (b,u)=
      if b=parityDot inst.shift u then (fourierCoef (signedFun inst.f) u:ℂ) else 0 := by
  rw [outputSum]
  have hc : ((uniformWeight n * ∑ x : Reg n, chi u x *
      (if b=Bool.xor (inst.f x) (inst.g x) then signedFun inst.f x else 0):ℝ):ℂ)=
      (uniformWeight n:ℂ)*∑ x : Reg n, (chi u x:ℂ)*
        (if b=Bool.xor (inst.f x) (inst.g x) then (signedFun inst.f x:ℂ) else 0) := by
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [←hc,maskedFourier]
  split_ifs <;> simp

/-- The Born law is exactly the source sampling distribution, with two counted XOR queries. -/
theorem bornLaw {n : ℕ} (inst : BHSPInstance n) (b : Bool) (u : Reg n) :
    BornProb (output inst.f inst.g) (b,u)=sampleDist (signedFun inst.f) inst.shift b u := by
  rw [BornProb,outputExact]
  unfold sampleDist
  split_ifs <;> simp [Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Every actual nonzero Born outcome gives a correct linear equation for the shift. -/
theorem exactEquation {n : ℕ} (inst : BHSPInstance n) (b : Bool) (u : Reg n)
    (h : BornProb (output inst.f inst.g) (b,u)≠0) : b=parityDot inst.shift u := by
  rw [bornLaw] at h
  exact sampleConsist _ _ h

/-- The actual input-register marginal is the squared Fourier coefficient. -/
theorem marginalLaw {n : ℕ} (inst : BHSPInstance n) (u : Reg n) :
    (∑ b : Bool, BornProb (output inst.f inst.g) (b,u))=
      (fourierCoef (signedFun inst.f) u)^2 := by
  simp_rw [bornLaw]
  exact sampleMarginal _ _ _

end Qatlib.Papers.BoolHidShift11.ShiftSample.SampleCircuit
