/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.QAOASupremacy16.CircuitDefs

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators

variable {n : ℕ}

structure CostFn (n m : ℕ) where

  toFun : Reg n → ℕ

  le_m : ∀ z, toFun z ≤ m

instance {n m : ℕ} : CoeFun (CostFn n m) (fun _ => Reg n → ℕ) := ⟨CostFn.toFun⟩

noncomputable def phaseGate (γ : ℝ) (C : Reg n → ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun z => Complex.exp (-(γ * (C z : ℝ)) * Complex.I)

@[simp] theorem phaseGate_mulVec (γ : ℝ) (C : Reg n → ℕ) (ψ : QState (Reg n)) (z : Reg n) :
    (phaseGate γ C).mulVec ψ z
      = Complex.exp (-(γ * (C z : ℝ)) * Complex.I) * ψ z := by
  simp [phaseGate, Matrix.mulVec, dotProduct, Matrix.diagonal]

theorem applyGate_phaseGate (γ : ℝ) (C : Reg n → ℕ) (ψ : QState (Reg n)) :
    ApplyGate (phaseGate γ C) ψ
      = fun z => Complex.exp (-(γ * (C z : ℝ)) * Complex.I) * ψ z := by
  funext z
  exact phaseGate_mulVec γ C ψ z

theorem hadamardN_zero_col (y : Reg n) :
    HadamardN n y (ZeroStr n) = ((Real.sqrt 2 : ℂ)⁻¹) ^ n :=
  hadamardN_apply_zero_right y

theorem hadamardN_mulVec_ket_zero (n : ℕ) (y : Reg n) :
    ((HadamardN n).mulVec (Ket (ZeroStr n))) y = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  rw [Matrix.mulVec, dotProduct]
  calc (∑ x : Reg n, HadamardN n y x * Ket (ZeroStr n) x)
      = HadamardN n y (ZeroStr n) := by
        simp only [Ket]
        rw [Finset.sum_eq_single (ZeroStr n)]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
    _ = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := hadamardN_apply_zero_right y

theorem hadamardN_ket_zero_apply (n : ℕ) (y : Reg n) :
    ApplyGate (HadamardN n) (Ket (ZeroStr n)) y = ((Real.sqrt 2 : ℂ)⁻¹) ^ n :=
  hadamardN_mulVec_ket_zero n y

theorem inv_sqrt_two_pow_mul_self (n : ℕ) :
    ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n
      = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← mul_pow, Qatlib.Foundations.PureStateMath.inv_sqrt2_mul_self,
    inv_pow]

noncomputable def Htilde : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => (Real.sqrt 2 : ℂ)⁻¹ * (if a = b then 1 else -Complex.I)

noncomputable def HtildeN (n : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => ∏ i, Htilde (x i) (y i)

noncomputable def qaoaState (n : ℕ) (C : Reg n → ℕ) : QState (Reg n) :=
  ApplyGate (HtildeN n)
    (ApplyGate (phaseGate (Real.pi / 4) C)
      (ApplyGate (HadamardN n) (Ket (ZeroStr n))))

noncomputable def qaoaProb (n : ℕ) (C : Reg n → ℕ) (z : Reg n) : ℝ :=
  BornProb (qaoaState n C) z

theorem qaoaProb_eq_matrix_element (n : ℕ) (C : Reg n → ℕ) (z : Reg n) :
    qaoaProb n C z
      = ‖∑ y : Reg n, HtildeN n z y *
          (Complex.exp (-((Real.pi / 4) * (C y : ℝ)) * Complex.I) *
            HadamardN n y (ZeroStr n))‖ ^ 2 := by
  have hphase : (phaseGate (Real.pi / 4) C).mulVec
      ((HadamardN n).mulVec (Ket (ZeroStr n)))
      = fun y => Complex.exp (-((Real.pi / 4) * (C y : ℝ)) * Complex.I) *
          ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
    funext y
    rw [phaseGate_mulVec, hadamardN_mulVec_ket_zero]
    congr 1
    congr 1
    push_cast
    ring
  unfold qaoaProb BornProb qaoaState
  simp only [ApplyGate]
  rw [hphase, Matrix.mulVec, dotProduct]
  simp only [hadamardN_apply_zero_right]

theorem qaoaProb_nonneg (n : ℕ) (C : Reg n → ℕ) (z : Reg n) : 0 ≤ qaoaProb n C z :=
  bornProb_nonneg (qaoaState n C) z

noncomputable def betaZeroState (γ : ℝ) (C : Reg n → ℕ) : QState (Reg n) :=
  ApplyGate (phaseGate γ C) (ApplyGate (HadamardN n) (Ket (ZeroStr n)))

noncomputable def matrixElement (γ : ℝ) (C : Reg n → ℕ) : ℂ :=
  ∑ y : Reg n, HadamardN n (ZeroStr n) y * betaZeroState γ C y

noncomputable def cspAmplitude (γ : ℝ) (C : Reg n → ℕ) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ z : Reg n, Complex.exp (-(γ * (C z : ℝ)) * Complex.I)

theorem betaZeroState_apply (γ : ℝ) (C : Reg n → ℕ) (y : Reg n) :
    betaZeroState γ C y
      = Complex.exp (-(γ * (C y : ℝ)) * Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  unfold betaZeroState
  rw [applyGate_phaseGate]
  simp only [hadamardN_ket_zero_apply]

theorem matrixElement_eq_cspAmplitude (γ : ℝ) (C : Reg n → ℕ) :
    matrixElement γ C = cspAmplitude γ C := by
  unfold matrixElement cspAmplitude
  calc (∑ y : Reg n, HadamardN n (ZeroStr n) y * betaZeroState γ C y)
      = ∑ y : Reg n, ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
          (Complex.exp (-(γ * (C y : ℝ)) * Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) ^ n) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hadamardN_apply_zero_left, betaZeroState_apply]
    _ = (((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n) *
          ∑ y : Reg n, Complex.exp (-(γ * (C y : ℝ)) * Complex.I) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
    _ = ((2 : ℂ) ^ n)⁻¹ *
          ∑ y : Reg n, Complex.exp (-(γ * (C y : ℝ)) * Complex.I) := by
        rw [inv_sqrt_two_pow_mul_self]

noncomputable def phaseAngle (m r : ℕ) : ℝ :=
  2 * Real.pi * (r : ℝ) / ((m : ℝ) + 1)

end Qatlib.Papers.QAOASupremacy16.CircuitDefs
