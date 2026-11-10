/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.StochasticFrame.Reflection
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.AlgebraMap
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Concepts.PolynomialCalc.QubitizedPower
open Qatlib.Foundations.MatrixGeometry.StochasticFrame
variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

def walk (C : Matrix M N ℂ) (U : Matrix M M ℂ) := rangeReflection C*U

def signal (C : Matrix M N ℂ) (U : Matrix M M ℂ) := Cᴴ*U*C

theorem reflection_frame (C : Matrix M N ℂ) (hC : Cᴴ*C=1) : rangeReflection C*C=C := by
  unfold rangeReflection
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_assoc,hC,Matrix.mul_one,Matrix.one_mul]
  simp only [two_smul]
  abel

theorem walk_unitary (C : Matrix M N ℂ) (U : Matrix M M ℂ) (hC : Cᴴ*C=1)
    (hU : Uᴴ=U) (hU2 : U*U=1) : (walk C U)ᴴ*walk C U=1 := by
  unfold walk
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Uᴴ*((rangeReflection C)ᴴ*rangeReflection C)*U := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [rangeReflection_unitary C hC,Matrix.mul_one,hU,hU2]
omit [DecidableEq N] in

theorem walk_frame_sum (C : Matrix M N ℂ) (U : Matrix M M ℂ) :
    walk C U*C+U*C=(2 : ℂ)•(C*signal C U) := by
  unfold walk rangeReflection signal
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc]
  abel

theorem walk_backward (C : Matrix M N ℂ) (U : Matrix M M ℂ) (hC : Cᴴ*C=1)
    (hU2 : U*U=1) : walk C U*(U*C)=C := by
  unfold walk
  rw [Matrix.mul_assoc,← Matrix.mul_assoc U U C,hU2,Matrix.one_mul,reflection_frame C hC]

theorem walk_square_frame (C : Matrix M N ℂ) (U : Matrix M M ℂ) (hC : Cᴴ*C=1)
    (hU2 : U*U=1) : walk C U^2*C=(2 : ℂ)•(walk C U*C*signal C U)-C := by
  have hs := congrArg (fun X : Matrix M N ℂ => walk C U*X) (walk_frame_sum C U)
  try dsimp only at hs
  rw [Matrix.mul_add,walk_backward C U hC hU2,Matrix.mul_smul] at hs
  simp only [← Matrix.mul_assoc,pow_two] at hs ⊢
  exact eq_sub_of_add_eq hs

theorem compressed_recurrence (C : Matrix M N ℂ) (U : Matrix M M ℂ) (hC : Cᴴ*C=1)
    (hU2 : U*U=1) (n : ℕ) :
    Cᴴ*walk C U^(n+2)*C=(2 : ℂ)•((Cᴴ*walk C U^(n+1)*C)*signal C U)-Cᴴ*walk C U^n*C := by
  calc
    _ = Cᴴ*(walk C U^n*(walk C U^2*C)) := by simp only [pow_add,Matrix.mul_assoc]
    _ = Cᴴ*(walk C U^n*((2 : ℂ)•(walk C U*C*signal C U)-C)) := by
      rw [walk_square_frame C U hC hU2]
    _ = _ := by
      simp only [Matrix.mul_sub,Matrix.mul_smul,pow_succ,Matrix.mul_assoc]

theorem compressed_chebyshev (C : Matrix M N ℂ) (U : Matrix M M ℂ) (hC : Cᴴ*C=1)
    (hU2 : U*U=1) (n : ℕ) :
    Cᴴ*walk C U^n*C=Polynomial.aeval (signal C U) (Polynomial.Chebyshev.T ℂ (n : ℤ)) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hC
  | one =>
    have hleft : Cᴴ*rangeReflection C=Cᴴ := by
      have hh := congrArg Matrix.conjTranspose (reflection_frame C hC)
      simpa only [Matrix.conjTranspose_mul,rangeReflection_adjoint,Matrix.conjTranspose_conjTranspose] using hh
    simp [walk,signal,← Matrix.mul_assoc,hleft]
  | more n hn hn1 =>
    rw [compressed_recurrence C U hC hU2 n,hn,hn1]
    have ht : Polynomial.Chebyshev.T ℂ ((n+2 : ℕ) : ℤ)=
        2*Polynomial.Chebyshev.T ℂ ((n+1 : ℕ) : ℤ)*Polynomial.X-
          Polynomial.Chebyshev.T ℂ (n : ℤ) := by
      push_cast
      rw [Polynomial.Chebyshev.T_add_two]
      ring
    rw [ht]
    simp only [map_sub,map_mul,map_ofNat,Polynomial.aeval_X]
    simp only [two_smul]
    noncomm_ring
end Qatlib.Concepts.PolynomialCalc.QubitizedPower
