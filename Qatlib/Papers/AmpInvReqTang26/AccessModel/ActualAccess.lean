/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualNorm
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Kronecker
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.ForwardHist

structure PreparationAlgorithm (I A : Type*) [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A] where

  start : I

  goodData : I → Bool

  init : I×A → ℂ

  hinit : ∑x,‖init x‖^2=1

  step : ℕ → Matrix (I×A) (I×A) ℂ

  hstep : ∀t,(step t)ᴴ*step t=1

  value : I×A → ℝ

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

def preparationQuery (X : Matrix I I ℂ) : Matrix (I×A) (I×A) ℂ := X ⊗ₖ (1 : Matrix A A ℂ)

def preparationRun (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ) : ℕ → I×A → ℂ
  | 0 => Alg.step 0 *ᵥ Alg.init
  | n+1 => Alg.step (n+1) *ᵥ (preparationQuery X *ᵥ preparationRun Alg X n)

omit [Fintype A] [DecidableEq A] in

def preparationGoodMass (start : I) (good : I → Bool) (X : Matrix I I ℂ) : ℝ :=
  ∑i,if good i then ‖X i start‖^2 else 0

omit [Fintype A] [DecidableEq A] in

def preparationAmplitude (start : I) (good : I → Bool) (X : Matrix I I ℂ) : ℝ :=
  Real.sqrt (preparationGoodMass start good X)

omit [Fintype A] [DecidableEq A] in

def preparationGoodVector (start : I) (good : I → Bool) (X : Matrix I I ℂ) : I → ℂ :=
  fun i => if good i then X i start / (preparationAmplitude start good X:ℂ) else 0

def preparationOutput (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ) (n : ℕ) : Matrix I I ℂ :=
  fun i j => ∑a,preparationRun Alg X n (i,a)*star (preparationRun Alg X n (j,a))

def SolvesAmplification (Alg : PreparationAlgorithm I A) (n : ℕ) (a0 : ℝ) : Prop :=
  ∀ X : Matrix I I ℂ, Xᴴ*X=1 →
    a0≤preparationAmplitude Alg.start Alg.goodData X →
    0<preparationAmplitude Alg.start Alg.goodData X →
    Matrix.traceNorm (preparationOutput Alg X n-
      Matrix.vecMulVec (preparationGoodVector Alg.start Alg.goodData X)
        (star (preparationGoodVector Alg.start Alg.goodData X)))/2≤0.01

def SolvesEstimation (Alg : PreparationAlgorithm I A) (n : ℕ) (eps : ℝ) : Prop :=
  ∀ X : Matrix I I ℂ, Xᴴ*X=1 →
    (∑x,if |Alg.value x-preparationAmplitude Alg.start Alg.goodData X|<eps
      then ‖preparationRun Alg X n x‖^2 else 0)≥0.99

theorem preparationQuery_unitary (X : Matrix I I ℂ) (hX : Xᴴ*X=1) :
    (preparationQuery (A := A) X)ᴴ*preparationQuery X=1 := by
  simp only [preparationQuery,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,hX,Matrix.one_mul,Matrix.one_kronecker_one]

theorem preparationRun_normalized (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ)
    (hX : Xᴴ*X=1) (n : ℕ) : ∑x,‖preparationRun Alg X n x‖^2=1 := by
  induction n with
  | zero => exact (unitary_normSq _ (Alg.hstep 0) Alg.init).trans Alg.hinit
  | succ n ih =>
    simp only [preparationRun]
    rw [unitary_normSq _ (Alg.hstep (n+1)),unitary_normSq _ (preparationQuery_unitary X hX)]
    exact ih

omit [Fintype A] [DecidableEq A] in

theorem preparationAmplitude_bounds (start : I) (good : I → Bool) (X : Matrix I I ℂ)
    (hX : Xᴴ*X=1) : 0≤preparationAmplitude start good X ∧ preparationAmplitude start good X≤1 := by
  have hn := unitary_normSq X hX (Pi.single start 1)
  simp only [Matrix.mulVec_single_one] at hn
  have hs : (∑i : I,‖(Pi.single start (1:ℂ) : I → ℂ) i‖^2)=1 := by
    rw [Finset.sum_eq_single start]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [hs] at hn
  have hnon : 0≤preparationGoodMass start good X :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  have hmass : preparationGoodMass start good X≤1 := by
    rw [preparationGoodMass]
    calc
      _ ≤ ∑i,‖X i start‖^2 := Finset.sum_le_sum (fun i _ => by split_ifs <;> simp)
      _ = 1 := hn
  refine ⟨Real.sqrt_nonneg _,?_⟩
  exact Real.sqrt_le_one.mpr hmass

omit [Fintype A] [DecidableEq A] [DecidableEq I] in

theorem preparationGoodVector_normalized (start : I) (good : I → Bool) (X : Matrix I I ℂ)
    (ha : 0<preparationAmplitude start good X) :
    ∑i,‖preparationGoodVector start good X i‖^2=1 := by
  have hm : 0≤preparationGoodMass start good X :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  have hp (i : I) : ‖preparationGoodVector start good X i‖^2 =
      (if good i then ‖X i start‖^2 else 0)/(preparationAmplitude start good X)^2 := by
    cases hi : good i <;> simp [preparationGoodVector,hi,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos ha,div_pow]
  rw [Finset.sum_congr rfl (fun i _ => hp i),← Finset.sum_div]
  change preparationGoodMass start good X/(preparationAmplitude start good X)^2=1
  have hne : preparationGoodMass start good X≠0 := by
    intro hz
    simp [preparationAmplitude,hz] at ha
  rw [preparationAmplitude,Real.sq_sqrt hm,div_self hne]

end Qatlib.Papers.AmpInvReqTang26.AccessModel
