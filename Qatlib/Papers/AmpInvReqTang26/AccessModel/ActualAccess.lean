/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualNorm
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Preparation-oracle algorithms and amplitude tasks

Defines `PreparationAlgorithm`, whose normalized initial state and unitary interleaving steps
use the preparation oracle on the data register. The reduced output `preparationOutput` is
compared with the normalized good component for amplification, while estimation uses the Born
mass of outcomes whose assigned values approximate the preparation amplitude. See
[TangWright2025].

## Main statements

* `SolvesAmplification`: uniform trace-distance accuracy for the good-state target under an
  amplitude promise.
* `SolvesEstimation`: uniform estimation success probability at least 0.99.
* `preparationRun_normalized`: unitary oracle runs remain normalized.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Kronecker
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.ForwardHist

/-- A preparation-oracle algorithm with a designated input, a good-data predicate, a normalized
initial state, unitary interleaving steps, and real values assigned to measurement outcomes. -/
structure PreparationAlgorithm (I A : Type*) [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A] where

  start : I

  goodData : I → Bool

  init : I×A → ℂ

  hinit : ∑x,‖init x‖^2=1

  step : ℕ → Matrix (I×A) (I×A) ℂ

  hstep : ∀t,(step t)ᴴ*step t=1

  value : I×A → ℝ

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

/-- The preparation oracle `X` tensored with the identity on the auxiliary register. -/
def preparationQuery (X : Matrix I I ℂ) : Matrix (I×A) (I×A) ℂ := X ⊗ₖ (1 : Matrix A A ℂ)

/-- The state after `n` forward uses of the preparation oracle, interleaved with the algorithm's
unitary steps. -/
def preparationRun (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ) : ℕ → I×A → ℂ
  | 0 => Alg.step 0 *ᵥ Alg.init
  | n+1 => Alg.step (n+1) *ᵥ (preparationQuery X *ᵥ preparationRun Alg X n)

omit [Fintype A] [DecidableEq A] in

/-- The squared mass of the good coordinates in the column of `X` indexed by `start`. -/
def preparationGoodMass (start : I) (good : I → Bool) (X : Matrix I I ℂ) : ℝ :=
  ∑i,if good i then ‖X i start‖^2 else 0

omit [Fintype A] [DecidableEq A] in

/-- The square root of `preparationGoodMass start good X`. -/
def preparationAmplitude (start : I) (good : I → Bool) (X : Matrix I I ℂ) : ℝ :=
  Real.sqrt (preparationGoodMass start good X)

omit [Fintype A] [DecidableEq A] in

/-- The good part of the designated column of `X`, divided by its preparation amplitude. -/
def preparationGoodVector (start : I) (good : I → Bool) (X : Matrix I I ℂ) : I → ℂ :=
  fun i => if good i then X i start / (preparationAmplitude start good X:ℂ) else 0

/-- The reduced data-register matrix of the algorithm's output after `n` oracle uses, obtained
by summing over the auxiliary register. -/
def preparationOutput (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ) (n : ℕ) : Matrix I I ℂ :=
  fun i j => ∑a,preparationRun Alg X n (i,a)*star (preparationRun Alg X n (j,a))

/-- For every unitary preparation oracle with positive amplitude at least `a0`, the reduced
output is within trace distance 0.01 of the normalized good-state projector [Tang and
Wright, Problem 1.1][TangWright2025]. -/
def SolvesAmplification (Alg : PreparationAlgorithm I A) (n : ℕ) (a0 : ℝ) : Prop :=
  ∀ X : Matrix I I ℂ, Xᴴ*X=1 →
    a0≤preparationAmplitude Alg.start Alg.goodData X →
    0<preparationAmplitude Alg.start Alg.goodData X →
    Matrix.traceNorm (preparationOutput Alg X n-
      Matrix.vecMulVec (preparationGoodVector Alg.start Alg.goodData X)
        (star (preparationGoodVector Alg.start Alg.goodData X)))/2≤0.01

/-- For every unitary preparation oracle, outcomes with an assigned estimate within strict error
`eps` of its amplitude have Born mass at least 0.99 [Tang and Wright, Problem
1.1][TangWright2025]. -/
def SolvesEstimation (Alg : PreparationAlgorithm I A) (n : ℕ) (eps : ℝ) : Prop :=
  ∀ X : Matrix I I ℂ, Xᴴ*X=1 →
    (∑x,if |Alg.value x-preparationAmplitude Alg.start Alg.goodData X|<eps
      then ‖preparationRun Alg X n x‖^2 else 0)≥0.99

/-- Tensoring a unitary preparation oracle with the auxiliary identity preserves the equation
`Xᴴ * X = 1`. -/
theorem preparationQuery_unitary (X : Matrix I I ℂ) (hX : Xᴴ*X=1) :
    (preparationQuery (A := A) X)ᴴ*preparationQuery X=1 := by
  simp only [preparationQuery,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,hX,Matrix.one_mul,Matrix.one_kronecker_one]

/-- For a unitary preparation oracle, the state after any number of oracle uses has total
squared mass one. -/
theorem preparationRun_normalized (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ)
    (hX : Xᴴ*X=1) (n : ℕ) : ∑x,‖preparationRun Alg X n x‖^2=1 := by
  induction n with
  | zero => exact (unitary_normSq _ (Alg.hstep 0) Alg.init).trans Alg.hinit
  | succ n ih =>
    simp only [preparationRun]
    rw [unitary_normSq _ (Alg.hstep (n+1)),unitary_normSq _ (preparationQuery_unitary X hX)]
    exact ih

omit [Fintype A] [DecidableEq A] in

/-- For a unitary preparation oracle, the preparation amplitude lies in the interval `[0, 1]`. -/
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

/-- If the preparation amplitude is positive, the vector `preparationGoodVector` has total
squared mass one. -/
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
