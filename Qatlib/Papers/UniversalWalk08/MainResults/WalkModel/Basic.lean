/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

namespace Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore

open Matrix
open scoped Matrix

set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsZeroOneHermitianAdjacency (A : Matrix V V ℂ) : Prop :=
  (∀ i j, A i j = 0 ∨ A i j = 1) ∧ Aᴴ = A

def MaxDegreeLe (A : Matrix V V ℂ) (d : ℕ) : Prop :=
  ∀ i, ∑ j, (A i j).re ≤ (d : ℝ)

noncomputable def walkPropagator (A : Matrix V V ℂ) (t : ℝ) : Matrix V V ℂ :=
  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • A)

noncomputable def walkAmplitude (A : Matrix V V ℂ) (t : ℝ) (dest src : V) : ℂ :=
  walkPropagator A t dest src

noncomputable def walkProbability (A : Matrix V V ℂ) (t : ℝ) (dest src : V) : ℝ :=
  Complex.normSq (walkAmplitude A t dest src)

@[simp]
theorem walkPropagator_zero (A : Matrix V V ℂ) : walkPropagator A 0 = 1 := by
  unfold walkPropagator
  simp

theorem walkPropagator_mul (A : Matrix V V ℂ) (s t : ℝ) :
    walkPropagator A s * walkPropagator A t = walkPropagator A (s + t) := by
  unfold walkPropagator
  have hcomm : Commute ((-(Complex.I * (s : ℂ))) • A) ((-(Complex.I * (t : ℂ))) • A) :=
    ((Commute.refl A).smul_left _).smul_right _
  calc
    NormedSpace.exp ((-(Complex.I * (s : ℂ))) • A) *
        NormedSpace.exp ((-(Complex.I * (t : ℂ))) • A)
        = NormedSpace.exp (((-(Complex.I * (s : ℂ))) • A) +
            ((-(Complex.I * (t : ℂ))) • A)) :=
          (Matrix.exp_add_of_commute _ _ hcomm).symm
    _ = NormedSpace.exp ((-(Complex.I * ((s + t : ℝ) : ℂ))) • A) := by
          congr 1
          rw [← add_smul]
          congr 1
          push_cast
          ring

theorem walkPropagator_conjTranspose {A : Matrix V V ℂ} (hA : Aᴴ = A) (t : ℝ) :
    (walkPropagator A t)ᴴ = walkPropagator A (-t) := by
  unfold walkPropagator
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, hA]
  congr 1

  push_cast
  rw [Complex.star_def, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem walkPropagator_unitary {A : Matrix V V ℂ} (hA : Aᴴ = A) (t : ℝ) :
    (walkPropagator A t)ᴴ * walkPropagator A t = 1 ∧
      walkPropagator A t * (walkPropagator A t)ᴴ = 1 := by
  have hconj := walkPropagator_conjTranspose hA t
  constructor
  · rw [hconj, walkPropagator_mul]
    rw [show -t + t = 0 by ring, walkPropagator_zero]
  · rw [hconj, walkPropagator_mul]
    rw [show t + -t = 0 by ring, walkPropagator_zero]

omit [Fintype V] [DecidableEq V] in

theorem hermitian_of_isZeroOneHermitianAdjacency {A : Matrix V V ℂ}
    (h : IsZeroOneHermitianAdjacency A) : Aᴴ = A := h.2

theorem walkPropagator_unitary_of_adjacency {A : Matrix V V ℂ}
    (h : IsZeroOneHermitianAdjacency A) (t : ℝ) :
    (walkPropagator A t)ᴴ * walkPropagator A t = 1 ∧
      walkPropagator A t * (walkPropagator A t)ᴴ = 1 :=
  walkPropagator_unitary (hermitian_of_isZeroOneHermitianAdjacency h) t

theorem sum_walkProbability_eq_one {A : Matrix V V ℂ} (hA : Aᴴ = A) (t : ℝ)
    (src : V) :
    ∑ dest, walkProbability A t dest src = 1 := by

  have hunit : (walkPropagator A t)ᴴ * walkPropagator A t = 1 :=
    (walkPropagator_unitary hA t).1
  have hentry := congrFun (congrFun hunit src) src
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at hentry

  have hsumC : (∑ d, (((Complex.normSq ((walkPropagator A t) d src)) : ℝ) : ℂ)) = 1 := by
    rw [← hentry]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [Matrix.conjTranspose_apply]
  have hre := congrArg Complex.re hsumC
  simpa [walkProbability, walkAmplitude] using hre

end Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore
