/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceCoupling
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier
open Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
open scoped BigOperators

variable {n : ℕ}

def uniformExpect (F : (Fin n → Bool) → ℝ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ x, F x

def signFun (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℝ := fun x => if f x then 1 else -1

def dependsOnlyOn (J : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → f x = f y

def dependsOnlyOnReal (J : Finset (Fin n)) (F : (Fin n → Bool) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → F x = F y

def IsKJunta (k : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ k ∧ dependsOnlyOn J f

def disagreement (f g : (Fin n → Bool) → Bool) : ℝ :=
  uniformExpect (fun x => if f x = g x then 0 else 1)

def farFromJunta (k : ℕ) (ε : ℝ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ g, IsKJunta (n := n) k g → ε ≤ disagreement f g

def signCoeff (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  uniformFourierCoeff S (signFun f)

def fsWeight (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  signCoeff f S ^ 2

def boolInfluence (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ :=
  uniformExpect (fun x => if f x = f (cubeFlip x i) then 0 else 1)

theorem boolInfluence_nonneg (f : (Fin n → Bool) → Bool) (i : Fin n) :
    0 ≤ boolInfluence f i := by
  unfold boolInfluence uniformExpect
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro x _
    split_ifs <;> norm_num

theorem fsWeight_nonneg (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
    0 ≤ fsWeight f S := by
  unfold fsWeight
  positivity

theorem fsWeight_pos_iff (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
    0 < fsWeight f S ↔ signCoeff f S ≠ 0 := by
  unfold fsWeight
  constructor
  · intro h hzero
    rw [hzero] at h
    norm_num at h
  · intro h
    positivity

theorem signFun_flip_sq (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (i : Fin n) :
    (signFun f x - signFun f (cubeFlip x i)) ^ 2 =
      4 * (if f x = f (cubeFlip x i) then (0 : ℝ) else 1) := by
  unfold signFun
  by_cases h : f x = f (cubeFlip x i)
  · rw [if_pos h, h]; ring
  · rw [if_neg h]
    cases hx1 : f x <;> cases hx2 : f (cubeFlip x i) <;> simp_all <;> norm_num

theorem cubeInf_signFun (f : (Fin n → Bool) → Bool) (i : Fin n) :
    cubeInf n (muWeight (1 / 2) n) (signFun f) i = 4 * boolInfluence f i := by
  rw [cubeInf_uniform]
  rw [Finset.sum_congr rfl (fun x _ => signFun_flip_sq f x i)]
  rw [← Finset.mul_sum]
  unfold boolInfluence uniformExpect
  ring

theorem boolInfluence_eq_sum_fsWeight (f : (Fin n → Bool) → Bool) (i : Fin n) :
    boolInfluence f i = ∑ S : Finset (Fin n), if i ∈ S then fsWeight f S else 0 := by
  have hfour : 4 * boolInfluence f i =
      4 * ∑ S : Finset (Fin n), if i ∈ S then fsWeight f S else 0 := by
    rw [← cubeInf_signFun, cubeInf_fourier]
    unfold fsWeight signCoeff
    rfl

  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ h4 hfour

theorem boolInfluence_pos_of_mem_fsWeight (f : (Fin n → Bool) → Bool)
    {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) (hS : 0 < fsWeight f S) :
    0 < boolInfluence f j := by
  rw [boolInfluence_eq_sum_fsWeight]
  have hterm : (if j ∈ S then fsWeight f S else 0) ≤
      ∑ T : Finset (Fin n), if j ∈ T then fsWeight f T else 0 :=
    Finset.single_le_sum (f := fun T => if j ∈ T then fsWeight f T else 0)
      (fun T _ => by
        (try dsimp only)
        split_ifs with hT
        · exact fsWeight_nonneg f T
        · norm_num)
      (Finset.mem_univ S)
  have hpos : 0 < (if j ∈ S then fsWeight f S else 0) := by
    rw [if_pos hj]; exact hS
  exact lt_of_lt_of_le hpos hterm

theorem signFun_dependsOnlyOnReal {J : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : dependsOnlyOn J f) : dependsOnlyOnReal J (signFun f) := by
  intro x y hxy
  unfold signFun
  rw [hf x y hxy]

theorem signCoeff_eq_zero_of_not_subset {J : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : dependsOnlyOn J f) {S : Finset (Fin n)} (hS : ¬ S ⊆ J) :
    signCoeff f S = 0 := by
  classical
  unfold signCoeff uniformFourierCoeff
  obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hS
  let A : (Fin n → Bool) → ℝ := fun x => cubeChar S x * signFun f x

  have hchar : ∀ x : Fin n → Bool, A (cubeFlip x i) = -A x := by
    intro x
    have hc : cubeChar S (cubeFlip x i) = -cubeChar S x := by
      rw [cubeChar_flip, if_pos hiS]
    have hf' : signFun f (cubeFlip x i) = signFun f x := by
      apply signFun_dependsOnlyOnReal hf
      intro j hj
      have hji : j ≠ i := by intro h; subst j; exact hiJ hj
      simp [cubeFlip, hji]
    simp only [A, hc, hf']
    ring
  have hcomp : ∑ x : Fin n → Bool, A (cubeFlip x i) = ∑ x : Fin n → Bool, A x :=
    Equiv.sum_comp (cubeFlipEquiv i) A
  have hcharSum : ∑ x : Fin n → Bool, A (cubeFlip x i) = ∑ x : Fin n → Bool, -A x :=
    Finset.sum_congr rfl (fun x _ => hchar x)

  have hEq : ∑ x : Fin n → Bool, -A x = ∑ x : Fin n → Bool, A x :=
    hcharSum.symm.trans hcomp
  have hzero : (∑ x : Fin n → Bool, A x) + ∑ x : Fin n → Bool, -A x = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    simp
  rw [hEq] at hzero
  have htwo : (2 : ℝ) * ∑ x : Fin n → Bool, A x = 0 := by
    rw [two_mul]
    exact hzero
  have hsum : ∑ x : Fin n → Bool, A x = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [show ∑ x : Fin n → Bool, cubeChar S x * signFun f x = 0 from hsum]
  ring

end Qatlib.Papers.JuntaLearning07.MainResults
