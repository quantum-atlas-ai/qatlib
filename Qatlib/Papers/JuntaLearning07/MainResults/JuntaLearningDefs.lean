/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceCoupling
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence

/-!
# Boolean juntas and Fourier-sampling weights

This module sets up the uniform Boolean-cube quantities used to study quantum learning and
testing of juntas in [AticiServedio2007]. It defines uniform expectation, the sign
representation `signFun`, coordinate dependence through `dependsOnlyOn` and `IsKJunta`, and
uniform disagreement through `disagreement` and `farFromJunta`.

The Fourier coefficient `signCoeff` and its square `fsWeight` connect the Boolean target with
Fourier sampling. `boolInfluence_eq_sum_fsWeight` identifies coordinate influence with the total
Fourier weight of sets containing that coordinate, and `signCoeff_eq_zero_of_not_subset`
confines Fourier support to any determining coordinate set.

## Main statements

- `fsWeight_pos_iff` characterizes positive Fourier-sampling weight by a nonzero coefficient.
* `cubeInf_signFun` relates the real-valued cube influence of the sign representation to Boolean
  influence.
* `boolInfluence_eq_sum_fsWeight` expresses influence as Fourier mass on sets containing the
  coordinate.
- `signCoeff_eq_zero_of_not_subset` gives vanishing coefficients outside a determining set.

## References

* [Atici and Servedio, 2007][AticiServedio2007], Quantum Algorithms for Learning and Testing
  Juntas.
-/

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

/-- The expectation of a real-valued function under the uniform distribution on the
`n`-dimensional Boolean cube. -/
def uniformExpect (F : (Fin n → Bool) → ℝ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ x, F x

/-- The real-valued sign representation of a Boolean function, sending `true` to `1` and `false`
to `-1`. -/
def signFun (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℝ := fun x => if f x then 1 else -1

/-- The property that a Boolean function has equal values on any two inputs agreeing on every
coordinate in `J`. -/
def dependsOnlyOn (J : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → f x = f y

/-- The property that a real-valued cube function has equal values on any two inputs agreeing on
every coordinate in `J`. -/
def dependsOnlyOnReal (J : Finset (Fin n)) (F : (Fin n → Bool) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → F x = F y

/-- The property that a Boolean function depends only on some set of at most `k` coordinates. -/
def IsKJunta (k : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ k ∧ dependsOnlyOn J f

/-- The uniform probability that the Boolean functions `f` and `g` take different values. -/
def disagreement (f g : (Fin n → Bool) → Bool) : ℝ :=
  uniformExpect (fun x => if f x = g x then 0 else 1)

/-- The property that `f` has uniform disagreement at least `ε` with every `k`-junta. -/
def farFromJunta (k : ℕ) (ε : ℝ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ g, IsKJunta (n := n) k g → ε ≤ disagreement f g

/-- The uniform Fourier coefficient of the sign representation of `f` at the coordinate set `S`. -/
def signCoeff (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  uniformFourierCoeff S (signFun f)

/-- The Fourier-sampling weight of `S`, defined as the square of the sign Fourier coefficient of
`f` at `S`. -/
def fsWeight (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  signCoeff f S ^ 2

/-- The uniform probability that flipping coordinate `i` changes the value of `f`. -/
def boolInfluence (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ :=
  uniformExpect (fun x => if f x = f (cubeFlip x i) then 0 else 1)

/-- The Boolean influence of every coordinate is nonnegative. -/
theorem boolInfluence_nonneg (f : (Fin n → Bool) → Bool) (i : Fin n) :
    0 ≤ boolInfluence f i := by
  unfold boolInfluence uniformExpect
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro x _
    split_ifs <;> norm_num

/-- Every Fourier-sampling weight is nonnegative. -/
theorem fsWeight_nonneg (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
    0 ≤ fsWeight f S := by
  unfold fsWeight
  positivity

/-- A coordinate set has positive Fourier-sampling weight exactly when its sign Fourier
coefficient is nonzero. -/
theorem fsWeight_pos_iff (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
    0 < fsWeight f S ↔ signCoeff f S ≠ 0 := by
  unfold fsWeight
  constructor
  · intro h hzero
    rw [hzero] at h
    norm_num at h
  · intro h
    positivity

/-- The squared change in the sign representation under a coordinate flip equals four times the
indicator that the Boolean value changes. -/
theorem signFun_flip_sq (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (i : Fin n) :
    (signFun f x - signFun f (cubeFlip x i)) ^ 2 =
      4 * (if f x = f (cubeFlip x i) then (0 : ℝ) else 1) := by
  unfold signFun
  by_cases h : f x = f (cubeFlip x i)
  · rw [if_pos h, h]; ring
  · rw [if_neg h]
    cases hx1 : f x <;> cases hx2 : f (cubeFlip x i) <;> simp_all <;> norm_num

/-- At uniform cube weight, the real cube influence of the sign representation is four times the
corresponding Boolean influence. -/
theorem cubeInf_signFun (f : (Fin n → Bool) → Bool) (i : Fin n) :
    cubeInf n (muWeight (1 / 2) n) (signFun f) i = 4 * boolInfluence f i := by
  rw [cubeInf_uniform]
  rw [Finset.sum_congr rfl (fun x _ => signFun_flip_sq f x i)]
  rw [← Finset.mul_sum]
  unfold boolInfluence uniformExpect
  ring

/-- The influence of coordinate `i` equals the total Fourier-sampling weight of all coordinate
sets containing `i`. -/
theorem boolInfluence_eq_sum_fsWeight (f : (Fin n → Bool) → Bool) (i : Fin n) :
    boolInfluence f i = ∑ S : Finset (Fin n), if i ∈ S then fsWeight f S else 0 := by
  have hfour : 4 * boolInfluence f i =
      4 * ∑ S : Finset (Fin n), if i ∈ S then fsWeight f S else 0 := by
    rw [← cubeInf_signFun, cubeInf_fourier]
    unfold fsWeight signCoeff
    rfl

  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ h4 hfour

/-- Every coordinate belonging to a set of positive Fourier-sampling weight has positive Boolean
influence. -/
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

/-- If a Boolean function depends only on `J`, its real-valued sign representation also depends
only on `J`. -/
theorem signFun_dependsOnlyOnReal {J : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : dependsOnlyOn J f) : dependsOnlyOnReal J (signFun f) := by
  intro x y hxy
  unfold signFun
  rw [hf x y hxy]

/-- If `f` depends only on `J`, its sign Fourier coefficient at `S` vanishes whenever `S`
contains a coordinate outside `J`. -/
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
