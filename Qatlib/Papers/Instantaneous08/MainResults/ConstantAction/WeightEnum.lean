/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.XProgram
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Weight enumerators for zero-output probabilities

This module defines the homogeneous weight enumerator `WEP` of a finite set of Boolean paths and
groups it by the integer coefficients `weightCount`. For constant-action X-programs, the
zero-output probability is the squared norm of this enumerator evaluated at cosine and imaginary
sine, giving the weight-enumerator identities underlying Lemma 4 of [ShepherdBremner2009].

## Main statements

* `prob_zero_eq_normSq_WEP`: expresses the zero-output probability through the kernel-path
  weight enumerator.
* `WEP_eq_weightCount`: expands the enumerator by Hamming weight.
* `prob_zero_eq_of_weightCount_eq`: shows that equal kernel weight counts give equal zero-output
  probabilities.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

attribute [local instance] Classical.propDecidable

/-- The number of true coordinates in a Boolean path. -/
def wPath {k : ℕ} (a : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => a i)).card

/-- The finite set of Boolean paths whose selected program rows sum to zero. -/
def kerPaths {n k : ℕ} (p : Fin k → F2Vec n) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun a => pathSample p a = 0)

/-- The homogeneous weight enumerator of `K`, with monomial `x ^ (k - wPath a) * y ^ wPath a`
for each path. -/
def WEP {k : ℕ} (K : Finset (Fin k → Bool)) (x y : ℂ) : ℂ :=
  ∑ a ∈ K, x ^ (k - wPath a) * y ^ (wPath a)

/-- At constant action, a path weight is a cosine power times a power of `I * sin θ`, with
exponents given by its Hamming weight. -/
theorem pathWeight_const_eq_pow {k : ℕ} (θ : ℝ) (a : Fin k → Bool) :
    pathWeight (fun _ => θ) a =
      (Real.cos θ : ℂ) ^ (k - wPath a) * (Complex.I * (Real.sin θ : ℂ)) ^ (wPath a) := by
  unfold pathWeight wPath pathCoeff
  rw [Finset.prod_ite (f := fun _ => Complex.I * (Real.sin θ : ℂ))
    (g := fun _ => (Real.cos θ : ℂ))]
  rw [Finset.prod_const, Finset.prod_const]
  have hcard : (Finset.univ.filter (fun i : Fin k => ¬ a i)).card =
      k - (Finset.univ.filter (fun i : Fin k => a i)).card := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
      (p := fun i => a i)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [hcard]
  exact mul_comm _ _

/-- The zero-output path sum is the kernel-path weight enumerator evaluated at `cos θ` and `I *
sin θ`. See [ShepherdBremner2009]. -/
theorem pathSum_zero_eq_WEP {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) :
    pathSum p (fun _ => θ) 0 =
      WEP (kerPaths p) (Real.cos θ) (Complex.I * (Real.sin θ : ℂ)) := by
  unfold pathSum WEP kerPaths
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  rw [pathWeight_const_eq_pow]
  by_cases h : pathSample p a = 0 <;> simp [h]

/-- The zero-output probability is the squared norm of the kernel-path weight enumerator at `cos
θ` and `I * sin θ`. See [ShepherdBremner2009]. -/
theorem prob_zero_eq_normSq_WEP {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) :
    prob p (fun _ => θ) 0 =
      Complex.normSq (WEP (kerPaths p) (Real.cos θ)
        (Complex.I * (Real.sin θ : ℂ))) := by
  rw [prob_eq_pathSum, pathSum_zero_eq_WEP]

/-- The weight enumerator evaluated at `(1, 1)` equals the cardinality of the path set. See
[ShepherdBremner2009]. -/
theorem WEP_one_one_eq_card {k : ℕ} (K : Finset (Fin k → Bool)) :
    WEP K 1 1 = (K.card : ℂ) := by
  unfold WEP
  have hterm : ∀ a ∈ K, (1 : ℂ) ^ (k - wPath a) * (1 : ℂ) ^ (wPath a) = 1 := by
    intro a _; simp
  calc ∑ a ∈ K, (1 : ℂ) ^ (k - wPath a) * (1 : ℂ) ^ (wPath a)
      = ∑ a ∈ K, (1 : ℂ) := Finset.sum_congr rfl hterm
    _ = (K.card : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The number of paths in `K` with Hamming weight `m`. See [ShepherdBremner2009]. -/
def weightCount {k : ℕ} (K : Finset (Fin k → Bool)) (m : ℕ) : ℕ :=
  (K.filter (fun a => wPath a = m)).card

/-- The Hamming weight of a Boolean path of length `k` is at most `k`. -/
theorem wPath_le {k : ℕ} (a : Fin k → Bool) : wPath a ≤ k := by
  unfold wPath
  calc (Finset.univ.filter (fun i => a i)).card
      ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp

/-- Expands the weight enumerator as a sum over weights from zero to `k`, with coefficients
`weightCount K m`. See [ShepherdBremner2009]. -/
theorem WEP_eq_weightCount {k : ℕ} (K : Finset (Fin k → Bool)) (x y : ℂ) :
    WEP K x y =
      ∑ m ∈ Finset.range (k + 1), (weightCount K m : ℂ) * x ^ (k - m) * y ^ m := by
  unfold WEP weightCount
  calc ∑ a ∈ K, x ^ (k - wPath a) * y ^ (wPath a)
      = ∑ a ∈ K, ∑ m ∈ Finset.range (k + 1),
          (if wPath a = m then x ^ (k - m) * y ^ m else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single (wPath a)]
        · simp
        · intro m _ hm
          rw [if_neg (fun h => hm h.symm)]
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (wPath_le a))) h
    _ = ∑ m ∈ Finset.range (k + 1), ∑ a ∈ K,
          (if wPath a = m then x ^ (k - m) * y ^ m else 0) := Finset.sum_comm
    _ = ∑ m ∈ Finset.range (k + 1),
          ((K.filter (fun a => wPath a = m)).card : ℂ) * x ^ (k - m) * y ^ m := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- Two finite path sets with the same count at every weight have equal weight enumerators. See
[ShepherdBremner2009]. -/
theorem WEP_determined_by_weights {k : ℕ} (K K' : Finset (Fin k → Bool))
    (h : ∀ m, weightCount K m = weightCount K' m) (x y : ℂ) :
    WEP K x y = WEP K' x y := by
  rw [WEP_eq_weightCount, WEP_eq_weightCount]
  apply Finset.sum_congr rfl
  intro m _
  rw [h m]

/-- Evaluating the second variable of the weight enumerator at one leaves a sum of powers of the
first variable weighted by `weightCount`. See [ShepherdBremner2009]. -/
theorem WEP_at_one {k : ℕ} (K : Finset (Fin k → Bool)) (x : ℂ) :
    WEP K x 1 =
      ∑ m ∈ Finset.range (k + 1), (weightCount K m : ℂ) * x ^ (k - m) := by
  rw [WEP_eq_weightCount]
  apply Finset.sum_congr rfl
  intro m _
  rw [one_pow, mul_one]

/-- Expresses the zero-output probability as the squared norm of the cosine-sine sum grouped by
kernel-path weights. See [ShepherdBremner2009]. -/
theorem prob_zero_eq_weightSum {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) :
    prob p (fun _ => θ) 0 =
      Complex.normSq (∑ m ∈ Finset.range (k + 1),
        (weightCount (kerPaths p) m : ℂ) * (Real.cos θ : ℂ) ^ (k - m) *
          (Complex.I * (Real.sin θ : ℂ)) ^ m) := by
  rw [prob_zero_eq_normSq_WEP, WEP_eq_weightCount]

/-- Programs with equal kernel-path weight counts have the same zero-output probability at every
constant action. See [ShepherdBremner2009]. -/
theorem prob_zero_eq_of_weightCount_eq {n k : ℕ} (p q : Fin k → F2Vec n)
    (h : ∀ m, weightCount (kerPaths p) m = weightCount (kerPaths q) m) (θ : ℝ) :
    prob p (fun _ => θ) 0 = prob q (fun _ => θ) 0 := by
  rw [prob_zero_eq_weightSum, prob_zero_eq_weightSum]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [h m]

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
