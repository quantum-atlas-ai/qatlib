/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.PositiveBranchDecomposition
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Positive decompositions of the identity map

`qudit_positive_family_scalar_one` studies finite families of complex linear maps that preserve
positive semidefinite operators and sum to the identity map. It proves that every member sends
the identity operator to a scalar multiple of the identity.

The proof uses positivity on pure inputs and a Hermitian matrix identity for balanced pairs of
basis vectors. This is a finite dimensional positive map argument in the setting of
[Watrous2018].

## Main statements

* `balanced_pair`: equality of diagonal entries from an annihilated balanced vector.
* `qudit_positive_family_scalar_one`: scalar images of the identity under positive summands.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators ComplexOrder
set_option linter.unusedSimpArgs false

/-- If a Hermitian matrix annihilates `Ket i + t • Ket j` for real `t` with `t² = 1`, its `i`
and `j` diagonal entries agree. -/
private theorem balanced_pair {n : ℕ} (A : Operator n) (hA : A.IsHermitian)
    (i j : Fin n) (t : ℝ) (ht : t^2 = 1)
    (hk : A *ᵥ (Qatlib.Foundations.PureStateMath.Ket i + (t : ℂ) • Qatlib.Foundations.PureStateMath.Ket j) = 0) : A i i = A j j := by
  have h0 := congrFun hk i
  have h1 := congrFun hk j
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
    mulVec_ket_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  have h10 : A j i = -(t : ℂ) * A j j := by linear_combination h1
  have hd := congrArg (fun M : Operator n => M j j) hA.eq
  have he := congrArg (fun M : Operator n => M i j) hA.eq
  simp only [Matrix.conjTranspose_apply] at hd he
  have hs : star (t : ℂ) = (t : ℂ) := by simp
  rw [h10, star_mul, star_neg, hs, hd] at he
  rw [← he] at h0
  have hc : (t : ℂ)^2 = 1 := by exact_mod_cast ht
  linear_combination h0 + (A j j) * hc

/-- If a finite family of positive complex linear maps sums to the identity map in nonzero
dimension, each map sends the identity operator to a scalar multiple of itself. -/
theorem qudit_positive_family_scalar_one (m n : ℕ) [NeZero n]
    (F : Fin m → Operator n → Operator n)
    (hadd : ∀ s A B, F s (A + B) = F s A + F s B)
    (hsmul : ∀ s (c : ℂ) A, F s (c • A) = c • F s A)
    (hpos : ∀ s A, A.PosSemidef → (F s A).PosSemidef)
    (hsum : ∀ A, ∑ s, F s A = A) :
    ∀ s, ∃ a : ℂ, F s 1 = a • (1 : Operator n) := by
  let E := fun k : Fin n => outerProduct (Qatlib.Foundations.PureStateMath.Ket k)
  have hzero (A : Operator n) (hp : A.PosSemidef) (v : Fin n → ℂ)
      (hv : A *ᵥ v = 0) : ∀ s, F s A *ᵥ v = 0 := by
    apply psd_family_kernel m (fun s => F s A) (fun s => hpos s A hp) v
    rw [hsum, hv, dotProduct_zero]
  have hcol (s : Fin m) (k j i : Fin n) (hj : j ≠ k) : F s (E k) i j = 0 := by
    have h := hzero (E k) (outerProduct_posSemidef _) (Qatlib.Foundations.PureStateMath.Ket j) (by
      rw [outerProduct_mulVec, inner_ket_ket, if_neg (Ne.symm hj), zero_smul]) s
    simpa only [mulVec_ket_apply, Pi.zero_apply] using congrFun h i
  have hentry (s : Fin m) (k i j : Fin n) :
      F s (E k) i j = if i = k ∧ j = k then F s (E k) k k else 0 := by
    by_cases hj : j = k
    · subst j
      by_cases hi : i = k
      · subst i; simp
      · have h := congrArg (fun A : Operator n => A i k)
          (hpos s (E k) (outerProduct_posSemidef _)).1.eq
        simp only [Matrix.conjTranspose_apply, hcol s k i k hi, star_zero] at h
        simp [hi, h.symm]
    · simp [hj, hcol s k j i hj]
  have hE : (∑ k, E k) = (1 : Operator n) := by
    ext i j
    simp [Matrix.sum_apply, E, outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket,
        Matrix.one_apply, mul_ite]
  have hFzero (s : Fin m) : F s 0 = 0 := by
    simpa using hsmul s 0 (0 : Operator n)
  have hFsum (s : Fin m) (T : Finset (Fin n)) :
      F s (∑ k ∈ T, E k) = ∑ k ∈ T, F s (E k) := by
    induction T using Finset.induction_on with
    | empty => simp [hFzero]
    | @insert a T ha ih => simp [ha, hadd, ih]
  have hI (s : Fin m) : F s 1 = ∑ k, F s (E k) := by
    rw [← hE]
    simpa using hFsum s Finset.univ
  have hId (s : Fin m) (i j : Fin n) :
      F s 1 i j = if i = j then F s (E i) i i else 0 := by
    rw [hI]
    simp only [Matrix.sum_apply]
    have he : (∑ k, F s (E k) i j) =
        ∑ k, if i = k ∧ j = k then F s (E k) k k else 0 :=
      Finset.sum_congr rfl (fun k _ => hentry s k i j)
    rw [he]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, show ∀ k, ¬ (i = k ∧ j = k) from fun k h => hij (h.1.trans h.2.symm)]
  have hpq (i j : Fin n) (t : ℂ) :
      Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i + t • Qatlib.Foundations.PureStateMath.Ket j) (Qatlib.Foundations.PureStateMath.Ket i - t • Qatlib.Foundations.PureStateMath.Ket j) =
        1 - t * (if i = j then 1 else 0) + star t * (if j = i then 1 else 0) - star t * t := by
    simp only [inner_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_add, map_mul, mul_sub, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Qatlib.Foundations.PureStateMath.Ket, apply_ite, map_one, map_zero, mul_ite, ite_mul, mul_one, one_mul,
      mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hij : i = j <;> simp only [hij, eq_comm, if_true, if_false, Complex.star_def] <;> ring
  have hdiag (s : Fin m) (i j : Fin n) : F s 1 i i = F s 1 j j := by
    by_cases hij : i = j
    · subst j; rfl
    let P :=
        outerProduct
        (Qatlib.Foundations.PureStateMath.Ket i + Qatlib.Foundations.PureStateMath.Ket j)
    let Q :=
        outerProduct
        (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)
    have hkP : F s P *ᵥ (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j) = 0 := by
      apply hzero P (outerProduct_posSemidef _)
      rw [outerProduct_mulVec]
      have h := hpq i j 1
      simp [hij, Ne.symm hij, ← sub_eq_add_neg] at h
      rw [h, zero_smul]
    have hkQ : F s Q *ᵥ (Qatlib.Foundations.PureStateMath.Ket i + Qatlib.Foundations.PureStateMath.Ket j) = 0 := by
      apply hzero Q (outerProduct_posSemidef _)
      rw [outerProduct_mulVec]
      have h := hpq i j (-1)
      simp [hij, Ne.symm hij, ← sub_eq_add_neg] at h
      rw [h, zero_smul]
    have hP := balanced_pair (F s P) (hpos s P (outerProduct_posSemidef _)).1
      i j (-1) (by norm_num) (by simpa using! hkP)
    have hQ := balanced_pair (F s Q) (hpos s Q (outerProduct_posSemidef _)).1
      i j 1 (by norm_num) (by simpa using hkQ)
    have hPQ : P + Q = (2 : ℂ) • (E i + E j) := by
      ext a b
      simp [P, Q, E, outerProduct_apply, map_add, map_sub]
      ring
    have hf : F s P + F s Q = (2 : ℂ) • (F s (E i) + F s (E j)) := by
      rw [← hadd, hPQ, hsmul, hadd]
    have hi := congrArg (fun A : Operator n => A i i) hf
    have hj := congrArg (fun A : Operator n => A j j) hf
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hi hj
    have hji : F s (E j) i i = 0 := hcol s j i i hij
    have hij' : F s (E i) j j = 0 := hcol s i j j (Ne.symm hij)
    rw [hji, add_zero] at hi
    rw [hij', zero_add] at hj
    rw [hId s i i, hId s j j, if_pos rfl, if_pos rfl]
    linear_combination (hj - hi + hP + hQ) / 2
  intro s
  refine ⟨F s 1 0 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hdiag s i 0
  · simp [hId, hij]

end Qatlib.Concepts.QuditTeleport.ResourceIff
