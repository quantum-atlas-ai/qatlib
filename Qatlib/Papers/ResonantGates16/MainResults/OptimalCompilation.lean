/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ResonantGates16.MainResults.SourceModel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Optimal Quantum Response Compilation Length

This module formalizes Lemma 1: any achievable resonant equiangular polynomial
tuple `(A, B, C, D)` whose polynomial `A` has degree `L` cannot be realized by
fewer than `L` primitive phase rotations (`L ≤ k` for every realizing length `k`),
and is realized at length `L`.

## Main statements

* `lemma1_optimal_compilation`: if `(A, B, C, D)` is achievable at length `L`
  and `A.natDegree = L`, then `L ≤ k` for every `k` with `Achievable k A B C D`,
  and `Achievable L A B C D`.

## References

* [Low, Yoder, and Chuang, 2016][LowYoderChuang2016Resonant], Lemma 1, p. 4.
-/

namespace Qatlib.Papers.ResonantGates16.MainResults.OptimalCompilation

open Polynomial
open Qatlib.Papers.ResonantGates16.MainResults.SourceModel

set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma qspProduct_poly (φs : List ℝ) :
    ∃ P Q : Polynomial ℂ,
      P.natDegree ≤ φs.length ∧
      (Q = 0 ∨ Q.natDegree + 1 ≤ φs.length) ∧
      ∀ θ : ℝ,
        qspProduct φs θ 0 0 = P.eval (Real.cos (θ / 2) : ℂ) ∧
        qspProduct φs θ 0 1 =
          (Real.sin (θ / 2) : ℂ) * Q.eval (Real.cos (θ / 2) : ℂ) := by
  induction φs with
  | nil =>
      refine ⟨1, 0, by simp, Or.inl rfl, ?_⟩
      intro θ
      simp [qspProduct]
  | cons φ φs ih =>
      obtain ⟨P, Q, hP, hQ, heval⟩ := ih
      let eplus : ℂ := -Complex.I * ((Real.cos φ : ℂ) + Complex.I * (Real.sin φ : ℂ))
      let eminus : ℂ := -Complex.I * ((Real.cos φ : ℂ) - Complex.I * (Real.sin φ : ℂ))
      have hXP : (X * P).natDegree ≤ φs.length + 1 := by
        have h := natDegree_mul_le (p := (X : Polynomial ℂ)) (q := P)
        simp only [natDegree_X] at h
        omega
      have hXQ : (X * Q).natDegree ≤ φs.length := by
        rcases hQ with hQ | hQ
        · simp [hQ]
        · have h := natDegree_mul_le (p := (X : Polynomial ℂ)) (q := Q)
          simp only [natDegree_X] at h
          omega
      have hsecond : (C eplus * (1 - X ^ 2) * Q).natDegree ≤ φs.length + 1 := by
        rcases hQ with hQ | hQ
        · simp [hQ]
        · have hbase : (1 - X ^ 2 : Polynomial ℂ).natDegree ≤ 2 := by
            apply (natDegree_sub_le _ _).trans
            norm_num
          have hconst := natDegree_C_mul_le eplus (1 - X ^ 2)
          have hmul := natDegree_mul_le
            (p := C eplus * (1 - X ^ 2)) (q := Q)
          omega
      refine ⟨X * P + C eplus * (1 - X ^ 2) * Q, C eminus * P + X * Q,
        ?_, ?_, ?_⟩
      · simpa only [List.length_cons] using
          (natDegree_add_le _ _).trans (max_le hXP hsecond)
      · right
        have h := (natDegree_add_le _ _).trans
          (max_le ((natDegree_C_mul_le eminus P).trans hP) hXQ)
        simpa only [List.length_cons] using Nat.add_le_add_right h 1
      · intro θ
        obtain ⟨h00, h01⟩ := heval θ
        have hsc : (Real.sin (θ / 2) : ℂ) ^ 2 =
            1 - (Real.cos (θ / 2) : ℂ) ^ 2 := by
          exact_mod_cast (show Real.sin (θ / 2) ^ 2 = 1 - Real.cos (θ / 2) ^ 2 by
            nlinarith [Real.sin_sq_add_cos_sq (θ / 2)])
        simp only [qspProduct, Matrix.mul_apply, Fin.sum_univ_two, h00, h01,
          primitiveGate, eval_add, eval_mul, eval_X, eval_C, eval_sub, eval_one, eval_pow]
        constructor
        · dsimp [eplus]
          linear_combination
            (-Complex.I * ((Real.cos φ : ℂ) + Complex.I * (Real.sin φ : ℂ)) *
              Q.eval (Real.cos (θ / 2) : ℂ)) * hsc
        · dsimp [eminus]
          ring

private lemma polynomial_real_part (P : Polynomial ℂ) :
    ∃ Pre : Polynomial ℝ, Pre.natDegree ≤ P.natDegree ∧
      ∀ x : ℝ, Pre.eval x = (P.eval (x : ℂ)).re := by
  classical
  refine ⟨∑ n ∈ P.support, monomial n (P.coeff n).re, ?_, ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro n hn
    exact (natDegree_monomial_le _).trans (le_natDegree_of_mem_supp n hn)
  · intro x
    rw [eval_finsetSum, eval_eq_sum, sum_def, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp [eval_monomial, ← Complex.ofReal_pow, Complex.mul_re]

/-- **Lemma 1 (Optimal quantum response compilation)**: an achievable tuple
`(A, B, C, D)` with `A.natDegree = L` requires at least `L` primitive rotations
and is realized by `L` rotations. -/
theorem lemma1_optimal_compilation (L : ℕ) (A B C D : Polynomial ℝ)
    (hchar : Achievable L A B C D) (hdeg : A.natDegree = L) :
    (∀ k : ℕ, Achievable k A B C D → L ≤ k) ∧ Achievable L A B C D := by
  refine ⟨?_, hchar⟩
  intro k hk
  obtain ⟨φs, hφs⟩ := hk
  obtain ⟨P, Q, hP, _, heval⟩ := qspProduct_poly (List.ofFn φs)
  obtain ⟨Pre, hPre, hreal⟩ := polynomial_real_part P
  have hresponse (θ : ℝ) :
      (responseMatrix k φs θ 0 0).re = Pre.eval (Real.cos (θ / 2)) := by
    rw [responseMatrix, (heval θ).1, hreal]
  have htuple (θ : ℝ) :
      (tupleMatrix k A B C D θ 0 0).re = A.eval (Real.cos (θ / 2)) := by
    unfold tupleMatrix
    split <;> simp [sigmaX, sigmaY, sigmaZ, Matrix.add_apply, Matrix.smul_apply,
      Complex.mul_re]
  have heq : A = Pre := by
    apply eq_of_infinite_eval_eq
    apply (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono
    intro x hx
    have hcos : Real.cos (2 * Real.arccos x / 2) = x := by
      rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.cos_arccos hx.1 hx.2
    have h := hresponse (2 * Real.arccos x)
    rw [hφs, htuple, hcos] at h
    exact h
  rw [← hdeg, heq]
  exact hPre.trans (by simpa using hP)

end Qatlib.Papers.ResonantGates16.MainResults.OptimalCompilation
