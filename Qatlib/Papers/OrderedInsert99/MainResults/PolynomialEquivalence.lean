/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial sequences for ordered insertion

Defines the initial polynomial `P0poly` and the bounded-degree polynomial-sequence conditions
`PolySeqExists` associated with invariant insertion in [FarhiEtAl1999]. The conditions prescribe
the initial and final polynomials and equality of consecutive evaluations at the alternating
roots `z ^ N = (-1) ^ ℓ`.

## Main statements

* `polyseq_zero_queries`: characterizes the zero-query conditions for positive `N`.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators
open Polynomial

/-- The initial polynomial `1 / √N` times the sum of `X ^ i` for `i < N`. -/
noncomputable def P0poly (N : ℕ) : Polynomial ℂ :=
  Polynomial.C (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) *
    ∑ i ∈ Finset.range N, Polynomial.X ^ i

/-- Existence of a degree-at-most-`N − 1` polynomial sequence with the prescribed endpoints and
matching consecutive evaluations at alternating `N`th roots. -/
def PolySeqExists (N k : ℕ) : Prop :=
  ∃ P : ℕ → Polynomial ℂ,
    (∀ ℓ, ℓ ≤ k → (P ℓ).natDegree ≤ N - 1) ∧
    P 0 = P0poly N ∧
    P k = Polynomial.X ^ (N - 1) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ∀ z : ℂ,
      z ^ N = (-1 : ℂ) ^ ℓ → (P ℓ).eval z = (P (ℓ - 1)).eval z)

/-- For positive `N`, a zero-query polynomial sequence exists exactly when `N = 1`
[FarhiEtAl1999]. -/
theorem polyseq_zero_queries (N : ℕ) (hN : 0 < N) :
    PolySeqExists N 0 ↔ N = 1 := by
  constructor
  · rintro ⟨P, hdeg, h0, hk, hmatch⟩
    have heq : P0poly N = Polynomial.X ^ (N - 1) := by
      rw [← h0]; exact hk
    have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff (N - 1)) heq
    have hsumcoeff :
        (∑ i ∈ Finset.range N, (Polynomial.X ^ i : Polynomial ℂ)).coeff (N - 1) = 1 := by
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (N - 1)]
      · simp
      · intro b hb hne
        rw [Polynomial.coeff_X_pow]
        exact if_neg (Ne.symm hne)
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    simp only [P0poly, Polynomial.coeff_C_mul, hsumcoeff, mul_one] at hcoeff
    have hx : (Polynomial.X ^ (N - 1) : Polynomial ℂ).coeff (N - 1) = 1 := by
      rw [Polynomial.coeff_X_pow]; simp
    rw [hx] at hcoeff
    have hN1 : (Real.sqrt (N : ℝ))⁻¹ = 1 := by
      have hcast : (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) = 1 := by
        simpa using hcoeff
      exact_mod_cast hcast
    have hsqrt : Real.sqrt (N : ℝ) = 1 := inv_eq_one.mp hN1
    have hNN : (N : ℝ) = 1 := by
      have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))
      rw [hsqrt] at h
      norm_num at h
      exact h.symm
    exact_mod_cast hNN
  · intro hN1
    subst hN1
    refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩
    · intro ℓ _; simp
    · simp [P0poly]
    · simp
    · intro ℓ h1 h2; omega

end Qatlib.Papers.OrderedInsert99.MainResults
