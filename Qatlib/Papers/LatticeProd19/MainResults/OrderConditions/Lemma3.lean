/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Choose.Sum
import Qatlib.Papers.LatticeProd19.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Recursive Binomial Formula for Time-Ordered Derivative Operators

This module defines the recursive operator sequence `T_0 = 1`,
`T_{j+1}(t) = -i T_j(t) H(t) + T_j'(t)` and proves Lemma 3:
`T_{j+1}(t) = -i ∑_{k=0}^j C(j, k) H^{(k)}(t) T_{j - k}(t)`.

## Main statements

* `Trec`: recursive operator sequence associated with a time-dependent generator `H`.
* `lemma3_recursive_formula`: binomial recurrence `T_{j+1}(t) = -i ∑_{k=0}^j C(j, k) H^{(k)}(t) T_{j-k}(t)`.

## References

* [Childs and Su, 2019][ChildsSu2019], Lemma 3, Eqs. (62)--(63), p. 10.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatticeProd19.MainResults.OrderConditions

open Qatlib.Papers.LatticeProd19.MainResults.SourceModel

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- Recursive operator family `T_0(t) = 1`, `T_{j+1}(t) = -i (T_j(t) H(t)) + T_j'(t)`. -/
def Trec (H : ℝ → 𝔸) : ℕ → ℝ → 𝔸
  | 0 => fun _ => 1
  | j + 1 => fun t => (-Complex.I) • (Trec H j t * H t) + deriv (Trec H j) t

private theorem contDiff_Trec (H : ℝ → 𝔸) (hH : ContDiff ℝ ⊤ H) :
    ∀ m : ℕ, ContDiff ℝ ⊤ (Trec H m)
  | 0 => contDiff_const
  | m + 1 => by
    have ih := contDiff_Trec H hH m
    exact ((ih.mul hH).const_smul (-Complex.I)).add ih.analyticOnNhd.deriv.contDiff

/-- **Lemma 3**: for smooth `H : ℝ → 𝔸` and every `j : ℕ`,
`Trec H (j + 1) t = -i • ∑_{k=0}^j C(j, k) • (H^{(k)}(t) * Trec H (j - k) t)`. -/
theorem lemma3_recursive_formula (H : ℝ → 𝔸) (hH : ContDiff ℝ ⊤ H) (j : ℕ) :
    ∀ t : ℝ, Trec H (j + 1) t
      = (-Complex.I) • (∑ k ∈ Finset.range (j + 1),
          (Nat.choose j k : ℝ) • (iteratedDeriv k H t * Trec H (j - k) t)) := by
  induction j with
  | zero =>
    intro t
    simp [Trec]
  | succ j ih =>
    intro t
    -- Differentiate the induction hypothesis term by term.
    have hd : HasDerivAt (Trec H (j + 1))
        ((-Complex.I) • (∑ k ∈ Finset.range (j + 1),
          (Nat.choose j k : ℝ) •
            (iteratedDeriv (k + 1) H t * Trec H (j - k) t +
              iteratedDeriv k H t * deriv (Trec H (j - k)) t))) t := by
      rw [funext ih]
      apply HasDerivAt.fun_const_smul
      apply HasDerivAt.fun_sum
      intro k _hk
      apply HasDerivAt.fun_const_smul
      apply HasDerivAt.mul
      · simpa only [iteratedDeriv_succ] using
          ((hH.differentiable_iteratedDeriv k (by simp)).differentiableAt.hasDerivAt)
      · exact ((contDiff_Trec H hH (j - k)).differentiable (by simp)).differentiableAt.hasDerivAt
    -- Pascal's identity joins the two sums from the product rule.
    have hsum := Finset.sum_choose_succ_nsmul
      (fun k m => iteratedDeriv k H t * Trec H m t) j
    simp only [← Nat.cast_smul_eq_nsmul ℝ] at hsum
    change (-Complex.I) • (Trec H (j + 1) t * H t) + deriv (Trec H (j + 1)) t = _
    rw [hd.deriv, ih t, smul_mul_assoc, ← smul_add, hsum]
    congr 1
    rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hsub : j + 1 - k = j - k + 1 := by
      have := Finset.mem_range.mp hk
      omega
    rw [hsub, Trec]
    simp only [mul_add, mul_smul_comm, ← mul_assoc, smul_add, smul_mul_assoc]
    rw [smul_comm (-Complex.I) (Nat.choose j k : ℝ)]
    abel

end Qatlib.Papers.LatticeProd19.MainResults.OrderConditions
