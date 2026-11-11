/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Rank-one support of a finite positive sum

If a finite sum of operators `|u_j⟩⟨u_j|` equals a scalar multiple of
`|v⟩⟨v|`, every summand vector lies in the span of `v`. The proof tests the
identity on the orthogonal complement of that span and uses nonnegativity of
squared inner products. No normalization of the vectors is required.

This is useful for pure outputs of operator-sum maps [Kraus1971]. Orthogonal
complements and rank-one operators are standard functional analysis; see
[Reed & Simon, *Functional Analysis*][ReedSimon1980I] and [Bhatia2007].
-/

set_option autoImplicit false

namespace Qatlib.Foundations.ChannelTheory.PureOutput

open scoped BigOperators

/-- Every vector in a finite rank-one positive decomposition of a rank-one
operator belongs to its supporting line. This is the support argument used for
pure outputs in [Kraus, state changes][Kraus1971]. -/
theorem mem_span_of_sum_rankOne_eq_smul_rankOne
    {E J : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype J]
    (u : J → E) (v : E) (r : ℂ)
    (h : (∑ j, InnerProductSpace.rankOne ℂ (u j) (u j)) =
      r • InnerProductSpace.rankOne ℂ v v) :
    ∀ j, u j ∈ Submodule.span ℂ {v} := by
  classical
  let S : Submodule ℂ E := Submodule.span ℂ {v}
  letI : FiniteDimensional ℂ S := by
    dsimp [S]
    infer_instance
  letI : CompleteSpace S := FiniteDimensional.complete ℂ S
  intro j
  have hdouble : u j ∈ Sᗮᗮ := by
    apply (Submodule.mem_orthogonal' Sᗮ (u j)).2
    intro y hy
    have hvy : inner ℂ v y = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp hy
    have htarget : InnerProductSpace.rankOne ℂ v v y = 0 := by
      rw [InnerProductSpace.rankOne_apply, hvy, zero_smul]
    have hsum : (∑ k, inner ℂ y
        (InnerProductSpace.rankOne ℂ (u k) (u k) y)) = 0 := by
      calc
        _ = inner ℂ y ((∑ k, InnerProductSpace.rankOne ℂ (u k) (u k)) y) := by
          rw [ContinuousLinearMap.sum_apply, inner_sum]
        _ = inner ℂ y ((r • InnerProductSpace.rankOne ℂ v v) y) :=
          congrArg (fun A : E →L[ℂ] E => inner ℂ y (A y)) h
        _ = 0 := by
          rw [ContinuousLinearMap.smul_apply, htarget, smul_zero, inner_zero_right]
    have hquadratic (k : J) :
        (inner ℂ y (InnerProductSpace.rankOne ℂ (u k) (u k) y)).re =
          ‖inner ℂ (u k) y‖ ^ 2 := by
      rw [InnerProductSpace.inner_right_rankOne_apply,
        ← inner_conj_symm y (u k), Complex.conj_mul']
      simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    have hnorms : (∑ k, ‖inner ℂ (u k) y‖ ^ 2) = 0 := by
      have hre := congrArg Complex.re hsum
      rw [Complex.re_sum] at hre
      simpa only [hquadratic, Complex.zero_re] using hre
    have hj : ‖inner ℂ (u j) y‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg ‖inner ℂ (u k) y‖)).mp hnorms j (Finset.mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
  simpa only [Submodule.orthogonal_orthogonal] using hdouble

end Qatlib.Foundations.ChannelTheory.PureOutput
