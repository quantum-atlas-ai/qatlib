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
# Higher-Order Differentiation Rule for Exponential Adjoint Conjugation

This module proves Corollary 1: in a complex Banach algebra, the `p`-th derivative
of `s ↦ Ad_{e^{sX}}(Y(s))` expands as the binomial sum
`∑_{j=0}^p C(p, j) Ad_{e^{tX}}(ad_X^j(Y^{(p - j)}(t)))`.

## Main statements

* `corollary1_higher_order_rule`: binomial higher-derivative formula for `Ad_{e^{tX}}(Y(t))`.

## References

* [Childs and Su, 2019][ChildsSu2019], Corollary 1, Eq. (41), p. 6.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatticeProd19.MainResults.AdjointCalculus

open Qatlib.Papers.LatticeProd19.MainResults.SourceModel

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

private def adPowCLM (X : 𝔸) : ℕ → 𝔸 →L[ℝ] 𝔸
  | 0 => ContinuousLinearMap.id ℝ 𝔸
  | j + 1 =>
      (ContinuousLinearMap.mul ℝ 𝔸 X - (ContinuousLinearMap.mul ℝ 𝔸).flip X).comp
        (adPowCLM X j)

private theorem adPowCLM_apply (X : 𝔸) (j : ℕ) (Z : 𝔸) :
    adPowCLM X j Z = adPow X j Z := by
  induction j with
  | zero => rfl
  | succ j ih => simp [adPowCLM, adPow_succ, ad, ih]

private theorem higher_order_rule_all
    (X : 𝔸) (Y : ℝ → 𝔸) (hY : ContDiff ℝ ⊤ Y) (p : ℕ) :
    iteratedDeriv p (fun s : ℝ => AdExp X s (Y s))
      = fun t => ∑ j ∈ Finset.range (p + 1),
          (Nat.choose p j : ℝ) •
            AdExp X t (adPow X j (iteratedDeriv (p - j) Y t)) := by
  induction p with
  | zero => funext t; simp
  | succ p ih =>
      funext t
      have hD (j : ℕ) :
          HasDerivAt
            (fun s => (Nat.choose p j : ℝ) •
              AdExp X s (adPow X j (iteratedDeriv (p - j) Y s)))
            ((Nat.choose p j : ℝ) •
              (AdExp X t (adPow X (j + 1) (iteratedDeriv (p - j) Y t)) +
                AdExp X t (adPow X j (iteratedDeriv (p - j + 1) Y t)))) t := by
        have hYm : HasDerivAt (iteratedDeriv (p - j) Y)
            (iteratedDeriv (p - j + 1) Y t) t := by
          rw [iteratedDeriv_succ]
          exact (hY.differentiable_iteratedDeriv (p - j) (by simp)).differentiableAt.hasDerivAt
        have hAd : HasDerivAt (fun s => adPow X j (iteratedDeriv (p - j) Y s))
            (adPow X j (iteratedDeriv (p - j + 1) Y t)) t := by
          simpa only [Function.comp_def, adPowCLM_apply] using
            (adPowCLM X j).hasFDerivAt.comp_hasDerivAt t hYm
        simpa only [← adPow_succ] using
          (AdExp_hasDerivAt X _ _ t hAd).fun_const_smul (Nat.choose p j : ℝ)
      rw [iteratedDeriv_succ, ih,
        (HasDerivAt.fun_sum (u := Finset.range (p + 1)) (fun j _ => hD j)).deriv]
      simp only [smul_add, Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul]
      rw [Finset.sum_choose_succ_nsmul
        (fun j m => AdExp X t (adPow X j (iteratedDeriv m Y t))) p, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjp : j ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [show p - j + 1 = p + 1 - j by omega]

/-- **Corollary 1**: for smooth `Y : ℝ → 𝔸`, the `p`-th iterated derivative of
`s ↦ AdExp X s (Y s)` is `∑_{j=0}^p C(p, j) AdExp X t (adPow X j (iteratedDeriv (p - j) Y t))`. -/
theorem corollary1_higher_order_rule
    (X : 𝔸) (Y : ℝ → 𝔸) (hY : ContDiff ℝ ⊤ Y) (p : ℕ) (_hp : 1 ≤ p) (t : ℝ) :
    iteratedDeriv p (fun s : ℝ => AdExp X s (Y s)) t
      = ∑ j ∈ Finset.range (p + 1),
          (Nat.choose p j : ℝ) •
            AdExp X t (adPow X j (iteratedDeriv (p - j) Y t)) := by
  exact congrFun (higher_order_rule_all X Y hY p) t

end Qatlib.Papers.LatticeProd19.MainResults.AdjointCalculus
