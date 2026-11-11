/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Annealing norm recurrences

This module develops the finite weighted-square and recurrence estimates used in Appendix A of
[SommaBoixoBarnum2007]. The annealing-rate and remainder hypotheses turn the stated
norm-increment inequality into a contractive recurrence, yielding the uniform bounds `b k ≤ 2`
and `sqrt (b k) ≤ sqrt 2`.

## Main statements

* `one_le_sum_sq_div`: a weighted-square lower bound for normalized weights.
* `eqA18_norm_sq_bound`: an explicit solution bound for the scalar recurrence.
* `a7_implies_norm_le_sqrt_two`: the uniform square-root norm bound.

## References

* [Somma et al., 2007][SommaBoixoBarnum2007]
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.QAnnealing07.MainResults.NormConvergence

/-- For two normalized finite weight functions with strictly positive `π`, the weighted square
sum `∑ i, μ i ^ 2 / π i` is at least one [SommaBoixoBarnum2007]. -/
theorem one_le_sum_sq_div
    {ι : Type*} [Fintype ι] (μ π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (_hμ : ∀ i, 0 ≤ μ i)
    (hsumμ : ∑ i, μ i = 1) (hsumπ : ∑ i, π i = 1) :
    1 ≤ ∑ i, μ i ^ 2 / π i := by
  have h := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset ι) μ
    (fun i _ => hπ i)
  simpa [hsumμ, hsumπ] using h

/-- In a real inner-product space, the squared-norm increment from adding `d` to `h` is `2 *
inner ℝ h d + ‖d‖ ^ 2` [SommaBoixoBarnum2007]. -/
theorem norm_sq_increment_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (h d : E) :
    ‖h + d‖ ^ 2 - ‖h‖ ^ 2 = 2 * inner ℝ h d + ‖d‖ ^ 2 := by
  rw [norm_add_sq_real]
  ring

/-- The stated annealing-rate, remainder, and lower-norm assumptions strengthen the increment
bound to `n2next - n2 ≤ -δ * n2 + 2δ` [SommaBoixoBarnum2007]. -/
theorem a15_implies_a16
    (δ Δβ EM τ C n2 n2next : ℝ)
    (hδ : 0 < δ) (hτ1 : τ ≤ 1 / 2)
    (hδsmall : C * δ ≤ 1 / 2)
    (hA7 : Δβ * EM ≤ τ * δ) (hn2 : 1 ≤ n2)
    (hA15 : n2next - n2 ≤ (-2 * δ + Δβ * EM) * n2 + 2 * δ + C * δ ^ 2) :
    n2next - n2 ≤ -δ * n2 + 2 * δ := by
  have hτδ : Δβ * EM ≤ δ / 2 := by
    have h' : τ * δ ≤ (1 / 2) * δ := mul_le_mul_of_nonneg_right hτ1 hδ.le
    linarith
  have hcoef : Δβ * EM - δ ≤ 0 := by linarith
  have hmul : (Δβ * EM - δ) * n2 ≤ (Δβ * EM - δ) * 1 :=
    mul_le_mul_of_nonpos_left hn2 hcoef
  have hCδ2 : C * δ ^ 2 ≤ δ / 2 := by
    have h' : C * δ * δ ≤ (1 / 2) * δ := mul_le_mul_of_nonneg_right hδsmall hδ.le
    calc C * δ ^ 2 = C * δ * δ := by ring
      _ ≤ (1 / 2) * δ := h'
      _ = δ / 2 := by ring
  have hkey : (Δβ * EM - δ) * n2 + C * δ ^ 2 ≤ 0 := by
    have h1 : (Δβ * EM - δ) * n2 ≤ Δβ * EM - δ := by simpa using hmul
    linarith
  linarith [hA15, hkey]

/-- A sequence starting at one and satisfying the stated affine recurrence with `δ ≤ 1` obeys `b
k ≤ 2 - (1 - δ) ^ k` [SommaBoixoBarnum2007]. -/
theorem eqA18_norm_sq_bound
    (δ : ℝ) (b : ℕ → ℝ) (hδ1 : δ ≤ 1)
    (hb0 : b 0 = 1) (hrec : ∀ k, b (k + 1) ≤ (1 - δ) * b k + 2 * δ) :
    ∀ k, b k ≤ 2 - (1 - δ) ^ k := by
  intro k
  induction k with
  | zero => rw [hb0]; norm_num
  | succ k ih =>
      have h1δ : 0 ≤ 1 - δ := by linarith
      have hstep := hrec k
      have hpow : (1 - δ) ^ (k + 1) = (1 - δ) ^ k * (1 - δ) := pow_succ _ k
      have hmul : (1 - δ) * b k ≤ (1 - δ) * (2 - (1 - δ) ^ k) :=
        mul_le_mul_of_nonneg_left ih h1δ
      rw [hpow]
      nlinarith [hmul]

/-- Under the annealing-rate and increment hypotheses with `0 < δ ≤ 1`, every `b k` is at most
two and its square root is at most `sqrt 2` [SommaBoixoBarnum2007]. -/
theorem a7_implies_norm_le_sqrt_two
    (δ Δβ EM τ C : ℝ) (b : ℕ → ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ1 : τ ≤ 1 / 2)
    (hδsmall : C * δ ≤ 1 / 2)
    (hA7 : Δβ * EM ≤ τ * δ)
    (hb0 : b 0 = 1) (hb1 : ∀ k, 1 ≤ b k)
    (hA15 : ∀ k, b (k + 1) - b k ≤ (-2 * δ + Δβ * EM) * b k + 2 * δ + C * δ ^ 2) :
    (∀ k, b k ≤ 2) ∧ (∀ k, Real.sqrt (b k) ≤ Real.sqrt 2) := by
  have hrec : ∀ k, b (k + 1) ≤ (1 - δ) * b k + 2 * δ := by
    intro k
    have h16 := a15_implies_a16 δ Δβ EM τ C (b k) (b (k + 1))
      hδ hτ1 hδsmall hA7 (hb1 k) (hA15 k)
    linarith
  have hb := eqA18_norm_sq_bound δ b hδ1 hb0 hrec
  have h1δ : 0 ≤ 1 - δ := by linarith
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have hpow : 0 ≤ (1 - δ) ^ k := pow_nonneg h1δ k
    linarith [hb k, hpow]
  · exact Real.sqrt_le_sqrt (by
      have hpow : 0 ≤ (1 - δ) ^ k := pow_nonneg h1δ k
      linarith [hb k, hpow])

end Qatlib.Papers.QAnnealing07.MainResults.NormConvergence
