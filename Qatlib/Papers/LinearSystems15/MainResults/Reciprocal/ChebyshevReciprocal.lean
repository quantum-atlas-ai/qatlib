/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalReciprocal
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# LinearSystems15 — Chebyshev reciprocal approximation

Paper-layer statements for Childs–Kothari–Somma,
"Quantum algorithm for systems of linear equations with exponentially improved
dependence on precision" (arXiv:1511.02306).

The source §4.2 (pp. 18–21) approximates `1/x` on the signed gap domain
`D_κ = [-1,-1/κ] ∪ [1/κ,1]` by the truncation of the binomial-Chebyshev
expansion of `f(x) = (1-(1-x²)^b)/x`.

What is proved here:

* `lemma14_chebyshev_reciprocal` — source **Lemma 14** (2ε closeness of the
  truncated series), reused from the frozen `QSingValue19` near-optimal
  reciprocal development (same literal polynomial, ceiling cutoffs).
* `lemma17_geometric_reciprocal` — source **Lemma 17**, proved here for an
  arbitrary integer cutoff `b ≥ (κd)² log(κd/ε)` (the frozen library only
  provides the ceiling instance `b = ⌈κ² log(κ/ε)⌉`).
* `lemma18_full_expansion` — source **Lemma 18** (exact Chebyshev expansion),
  reused from the frozen full-expansion identity plus the geometric closed form.
* `lemma19_truncation_error` — source **Lemma 19** (truncation error at
  `j₀ = √(b log(4b/ε))`), reused from the frozen truncation theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.LinearSystems15.MainResults.Reciprocal

open Polynomial
open scoped BigOperators

open Qatlib.Concepts.QsvtCore.LinearSystems

/-! ## Lemma 14 — the truncated series is `2ε`-close to `1/x` -/

/-- **Source Lemma 14** (arXiv:1511.02306, §4.2, pp. 20–21; the `2ε` Chebyshev
error of the printed cutoffs).  With `b = ⌈κ² log(κ/ε)⌉` and
`j₀ = ⌈√(b log(4b/ε))⌉` (the integer encodings of the paper's real cutoffs),
the truncated series `g(x) = 4 Σ_{j≤j₀} (-1)^j [Σ_{i=j+1}^{b} C(2b,b+i)/2^{2b}] T_{2j+1}(x)`
is `2ε`-close to `1/x` on the signed gap domain `D_κ = {x | 1/κ ≤ |x| ≤ 1}`.

Reuses the frozen `QSingValue19` theorem `nearOptimalReciprocal_error_of_abs`
(full FQN `QuantumAlgorithm.Papers.QSingValue19.LinearSystems.nearOptimalReciprocal_error_of_abs`),
whose `nearOptimalReciprocalPolynomial κ ε` is definitionally the paper's `g`. -/
theorem lemma14_chebyshev_reciprocal (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (x : ℝ) (hx : |x| ∈ Set.Icc κ⁻¹ 1) :
    |(nearOptimalReciprocalPolynomial κ ε).eval x - x⁻¹| ≤ 2 * ε :=
  nearOptimalReciprocal_error_of_abs κ ε hκ hε hε1 x hx

/-! ## Lemma 17 — the geometric reciprocal with an arbitrary cutoff -/

/-- **Source Lemma 17** (arXiv:1511.02306, §4.2, p. 18, eqs. (74)–(76)).
For `κd > 1`, `ε > 0` and any integer `b ≥ (κd)² log(κd/ε)`, the function
`f(x) = (1-(1-x²)^b)/x` is `ε`-close to `1/x` on the signed gap domain
`D_{κd} = {x | 1/(κd) ≤ |x| ≤ 1}`.

Proof follows the source: on `D_{κd}` the numerator differs from `1` most at
`|x| = 1/(κd)` (eq. (75)), so `(1-x²)^b ≤ (1-(κd)⁻²)^b ≤ e^{-b/(κd)²} ≤ ε/(κd)`,
and dividing by `|x| ≥ 1/(κd)` gives eq. (76). -/
theorem lemma17_geometric_reciprocal (κd ε : ℝ) (hκd : 1 < κd) (hε : 0 < ε)
    (b : ℕ) (hb : κd ^ 2 * Real.log (κd / ε) ≤ (b : ℝ))
    (x : ℝ) (hx : |x| ∈ Set.Icc κd⁻¹ 1) :
    |(1 - (1 - x ^ 2) ^ b) / x - x⁻¹| ≤ ε := by
  have hκd0 : 0 < κd := by linarith
  have hinvpos : 0 < κd⁻¹ := inv_pos.mpr hκd0
  have habs : κd⁻¹ ≤ |x| := hx.1
  have hxle : |x| ≤ 1 := hx.2
  have hx0 : x ≠ 0 := by
    intro h
    have hz : |x| = 0 := by simp [h]
    linarith
  -- The squared bound `x² ≤ 1`, hence `0 ≤ 1 - x²`.
  have hsqle : x ^ 2 ≤ 1 := by
    have h1 : |x| ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxle 2
    simpa [sq_abs] using h1
  have hsq0 : 0 ≤ 1 - x ^ 2 := by linarith
  -- Pointwise dominance of the numerator by its value at the gap edge.
  have hstep : 1 - x ^ 2 ≤ 1 - κd⁻¹ ^ 2 := by
    have ht : κd⁻¹ ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ hinvpos.le habs 2
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [ht, hx2]
  have hpow : (1 - x ^ 2) ^ b ≤ (1 - κd⁻¹ ^ 2) ^ b :=
    pow_le_pow_left₀ hsq0 hstep b
  -- `(1-t)^b ≤ exp(-b t)` for `t = (κd)⁻²`.
  have hbase : (1 - κd⁻¹ ^ 2) ^ b ≤ Real.exp (-(b : ℝ) / κd ^ 2) := by
    have hb1 : 1 - κd⁻¹ ^ 2 ≤ Real.exp (-(κd⁻¹ ^ 2)) := by
      have h := Real.add_one_le_exp (-(κd⁻¹ ^ 2))
      linarith
    have hnonneg : (0 : ℝ) ≤ 1 - κd⁻¹ ^ 2 := by
      nlinarith [sq_nonneg κd⁻¹, inv_pos.mpr hκd0]
    calc
      (1 - κd⁻¹ ^ 2) ^ b ≤ (Real.exp (-(κd⁻¹ ^ 2))) ^ b :=
        pow_le_pow_left₀ hnonneg hb1 b
      _ = Real.exp ((b : ℝ) * (-(κd⁻¹ ^ 2))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(b : ℝ) / κd ^ 2) := by
        congr 1
        field_simp
  -- The exponential is at most `ε/κd` by the cutoff hypothesis.
  have hdiv : Real.log (κd / ε) ≤ (b : ℝ) / κd ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc Real.log (κd / ε) * κd ^ 2 = κd ^ 2 * Real.log (κd / ε) := by ring
      _ ≤ (b : ℝ) := hb
  have hexp : Real.exp (-(b : ℝ) / κd ^ 2) ≤ ε / κd := by
    have hle : -(b : ℝ) / κd ^ 2 ≤ -Real.log (κd / ε) := by
      simpa [neg_div] using neg_le_neg hdiv
    calc
      Real.exp (-(b : ℝ) / κd ^ 2) ≤ Real.exp (-Real.log (κd / ε)) :=
        Real.exp_le_exp.mpr hle
      _ = ε / κd := by
        rw [Real.exp_neg, Real.exp_log (div_pos hκd0 hε)]
        field_simp
  have hnum : (1 - x ^ 2) ^ b ≤ ε / κd := hpow.trans (hbase.trans hexp)
  -- Rewrite the residual and divide.
  have hrewrite : (1 - (1 - x ^ 2) ^ b) / x - x⁻¹ = -((1 - x ^ 2) ^ b / x) := by
    field_simp
    ring
  have habsval : |(1 - (1 - x ^ 2) ^ b) / x - x⁻¹| = (1 - x ^ 2) ^ b / |x| := by
    rw [hrewrite, abs_neg, abs_div, abs_of_nonneg (pow_nonneg hsq0 b)]
  rw [habsval]
  calc
    (1 - x ^ 2) ^ b / |x| ≤ (ε / κd) / κd⁻¹ :=
      div_le_div₀ (le_of_lt (div_pos hε hκd0)) hnum hinvpos habs
    _ = ε := by
      field_simp

/-! ## Lemma 18 — exact binomial–Chebyshev expansion -/

/-- **Source Lemma 18** (arXiv:1511.02306, §4.2, p. 18, eq. (77)).  For every
`b`, on `[-1,1]` and away from the origin,
`f(x) = (1-(1-x²)^b)/x = 4 Σ_{j=0}^{b-1} (-1)^j [Σ_{i=j+1}^{b} C(2b,b+i)/2^{2b}] T_{2j+1}(x)`.

Reuses the frozen polynomial identity `nearOptimalReciprocal_full_expansion`
(full FQN `QuantumAlgorithm.Papers.QSingValue19.LinearSystems.nearOptimalReciprocal_full_expansion`)
together with the geometric closed form `reciprocalPolynomial_eval_div`. -/
theorem lemma18_full_expansion (b : ℕ) (x : ℝ) (hx0 : x ≠ 0) :
    (1 - (1 - x ^ 2) ^ b) / x =
      ∑ j ∈ Finset.range b,
        4 * (-1 : ℝ) ^ j *
            (∑ i ∈ Finset.Ico (j + 1) (b + 1), ((2 * b).choose (b + i) : ℝ)) /
              (2 : ℝ) ^ (2 * b) *
          (Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x := by
  rw [← reciprocalPolynomial_eval_div b hx0, ← nearOptimalReciprocal_full_expansion]
  simp only [eval_finsetSum, eval_mul, eval_C]

/-! ## Lemma 19 — truncation error -/

/-- **Source Lemma 19** (arXiv:1511.02306, §4.2, pp. 20–21, eqs. (88)–(91)).
Truncating (77) at `j₀ = ⌈√(b log(4b/ε))⌉`, `b = ⌈κ² log(κ/ε)⌉`, gives a
polynomial `g` that is `ε`-close to `f` on `[-1,1]`.

Reuses the frozen `nearOptimalReciprocal_truncation_error` (full FQN
`QuantumAlgorithm.Papers.QSingValue19.LinearSystems.nearOptimalReciprocal_truncation_error`)
and the geometric closed form of `reciprocalPolynomial`. -/
theorem lemma19_truncation_error (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(nearOptimalReciprocalPolynomial κ ε).eval x -
        (1 - (1 - x ^ 2) ^ (nearOptimalReciprocalB κ ε)) / x| ≤ ε := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · -- At the origin both sides vanish: the summands are odd Chebyshev values.
    subst hx0
    have heval : (nearOptimalReciprocalPolynomial κ ε).eval (0 : ℝ) = 0 := by
      simp only [nearOptimalReciprocalPolynomial, eval_finsetSum, eval_mul, eval_C]
      apply Finset.sum_eq_zero
      intro j _
      have hodd : (Chebyshev.T ℝ (((2 * j + 1 : ℕ) : ℤ))).eval (0 : ℝ) = 0 := by
        apply Chebyshev.T_eval_zero_of_odd
        exact ⟨(j : ℤ), by push_cast; ring⟩
      rw [hodd]
      ring
    rw [heval]
    have hz : (1 - (1 - (0 : ℝ) ^ 2) ^ (nearOptimalReciprocalB κ ε)) / 0 = 0 := by simp
    rw [hz]
    simp
    linarith
  · have h := nearOptimalReciprocal_truncation_error κ ε hκ hε hε1 x hx
    rw [reciprocalPolynomial_eval_div (nearOptimalReciprocalB κ ε) hx0] at h
    exact h

end Qatlib.Papers.LinearSystems15.MainResults.Reciprocal
