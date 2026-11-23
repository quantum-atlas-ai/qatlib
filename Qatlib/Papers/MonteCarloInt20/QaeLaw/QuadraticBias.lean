/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic

/-!
# A finite quadratic payoff bridge for nested amplitude estimation

For a finite, non-empty sample family, a quadratic payoff has an exact
nonlinear bias.  The bias is the quadratic coefficient multiplied by the
finite-population variance.  This is the finite identity needed before any
Taylor-style error budget can be claimed for a nonlinear payoff.

The query-count theorem below uses the two exact source-access words from the
paper.  Factoring out the positive outer repetition count makes the threshold
`M ≤ D` kernel-visible while retaining the full `(2N - 1)` and `(2M - 1)`
factors.
-/

set_option autoImplicit false

@[expose] public section

namespace Qatlib.Papers.MonteCarloInt20.QaeLaw

open scoped BigOperators

noncomputable section

section QuadraticPayoff

variable {n : ℕ}

/-- The uniform finite mean of a real sample family on a non-empty domain. -/
def finiteMean (h_n : 0 < n) (x : Fin n → ℝ) : ℝ :=
  if hzero : n = 0 then False.elim (by omega) else (n : ℝ)⁻¹ * ∑ i, x i

/-- A quadratic payoff applied pointwise to a finite sample family. -/
def quadraticPayoff (a b : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i + b * (x i) ^ 2

/-- The payoff bias relative to applying the payoff to the finite mean. -/
def quadraticPayoffBias (h_n : 0 < n) (a b : ℝ) (x : Fin n → ℝ) : ℝ :=
  finiteMean h_n (quadraticPayoff a b x) -
    (a * finiteMean h_n x + b * (finiteMean h_n x) ^ 2)

/--
The exact finite-population bias of a quadratic payoff.

The statement is uniform in the coefficients and sample values.  No smoothness
or asymptotic approximation is hidden in the equality.  In particular, it
isolates the variance term that must be budgeted by a nested-QAE analysis.
-/
theorem quadratic_payoff_bias_eq_variance (h_n : 0 < n) (a b : ℝ) (x : Fin n → ℝ) :
    quadraticPayoffBias h_n a b x =
      b * (finiteMean h_n (fun i => (x i) ^ 2) - (finiteMean h_n x) ^ 2) := by
  have hmean :
      finiteMean h_n (quadraticPayoff a b x) =
        a * finiteMean h_n x + b * finiteMean h_n (fun i => (x i) ^ 2) := by
    simp [finiteMean, Nat.ne_of_gt h_n, quadraticPayoff,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring_nf
  rw [quadraticPayoffBias, hmean]
  ring_nf

/-- The affine special case has zero nonlinear payoff bias. -/
theorem affine_payoff_bias_zero (h_n : 0 < n) (a : ℝ) (x : Fin n → ℝ) :
    finiteMean h_n (fun i => a * x i) = a * finiteMean h_n x := by
  simp [finiteMean, Nat.ne_of_gt h_n, Finset.mul_sum]
  ring_nf

end QuadraticPayoff

section QueryCounts

/-- The previous sequential source-access count in factored form. -/
def previousSourceQueries (D N : ℕ) : ℕ :=
  (2 * N - 1) * (4 * D)

/-- The nested source-access count in factored form. -/
def nestedSourceQueries (M N : ℕ) : ℕ :=
  (2 * N - 1) * (2 * (2 * M - 1))

/--
For positive inner and outer repetition sizes, the exact nested word beats the
sequential word precisely at `M ≤ D`.

The theorem retains the complete source-access factors from the paper.  The
outer factor is cancelled only after its strict positivity has been proved,
so the result is not an asymptotic or vacuous big-O assertion.
-/
theorem nested_source_queries_lt_iff (D M N : ℕ)
    (hD : 0 < D) (hM : 0 < M) (hN : 0 < N) :
    nestedSourceQueries M N < previousSourceQueries D N ↔ M ≤ D := by
  have houter : 0 < 2 * N - 1 := by omega
  have hfactor :
      nestedSourceQueries M N = (2 * N - 1) * (2 * (2 * M - 1)) := by
    rfl
  have hprev :
      previousSourceQueries D N = (2 * N - 1) * (4 * D) := by
    rfl
  rw [hfactor, hprev, Nat.mul_lt_mul_left houter]
  constructor
  · intro h
    omega
  · intro h
    have hD4 : 0 < 4 * D := by omega
    omega

end QueryCounts

end

end Qatlib.Papers.MonteCarloInt20.QaeLaw

end
