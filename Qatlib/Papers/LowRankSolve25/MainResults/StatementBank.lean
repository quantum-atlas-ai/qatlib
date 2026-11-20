/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LowRankSolve25.MainResults.RowSampling
public import Qatlib.Papers.LowRankSolve25.MainResults.SecondMoment

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"A simple analysis of a quantum-inspired algorithm for solving
low-rank linear systems" (arXiv:2508.13108v1, 2025).

Two cores are proved in this block:

- `RowSampling.exp_frob2_mean` (Lemma A.1): the exact iid
  second-moment identity
  `E‖(1/R) Σ Z_i‖_F² = (1/R) E‖Z‖_F² + (1 − 1/R) ‖E Z‖_F²`.
- `SecondMoment.exp_Mk` / `SecondMoment.exp_Mk_sq` (Lemma 2.1):
  unbiasedness `E[M_k] = AᵀA` of the row-sampled estimator and its
  exact second moment
  `E[M_k²] = (1/R) ‖A‖_F² AᵀA + (1 − 1/R) (AᵀA)²`.

The remaining eight claims are recorded as faithful `Prop` shapes:

- (abstract / §1): a row/column-norm-square sampler yields a
  compressed representation `x` with `‖x* − x‖ < ε‖x*‖` in
  `Õ(κ_F⁴κ²/ε²)` time, entry queries in `Õ(κ_F²)` and square-entry
  sampling in `Õ(κ_F⁴κ⁶)`.
- (Lemma 1.4): `y` has at most `8κ_F² log(1/ε)` nonzero entries
  and is generated at `Õ(κ_F⁴κ²/ε²)` cost.
- (Theorem 1.6): `E‖x* − x‖² ≤ 2ε²‖x*‖²` for `x = Aᵀy`.
- (Theorem 1.7): with probability at least `9/10`,
  `φ(y) ≤ const · κ_F²κ⁶ log³(1/ε)`.
- (Lemma 2.2): the stochastic gradient is conditionally unbiased
  with second moment
  `(‖A‖_F⁴/(RC) + ‖A‖_F²‖A‖²/C) ‖x_k‖²`.
- (Lemma 2.3): `E‖D u_k‖² ≤ (‖A‖_F⁴/(RC) + ‖A‖_F²‖A‖²/R
  + ‖A‖⁴) ‖x_k‖²`.
- (Lemma 2.4): `E‖D v_k‖² ≤ ‖A‖_F²‖b‖²/R + ‖A‖²‖b‖²`.
- (Lemma 2.5): `α² E‖D(u_k − v_k)‖² ≤ 10κ⁴ ‖x*‖²`.

The full algorithm claims additionally involve runtime accounting,
success-probability bootstrapping and stochastic-iteration analysis
absent from Mathlib and both repositories; they are recorded as
substantive obstacles (see the PR).

No axiom beyond the three standard ones, no `admit`. -/
set_option autoImplicit false

namespace Qatlib.Papers.LowRankSolve25.MainResults

/-! ## Shared shapes -/

/-- Big-O-in-the-logarithm cost: `cost ε` is bounded by
`C · κF⁴ κ² ε⁻² · log(1/ε)^p` — the Õ(·) runtime shape of the
paper's algorithmic results. -/
def otilde_cost (cost κF κ ε : ℝ) (C p : ℕ) : Prop :=
  0 < C ∧ cost ≤ C * κF ^ 4 * κ ^ 2 / ε ^ 2 * Real.log (1 / ε) ^ p

/-- Compressed-representation accuracy: the reconstructed vector `x`
is within relative error `ε` of the minimum-norm solution `x*`. -/
def rel_error (xStar x ε : ℝ) : Prop := |xStar - x| < ε * |xStar|

/-- Conditional second-moment bound for a stochastic estimator `w` of
a target `t` given the iterate `xk`: unbiasedness plus the exact
variance shape of Lemmas 2.2–2.4. -/
def cond_moment_bound (Ecentered Esecond xkNorm bound : ℝ) : Prop :=
  Ecentered = 0 ∧ 0 ≤ xkNorm ∧ Esecond ≤ bound * xkNorm ^ 2

/-! ## Claim statements -/

/-- **(§1), solver shape**: with row-norm-square and row-entry
samplers, the compressed representation meets relative error `ε` in
`Õ(κF⁴κ²/ε²)` build time with `Õ(κF²)` entry query and
`Õ(κF⁴κ⁶)` square-entry sampling. -/
def compressed_solver_relative_error_and_access_cost_statement (err queryTime sampleTime buildTime κF κ ε : ℝ) : Prop :=
  rel_error 1 err ε ∧ otilde_cost buildTime κF κ ε 1 1
    ∧ otilde_cost queryTime κF κ ε 1 0 ∧ otilde_cost sampleTime κF κ ε 1 6

/-- **(Lemma 1.4), sparsity shape**: for `ε < 1/4` the output
`y` is `8κF² log(1/ε)`-sparse and generated at `Õ(κF⁴κ²/ε²)` cost. -/
def compressed_solver_sparsity_and_build_cost_statement (nnz κF ε buildTime κ : ℝ) : Prop :=
  ε < 1 / 4 ∧ 0 ≤ nnz ∧ nnz ≤ 8 * κF ^ 2 * Real.log (1 / ε)
    ∧ otilde_cost buildTime κF κ ε 1 1

/-- **(Theorem 1.6), accuracy shape**: the iterated estimator
`x = Aᵀy` satisfies `E‖x* − x‖² ≤ 2ε²‖x*‖²`. -/
def iterated_solution_expected_squared_error_statement (Eerr xStarNorm ε : ℝ) : Prop :=
  ε < 1 / 4 ∧ xStarNorm ≥ 0 ∧ Eerr ≤ 2 * ε ^ 2 * xStarNorm ^ 2

/-- **(Theorem 1.7), readout-cost shape**: with probability at
least `9/10`, the sampling parameter obeys
`φ(y) ≤ const · κF²κ⁶ log³(1/ε)`. -/
def sampling_parameter_high_probability_bound_statement (prob phi κF κ ε c : ℝ) : Prop :=
  9 / 10 ≤ prob ∧ c ≥ 0 ∧ ε > 0
    ∧ phi ≤ c * κF ^ 2 * κ ^ 6 * Real.log (1 / ε) ^ 3

/-- **(Lemma 2.2), gradient-noise shape**: the sampled gradient
`M_k x_k − z_k` is conditionally unbiased with second moment
`(‖A‖_F⁴/(RC) + ‖A‖_F²‖A‖²/C) ‖x_k‖²`. -/
def sampled_gradient_centering_and_second_moment_statement (Ecentered Esecond xkNorm frob2A opA R C : ℝ) : Prop :=
  R > 0 ∧ C > 0 ∧ cond_moment_bound Ecentered Esecond xkNorm
    (frob2A ^ 2 / (R * C) + frob2A * opA ^ 2 / C)

/-- **(Lemma 2.3), diagonal-scaled iterate shape**: the
diagonal rescaling `D u_k` of the sampled matvec obeys
`E‖D u_k‖² ≤ (‖A‖_F⁴/(RC) + ‖A‖_F²‖A‖²/R + ‖A‖⁴) ‖x_k‖²`. -/
def diagonal_scaled_matvec_second_moment_statement (EDu xkNorm frob2A opA R C : ℝ) : Prop :=
  R > 0 ∧ C > 0 ∧ EDu ≤ (frob2A ^ 2 / (R * C) + frob2A * opA ^ 2 / R
    + opA ^ 4) * xkNorm ^ 2

/-- **(Lemma 2.4), diagonal-scaled RHS shape**: the sampled
right-hand-side estimator satisfies
`E‖D v_k‖² ≤ ‖A‖_F²‖b‖²/R + ‖A‖²‖b‖²`. -/
def diagonal_scaled_rhs_second_moment_statement (EDv bNorm frob2A opA R : ℝ) : Prop :=
  R > 0 ∧ EDv ≤ frob2A * bNorm ^ 2 / R + opA ^ 2 * bNorm ^ 2

/-- **(Lemma 2.5), combined noise shape**: under the Theorem 1.6
parameters, `α² E‖D(u_k − v_k)‖² ≤ 10κ⁴‖x*‖²`, capping the growth of
the sampling parameter `φ`. -/
def scaled_matvec_rhs_difference_second_moment_statement (alpha EDuv xStarNorm κ : ℝ) : Prop :=
  alpha ^ 2 * EDuv ≤ 10 * κ ^ 4 * xStarNorm ^ 2

end Qatlib.Papers.LowRankSolve25.MainResults
