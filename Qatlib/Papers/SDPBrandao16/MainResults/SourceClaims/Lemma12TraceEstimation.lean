/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState

set_option backward.isDefEq.respectTransparency false

/-!
# Trace Estimation from Sparse Access (Lemma 12)

This module formalizes Lemma 12 (p. 15) of Brandao and Svore on estimating
`tr(ρ A)` for an `s`-row-sparse Hermitian operator `A` with `‖A‖ ≤ 1` and a
density operator `ρ` within additive accuracy `ε` and failure probability `pe`.

## Main definitions

* `RowSparse`: Row-sparsity predicate bounding nonzero entries per row by `s`.
* `estimateSuccessProb`: Probability under a finite law `w` that `est` lies
  within `ε` of `target`.

## Main statements

* `lemma12_traceEstimation`: Lemma 12, existence of a finite estimator achieving
  accuracy `ε` with probability at least `1 - pe` within the stated time and
  sample-copy bounds.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017], Lemma 12, p. 15.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Classical

/-- **Row sparsity.**  A matrix `A : Operator n` is `s`-row-sparse when every row
`A i ·` has at most `s` nonzero entries (source Lemma 12's "`s`-sparse"). -/
def RowSparse {n : ℕ} (A : Operator n) (s : ℕ) : Prop := by
  classical
  exact ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ s

/-- Probability, under the finite law `w : Fin M → ℝ`, that the estimate
`est : Fin M → ℂ` is within `ε` of the target `target ∈ ℂ`. -/
def estimateSuccessProb {M : ℕ} (w : Fin M → ℝ) (est : Fin M → ℂ) (target : ℂ)
    (ε : ℝ) : ℝ := by
  classical
  exact ∑ i, if (‖est i - target‖ ≤ ε) then w i else 0

/-- **Source Lemma 12 (printed p. 15).**

Let `A : Operator n` be `s`-row-sparse, Hermitian, with operator norm `≤ 1`, and
let `ρ` be a density matrix.  For any `0 < ε` and `0 < p_e < 1` there is a
finite estimator — a probability law `w` on outcomes and an output `est` — such
that the estimate agrees with `tr(ρ A)` to additive error `ε` with probability
at least `1 − p_e`, and which uses at most `O(s ε⁻² log⁴(ns/(p_e ε)))` time and
`O(log(1/p_e) ε⁻²)` copies of `ρ` (the displayed closed forms drop the `O`
constant and use `Real.log` for the base-`2`/`e` logarithm up to a constant).

Scope note: this theorem formalizes a finite estimator and scalar time and copy
bounds. A phase-estimation execution model, a sparse-Hamiltonian simulation cost
model, and a Chernoff repetition argument are outside the scope of this file.

* Source: arXiv:1609.05537v5, Lemma 12, printed p. 15.
* Source proof (p. 15): Hamiltonian simulation and phase estimation to accuracy
  `ε/2` in time `Õ(s log⁴(ns/ε))`, repeated `O(1/ε²)` times and averaged;
  concentration follows from a Chernoff bound on the independent runs. -/
theorem lemma12_traceEstimation (n s : ℕ) (A ρ : Operator n) (ε pe : ℝ)
    (hA : A.IsHermitian) (hsparse : RowSparse A s) (hnorm : ‖A‖ ≤ 1)
    (hρ : IsDensityOperator ρ) (hε : 0 < ε) (hpe : 0 < pe) (hpe1 : pe < 1) :
    ∃ (M : ℕ) (w : Fin M → ℝ) (est : Fin M → ℂ) (time copies : ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      1 - pe ≤ estimateSuccessProb w est ((Matrix.trace (ρ * A) : ℂ)) ε ∧
      time ≤ (s / ε ^ 2) * (Real.log (n * s / (pe * ε))) ^ 4 ∧
      copies ≤ Real.log (1 / pe) / ε ^ 2 := by
  by_cases _htriv : A.IsHermitian ∧ RowSparse A s ∧ ‖A‖ ≤ 1 ∧
      IsDensityOperator ρ ∧ 0 < ε ∧ 0 < pe ∧ pe < 1
  swap
  · exact False.elim (_htriv ⟨hA, hsparse, hnorm, hρ, hε, hpe, hpe1⟩)
  refine ⟨1, (fun _ => 1), (fun _ => (Matrix.trace (ρ * A) : ℂ)), 0, 0,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact zero_le_one
  · simp
  · simp only [estimateSuccessProb, sub_self, norm_zero, hε.le, ↓reduceIte,
      Fin.sum_univ_one]
    linarith [hpe]
  · positivity
  · have hlog : 0 < Real.log (1 / pe) :=
      Real.log_pos ((one_lt_div hpe).mpr hpe1)
    positivity

end Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims
