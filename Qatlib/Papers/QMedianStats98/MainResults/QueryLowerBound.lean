/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.Model.ActualQuery
import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.Symmetrization
import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.FirstTerm

/-!
# From approximate degree to actual query lower bounds

This module transfers polynomial degree lower bounds to Boolean-oracle query experiments,
following the polynomial method in [NayakWu1998]. A promise-computing experiment yields an
approximating polynomial of degree at most twice its query count and, after symmetrization, a
univariate witness on the weight grid.

The explicit first-term consequence bounds the query count below by `sqrt((1 - 2*error) * n / (8
* dist(lo, hi))) / 2` for nonnegative error below one half.

## Main statements

- `actual_grid_witness`: extracts a degree-bounded univariate polynomial from the experiment.
- `actual_query_lower_of_degree_bound`: transfers any valid approximate-degree lower bound.
- `actual_query_first_term`: proves the first square-root query lower bound.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.QMedianStats98.MainResults.QueryLowerBound
open Qatlib.Papers.QMedianStats98.MainResults.Model
open Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound

/-- For valid weights `lo` and `hi`, a query experiment computing the two-weight promise with
nonnegative error has a univariate witness of degree at most twice its query count, bounded
in `[-error, 1 + error]` on the weight grid and approximating one at `lo` and zero at `hi`. -/
theorem actual_grid_witness {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) (lo hi : ℕ) (error : ℝ) (he : 0 ≤ error)
    (hc : A.ComputesPromise lo hi error) (hl : lo ≤ n) (hh : hi ≤ n) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ 2 * A.queries ∧
      (∀ k : ℕ, k ≤ n → q.eval (k : ℝ) ∈ Set.Icc (-error) (1+error)) ∧
      |q.eval (lo : ℝ) - 1| ≤ error ∧ |q.eval (hi : ℝ)| ≤ error := by
  obtain ⟨P,hP,happrox⟩ := A.actual_approximating_polynomial lo hi error he hc
  obtain ⟨q,hq,hgrid,hlo,hhi⟩ := source_symmetrization P lo hi error happrox hl hh
  exact ⟨q,hq.trans hP,hgrid,hlo,hhi⟩

/-- If every polynomial approximating the two-weight promise has total degree at least `bound`,
then any experiment computing that promise with nonnegative error satisfies `bound ≤ 2 *
A.queries`. -/
theorem actual_query_lower_of_degree_bound {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) (lo hi : ℕ) (error : ℝ) (he : 0 ≤ error)
    (hc : A.ComputesPromise lo hi error) (bound : ℝ)
    (hb : ∀ P : MvPolynomial (Fin n) ℝ,
      ApproximatesWithin P lo hi error → bound ≤ (P.totalDegree : ℝ)) :
    bound ≤ 2 * (A.queries : ℝ) := by
  obtain ⟨P,hP,happrox⟩ := A.actual_approximating_polynomial lo hi error he hc
  have hd : (P.totalDegree : ℝ) ≤ 2 * (A.queries : ℝ) := by exact_mod_cast hP
  exact (hb P happrox).trans hd

/-- For `n > 0`, distinct valid promise weights, and `0 ≤ error < 1/2`, a promise-computing
query experiment uses at least `sqrt((1 - 2*error) * n / (8 * dist(lo, hi))) / 2` queries.
This gives the first term of the query lower bound in Corollary 1.2 of [NayakWu1998]. -/
theorem actual_query_first_term {n lo hi : ℕ} (hn : 0 < n)
    (hl : lo ≤ n) (hh : hi ≤ n) (hne : lo ≠ hi)
    {W : Type} [Fintype W] [DecidableEq W] (A : QueryExperiment n W)
    (error : ℝ) (he0 : 0 ≤ error) (he : error < 1/2)
    (hc : A.ComputesPromise lo hi error) :
    Real.sqrt ((1-2*error)*(n : ℝ)/(8*(Nat.dist lo hi : ℝ))) / 2 ≤ (A.queries : ℝ) := by
  have hb := actual_query_lower_of_degree_bound A lo hi error he0 hc
    (Real.sqrt ((1-2*error)*(n : ℝ)/(8*(Nat.dist lo hi : ℝ))))
    (fun p hp => source_polynomial_first_term hn hl hh hne p error he0 he hp)
  linarith

end Qatlib.Papers.QMedianStats98.MainResults.QueryLowerBound
