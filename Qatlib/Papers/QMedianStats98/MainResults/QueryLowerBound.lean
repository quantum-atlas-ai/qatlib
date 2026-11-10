/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.Model.ActualQuery
import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.Symmetrization
import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.FirstTerm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.QMedianStats98.MainResults.QueryLowerBound
open Qatlib.Papers.QMedianStats98.MainResults.Model
open Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound

theorem actual_grid_witness {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) (lo hi : ℕ) (error : ℝ) (he : 0 ≤ error)
    (hc : A.ComputesPromise lo hi error) (hl : lo ≤ n) (hh : hi ≤ n) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ 2 * A.queries ∧
      (∀ k : ℕ, k ≤ n → q.eval (k : ℝ) ∈ Set.Icc (-error) (1+error)) ∧
      |q.eval (lo : ℝ) - 1| ≤ error ∧ |q.eval (hi : ℝ)| ≤ error := by
  obtain ⟨P,hP,happrox⟩ := A.actual_approximating_polynomial lo hi error he hc
  obtain ⟨q,hq,hgrid,hlo,hhi⟩ := source_symmetrization P lo hi error happrox hl hh
  exact ⟨q,hq.trans hP,hgrid,hlo,hhi⟩

theorem actual_query_lower_of_degree_bound {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) (lo hi : ℕ) (error : ℝ) (he : 0 ≤ error)
    (hc : A.ComputesPromise lo hi error) (bound : ℝ)
    (hb : ∀ P : MvPolynomial (Fin n) ℝ,
      ApproximatesWithin P lo hi error → bound ≤ (P.totalDegree : ℝ)) :
    bound ≤ 2 * (A.queries : ℝ) := by
  obtain ⟨P,hP,happrox⟩ := A.actual_approximating_polynomial lo hi error he hc
  have hd : (P.totalDegree : ℝ) ≤ 2 * (A.queries : ℝ) := by exact_mod_cast hP
  exact (hb P happrox).trans hd

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
