/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.Model.Basic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SymmetrizationAverageSubgoalBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BlockSubstitution

/-!
# Symmetrizing the partial symmetric approximation problem

This module reduces multivariate approximation of the two-weight partial symmetric function to a
univariate polynomial on the weight grid, as used in [NayakWu1998]. Averaging over each Boolean
Hamming layer preserves the global range and the approximation guarantees at the two promised
weights.

The resulting polynomial has natural degree no greater than the original total degree, allowing
univariate degree estimates to apply to the original approximation problem.

## Main statements

- `source_average_grid_range`: preserves the range on every valid weight layer.
- `source_average_positive` and `source_average_negative`: preserve the two promise values.
- `source_symmetrization`: packages the univariate witness and its degree bound.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
open Qatlib.Papers.QMedianStats98.MainResults.Model
open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The layer-average polynomial of an `ApproximatesWithin` polynomial takes values in `[-error,
1 + error]` at every integer weight `k ≤ n`. -/
theorem source_average_grid_range {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (lo hi : ℕ) (error : ℝ) (hp : ApproximatesWithin p lo hi error) (k : ℕ) (hk : k ≤ n) :
    (avgPoly p).eval (k : ℝ) ∈ Set.Icc (-error) (1 + error) := by
  rw [← layerAverage_eq_avgPoly p k (by simpa only [Fintype.card_fin] using hk)]
  exact block_layerAverage_bounds p k (by simpa only [Fintype.card_fin] using hk)
    (-error) (1+error) (fun X _ => hp.1 X)

/-- At a valid positive weight `lo`, the layer-average polynomial remains within `error` of one. -/
theorem source_average_positive {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (lo hi : ℕ) (error : ℝ) (hp : ApproximatesWithin p lo hi error) (hl : lo ≤ n) :
    |(avgPoly p).eval (lo : ℝ) - 1| ≤ error := by
  have hb := block_layerAverage_bounds p lo (by simpa only [Fintype.card_fin] using hl)
    (1-error) (1+error) (by
      intro X hX
      have h := hp.2.1 X hX
      rw [abs_le] at h
      change 1-error ≤ evalBool p X ∧ evalBool p X ≤ 1+error
      exact ⟨by linarith [h.1], by linarith [h.2]⟩)
  rw [layerAverage_eq_avgPoly p lo (by simpa only [Fintype.card_fin] using hl)] at hb
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- At a valid negative weight `hi`, the layer-average polynomial remains within `error` of
zero. -/
theorem source_average_negative {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (lo hi : ℕ) (error : ℝ) (hp : ApproximatesWithin p lo hi error) (hh : hi ≤ n) :
    |(avgPoly p).eval (hi : ℝ)| ≤ error := by
  have hb := block_layerAverage_bounds p hi (by simpa only [Fintype.card_fin] using hh)
    (-error) error (by
      intro X hX
      exact abs_le.mp (hp.2.2 X hX))
  rw [layerAverage_eq_avgPoly p hi (by simpa only [Fintype.card_fin] using hh)] at hb
  exact abs_le.mpr hb

/-- An approximating multivariate polynomial has a univariate witness of degree at most its
total degree, with range `[-error, 1 + error]` on the weight grid and the same approximation
guarantees at valid weights `lo` and `hi`. This is the symmetrization reduction used in
[NayakWu1998]. -/
theorem source_symmetrization {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (lo hi : ℕ) (error : ℝ) (hp : ApproximatesWithin p lo hi error)
    (hl : lo ≤ n) (hh : hi ≤ n) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ p.totalDegree ∧
      (∀ k : ℕ, k ≤ n → q.eval (k : ℝ) ∈ Set.Icc (-error) (1+error)) ∧
      |q.eval (lo : ℝ) - 1| ≤ error ∧ |q.eval (hi : ℝ)| ≤ error :=
  ⟨avgPoly p, avgPoly_natDegree_le p, source_average_grid_range p lo hi error hp,
    source_average_positive p lo hi error hp hl, source_average_negative p lo hi error hp hh⟩

end Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
