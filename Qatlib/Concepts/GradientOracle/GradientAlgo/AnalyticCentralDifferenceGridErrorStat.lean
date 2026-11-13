/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat
import Qatlib.Concepts.GradientOracle.GradientAlgo.TensorChebyshevGridBoundStat
import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceGridDefs

/-!
# Specification of analytic grid approximation

`AnalyticCentralDifferenceGridError` states a finite-grid error bound for a central-difference
stencil applied to an analytic function with controlled coordinate derivatives. Its geometric
threshold is the approximation input used in the gradient setting of
[GilyenArunachalamWiebe2019].

## Main statements

* `AnalyticCentralDifferenceGridError`: when `8*R*c*m*sqrt d < 1`, the exceptional grid count is
  at most `M^d/1000`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

open Qatlib.Concepts.GradientOracle.CentralDiff

noncomputable section

namespace Qatlib.Concepts.GradientOracle.GradientAlgo

/-- The proposition that analytic coordinate-derivative growth bounds control central-difference
error outside at most a `1/1000` fraction of the grid, with threshold `T^(2*m+1)/(1-T)` for
`T = 8*R*c*m*sqrt d < 1`. -/
def AnalyticCentralDifferenceGridError : Prop :=
  ∀ (d m : ℕ), 0 < m → ∀ (R c : ℝ), 0 < R → 0 < c →
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
      AnalyticOnNhd ℝ f (Set.univ : Set (EuclideanSpace ℝ (Fin d))) →
      (∀ (k : ℕ) (α : Fin k → Fin d),
        |iteratedFDeriv ℝ k f 0
            (fun i : Fin k => EuclideanSpace.single (α i) (1 : ℝ))|
          ≤ c ^ k * (k : ℝ) ^ ((k : ℝ) / 2)) →
    ∀ M : ℕ, 8 * R * c * (m : ℝ) * Real.sqrt d < 1 →
    ((Finset.univ.filter (fun z : Fin d → Fin M =>
        (8 * R * c * (m : ℝ) * Real.sqrt d) ^ (2 * m + 1)
            / (1 - 8 * R * c * (m : ℝ) * Real.sqrt d)
          < |∑ j : Fin d,
              (fderiv ℝ f 0) (EuclideanSpace.single j (1 : ℝ)) * gridCenter M R (z j)
            - centralDiffApply m f (gridPoint d M R z)|)).card : ℝ)
      ≤ ((M ^ d : ℕ) : ℝ) / 1000

end Qatlib.Concepts.GradientOracle.GradientAlgo
