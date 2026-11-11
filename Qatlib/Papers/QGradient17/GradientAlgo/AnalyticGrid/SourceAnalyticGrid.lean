/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessOpti
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceDefs
import Qatlib.Concepts.GradientOracle.GradientAlgo.CentralDifferenceGridDefs
import Qatlib.Concepts.GradientOracle.GradientAlgo.AnalyticCentralDifferenceGridErrorOpti
import Qatlib.Concepts.GradientOracle.GradientAlgo.TensorChebyshevGridBoundOpti

set_option backward.isDefEq.respectTransparency false

/-!
# GradientAlgo — analytic central-difference grid error (Theorem 24) and the
tensor Chebyshev grid bound (Lemma 36)

Fixed source: arXiv:1711.00465v3, *Optimizing quantum optimization algorithms
via faster quantum gradient computation*.

* Theorem 24 (§5.4, p.28): for an analytic `f : ℝ^d → ℝ` with Gevrey-type
  derivative growth `‖∂^k f(0)‖ ≤ c^k k^{k/2}`, on the symmetric cell-centre
  grid `R · G_M^d` (Definition 17) all but a `1/1000` fraction of grid points
  `y` obey
  `|∇f(0)·y − f_(2m)(y)| ≤ T^{2m+1}/(1−T)` with `T = 8 R c m √d`, under
  `T < 1`.
* Lemma 36 (App. A, p.52): the degree-`k` tensor polynomial of unit-bounded
  coefficients, evaluated at uniform symmetric coordinates in `[−1/2,1/2]`, is
  sub-Chebyshev: at most a `r^{-2k}` fraction of grid points exceed
  `√2 (r √(dk/2))^k`.

Both use the paper's actual grid functions `gridCenter` / `gridPoint` and are
bridges to the Frozen v2.0.2 contracts `analyticCentralDifferenceGridError`
and `tensorChebyshevGridBound`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.GradientOracle.GradientAlgo
open Qatlib.Concepts.GradientOracle.CentralDiff
open scoped BigOperators

namespace Qatlib.Papers.QGradient17.GradientAlgo.AnalyticGrid

/-- Theorem 24 of arXiv:1711.00465v3 (§5.4, p.28): analytic functions with
derivative growth `|∂_α f(0)| ≤ c^k k^{k/2}` have their linear form
`∇f(0)·y` approximated by the degree-`2m` central difference scheme
`f_(2m)(y)` on all but a `1/1000` fraction of the symmetric grid
`R · G_M^d`, with geometric error tail `T^{2m+1}/(1−T)`, `T = 8 R c m √d`.
Reuses `analyticCentralDifferenceGridError`. -/
theorem source_theorem_twentyfour
    (d m : ℕ) (hm : 0 < m) (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : AnalyticOnNhd ℝ f (Set.univ : Set (EuclideanSpace ℝ (Fin d))))
    (hb : ∀ (k : ℕ) (α : Fin k → Fin d),
      |iteratedFDeriv ℝ k f 0
          (fun i : Fin k => EuclideanSpace.single (α i) (1 : ℝ))|
        ≤ c ^ k * (k : ℝ) ^ ((k : ℝ) / 2))
    (M : ℕ) (hconv : 8 * R * c * (m : ℝ) * Real.sqrt d < 1) :
    ((Finset.univ.filter (fun z : Fin d → Fin M =>
        (8 * R * c * (m : ℝ) * Real.sqrt d) ^ (2 * m + 1)
            / (1 - 8 * R * c * (m : ℝ) * Real.sqrt d)
          < |∑ j : Fin d,
              (fderiv ℝ f 0) (EuclideanSpace.single j (1 : ℝ)) * gridCenter M R (z j)
            - centralDiffApply m f (gridPoint d M R z)|)).card : ℝ)
      ≤ ((M ^ d : ℕ) : ℝ) / 1000 :=
  analyticCentralDifferenceGridError d m hm R c hR hc f hf hb M hconv

/-- Lemma 36 (grid form) of arXiv:1711.00465v3 (App. A, p.52): for coordinates
drawn uniformly from a finite symmetric `S ⊆ [−1/2,1/2]`, a degree-`k` tensor
polynomial with `|H_α| ≤ 1` exceeds `√2 (r √(dk/2))^k` on at most a `r^{-2k}`
fraction of the `|S|^d` grid points, for every `r > 1`.  Reuses
`tensorChebyshevGridBound`. -/
theorem source_lemma_thirtysix
    (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (r : ℝ) (hr : 1 < r)
    (S : Finset ℝ) (hbound : ∀ v ∈ S, |v| ≤ 1 / 2)
    (hsymm : ∀ v ∈ S, -v ∈ S) (hne : S.Nonempty)
    (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1) :
    ((Finset.univ.filter (fun y : Fin d → S =>
        Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k
          ≤ |∑ α : Fin k → Fin d, H α * ∏ i : Fin k, (y (α i) : ℝ)|)).card : ℝ)
      ≤ (((S.card : ℕ) ^ d : ℕ) : ℝ) / r ^ (2 * k) :=
  tensorChebyshevGridBound d k hd hk r hr S hbound hsymm hne H hH

end Qatlib.Papers.QGradient17.GradientAlgo.AnalyticGrid
