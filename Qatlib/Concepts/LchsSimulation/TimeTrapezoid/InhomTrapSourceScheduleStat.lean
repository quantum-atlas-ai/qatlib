/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.InhomogeneousTrapezoidSourceQuadrature

/-!
# Specification of the trapezoidal source schedule

`InhomogeneousTrapezoidSourceSchedule` specifies a cutoff, parameter node count, and time
subdivision count from accuracy and regularity data. Its conclusion combines a parameter
quadrature budget with source error at most `ε / 2` and an upper bound on the weighted norms of
the sampled source vectors.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `InhomogeneousTrapezoidSourceSchedule`: records the schedule and its required estimates.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.WindowLchs

namespace Qatlib.Concepts.LchsSimulation.TimeTrapezoid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that the prescribed cutoff, parameter grid, and positive time subdivision
count meet the parameter error budget, source error `ε / 2`, and integrated-source-norm
bound with correction `β * (t - s) ^ 2 / Mt`. -/
def InhomogeneousTrapezoidSourceSchedule : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L L' H H' : ℝ → Matrix I I ℂ)
    (b b' b'' : ℝ → QState I) (s t ε Λ β β₂ lamL lamH lamLd lamHd bmax : ℝ),
    Continuous L → Continuous H → Continuous b →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s < t →
    0 < ε → 0 < bmax →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt L (L' u) u) →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt H (H' u) u) →
    (∀ u, s ≤ u → u ≤ t → ‖L' u‖ ≤ lamLd) →
    (∀ u, s ≤ u → u ≤ t → ‖H' u‖ ≤ lamHd) →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u) →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt b' (b'' u) u) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b'' u)‖ ≤ β₂) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b u)‖ ≤ bmax) →
    (∀ u, ‖L u‖ ≤ lamL) → (∀ u, ‖H u‖ ≤ lamH) →
    2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    let K := timeDependentLchsWindowCutoff (min (ε/2) (ε/(4*(t-s)*bmax)))
    let N := timeDependentLchsWindowNodes (min (ε/2) (ε/(4*(t-s)*bmax))) Λ
    let Mt := max 1 (Nat.ceil (Real.sqrt
      ((((lamL + lamH)^2 + (lamLd + lamHd))*bmax + 2*(lamL + lamH)*β + β₂)*
        (t-s)^3/(3*ε))))
    0 < Mt ∧
    2*(K : ℝ)/(N : ℝ) ≤ 1/2 ∧
    (2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/N) *
      (2/Real.pi + ∫ u in s..t, ‖L u‖)) ≤ min (ε/2) (ε/(4*(t-s)*bmax)) ∧
    ‖toEuclidean_fromVec (inhTrapSourceSum L H b s t K N Mt -
      inhSourceResponse L H b s t)‖ ≤ ε/2 ∧
    (∑ l : Fin (Mt+1), inhTrapWeight Mt s t l *
      ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖) ≤
      (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖) + β*(t-s)^2/(Mt : ℝ)

end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
