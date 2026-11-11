/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TrapPrepared.InhomTrapPreparedSolutionStat

/-!
# Specification of the forced LCHS preparation-window bound

`InhomogeneousTrapezoidOptimalPreparationCost` records the assumptions and conclusion of the
trapezoidal forced-evolution window bound. It requires unitary input and source preparations, a
prescribed positive time subdivision count, a bound on the source-mass correction, and a lower
bound on the forced output norm.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `InhomogeneousTrapezoidOptimalPreparationCost`: specifies the `8 * q + 1` window estimate.

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

open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.WindowLchs
open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.LchsSimulation.TrapPrepared

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that the computed trapezoidal forced-evolution schedule gives window size at
most `8 * q + 1`, with `q = (1 + ∫ u in s..t, ‖toEuclidean_fromVec (b u)‖) / τ`, under the
stated preparation, regularity, and source-mass hypotheses. -/
def InhomogeneousTrapezoidOptimalPreparationCost : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L L' H H' : ℝ → Matrix I I ℂ)
    (b b' b'' : ℝ → QState I) (s t ε τ Λ β β₂ lamL lamH lamLd lamHd bmax : ℝ)
    (Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ) (i₀ : I),
    Continuous L → Continuous H → Continuous b →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s < t →
    0 < ε → 0 < bmax → 0 < τ → ε ≤ τ / 2 →
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
    B ∈ Matrix.unitaryGroup I ℂ → (∀ l, P l ∈ Matrix.unitaryGroup I ℂ) →
    (∀ l : Fin (Mt + 1), b (inhTrapNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ =
        ((‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
          b (inhTrapNode Mt s t l)) →
    Mt = max 1 (Nat.ceil (Real.sqrt
      ((((lamL + lamH)^2 + (lamLd + lamHd))*bmax + 2*(lamL + lamH)*β + β₂)*
        (t-s)^3/(3*ε)))) →
    β*(t-s)^2/(Mt : ℝ) ≤ (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖) →
    τ ≤ ‖toEuclidean_fromVec
      (orderedForcedSolution (fun u => L u + Complex.I • H u) b s (B *ᵥ Ket i₀) t)‖ →
    let K := timeDependentLchsWindowCutoff (min (ε/2) (ε/(4*(t-s)*bmax)))
    let N := timeDependentLchsWindowNodes (min (ε/2) (ε/(4*(t-s)*bmax))) Λ
    let γ := inhTrapUnifiedCoeff b s t K N Mt
    let α := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass γ
    let q := (1 + (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖)) / τ
    (staticLchsWindow α τ : ℝ) ≤ 8*q + 1

end Qatlib.Concepts.LchsSimulation.TrapPrepared
