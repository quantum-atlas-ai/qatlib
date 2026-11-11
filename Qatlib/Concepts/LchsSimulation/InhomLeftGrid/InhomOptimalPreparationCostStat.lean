/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousPreparedSolutionStat

/-!
# Statement of the inhomogeneous preparation cost

`InhomogeneousOptimalPreparationCost` specifies a bound on the amplification-window length for
the scheduled inhomogeneous LCHS quadrature. The hypotheses include positive semidefinite and
Hermitian generator fields, source derivative and norm bounds, source-state preparation
unitaries, a quadrature slack condition, and a lower bound τ on the solution norm. This gives a
concrete finite-grid preparation estimate related to [AnLiuLin2023].

## Main statements

* `InhomogeneousOptimalPreparationCost`: the proposition asserting window length at most `8*q +
  1`.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
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

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.WindowLchs
open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that the prescribed inhomogeneous LCHS schedule has preparation-window
length at most `8*q + 1`, where `q = (1 + ∫ ‖b(u)‖ du) / τ`, under the stated regularity,
preparation, and slack conditions. -/
def InhomogeneousOptimalPreparationCost : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (b b' : ℝ → QState I)
    (s t ε τ Λ β lamL lamH bmax : ℝ) (Mt : ℕ) (B : Matrix I I ℂ)
    (P : Fin Mt → Matrix I I ℂ) (i₀ : I),
    Continuous L → Continuous H → Continuous b →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s < t →
    0 < ε → 0 < bmax → 0 < τ → ε ≤ τ / 2 →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b u)‖ ≤ bmax) →
    (∀ u, ‖L u‖ ≤ lamL) → (∀ u, ‖H u‖ ≤ lamH) →
    2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    B ∈ Matrix.unitaryGroup I ℂ → (∀ l, P l ∈ Matrix.unitaryGroup I ℂ) →
    (∀ l : Fin Mt, b (inhNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ =
        ((‖toEuclidean_fromVec (b (inhNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
          b (inhNode Mt s t l)) →
    Mt = max 1 (Nat.ceil (2*((lamL + lamH)*bmax + β)*(t-s)^2/ε)) →
    β*(t-s)^2/(2*(Mt : ℝ)) ≤ (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖) →
    τ ≤ ‖toEuclidean_fromVec
      (orderedForcedSolution (fun u => L u + Complex.I • H u) b s (B *ᵥ Ket i₀) t)‖ →
    let K := timeDependentLchsWindowCutoff (min (ε/2) (ε/(4*(t-s)*bmax)))
    let N := timeDependentLchsWindowNodes (min (ε/2) (ε/(4*(t-s)*bmax))) Λ
    let γ := inhUnifiedCoeff b s t K N Mt
    let α := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass γ
    let q := (1 + (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖)) / τ
    (staticLchsWindow α τ : ℝ) ≤ 8*q + 1

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
