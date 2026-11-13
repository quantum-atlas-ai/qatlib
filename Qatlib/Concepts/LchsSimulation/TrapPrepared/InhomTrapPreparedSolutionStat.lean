/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.InhomogeneousTrapezoidSourceQuadrature
import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers
import Mathlib.Logic.Equiv.Fin.Basic
import Qatlib.Concepts.LchsSimulation.TrapPrepared.InhomTrapPreparedSolutionDefs

/-!
# Specification of the prepared forced LCHS output

`InhomogeneousTrapezoidPreparedSolution` states a conditional density error estimate for the
unified trapezoidal LCHS circuit. Given an approximation to the forced solution with vector
error at most `ε` and solution norm at least `τ`, each positive-success amplification output has
density error at most `4 * ε / τ` when `ε ≤ τ / 2`.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `InhomogeneousTrapezoidPreparedSolution`: specifies the error of the postselected
  forced-solution density.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.LchsSimulation.TrapPrepared

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

section InhomogeneousTrapezoidUnifiedDefinitions

variable {I : Type} [Fintype I] [DecidableEq I]

end InhomogeneousTrapezoidUnifiedDefinitions

/-- The proposition that, under the stated unitary preparation and raw approximation hypotheses
with `ε ≤ τ / 2`, every positive-success unified circuit output has density trace norm error
at most `4 * ε / τ` from the forced solution. -/
def InhomogeneousTrapezoidPreparedSolution : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t ε τ : ℝ) (K N Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (i₀ : I) (j₀ : Fin (N + N * (Mt + 1))),
    Continuous L → Continuous H → (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    s ≤ t → B ∈ Matrix.unitaryGroup I ℂ → (∀ l, P l ∈ Matrix.unitaryGroup I ℂ) →
    (∀ l : Fin (Mt + 1), b (inhTrapNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ =
        ((‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
          b (inhTrapNode Mt s t l)) →
    0 < K → 0 < N → 0 < Mt → 0 < ε → 0 < τ → ε ≤ τ / 2 →
    let A := fun u => L u + Complex.I • H u
    let γ := inhTrapUnifiedCoeff b s t K N Mt
    let V := inhTrapUnifiedUnitary L H s t K N Mt B P
    let uT := orderedForcedSolution A b s (B *ᵥ Ket i₀) t
    τ ≤ ‖toEuclidean_fromVec uT‖ →
    ‖toEuclidean_fromVec ((∑ x, γ x • V x) *ᵥ (B *ᵥ Ket i₀) - uT)‖ ≤ ε →
    ∀ k : ℕ,
    let S := Finset.univ.filter (fun x : Fin (N + N * (Mt + 1)) × I => x.1 = j₀)
    let y := Run (preparedMark S) (staticLchsCompile γ V B j₀ i₀ k) (Ket (j₀, i₀))
    0 < MeasureProb y S →
    Matrix.traceNorm (staticLchsOutputDensity (staticLchsDataBranch j₀ y) -
      staticLchsOutputDensity uT) ≤ 4 * ε / τ

end Qatlib.Concepts.LchsSimulation.TrapPrepared
