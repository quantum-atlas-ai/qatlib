/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureStat
import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers
import Mathlib.Logic.Equiv.Fin.Basic
import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousPreparedSolutionDefs

/-!
# Prepared inhomogeneous LCHS solution specification

`InhomogeneousPreparedSolution` specifies a trace-norm accuracy guarantee for the successful
branch of the compiled unified LCHS family. It assumes normalized source preparations, a raw
approximation error, and a positive lower bound on the exact solution norm. See [AnLiuLin2023]
for the mathematical setting.

## Main statements

* `InhomogeneousPreparedSolution`: The prepared-solution guarantee that raw error at most `ε`
  yields trace-norm error at most `4 * ε / τ` for every successful compiled branch, under the
  stated preparation and solution-norm hypotheses.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
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

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

section InhomogeneousUnifiedDefinitions

variable {I : Type} [Fintype I] [DecidableEq I]

end InhomogeneousUnifiedDefinitions

/-- The prepared-solution guarantee that raw error at most `ε` yields trace-norm error at most
`4 * ε / τ` for every successful compiled branch, under the stated preparation and
solution-norm hypotheses. -/
def InhomogeneousPreparedSolution : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t ε τ : ℝ) (K N Mt : ℕ) (B : Matrix I I ℂ) (P : Fin Mt → Matrix I I ℂ)
    (i₀ : I) (j₀ : Fin (N + N * Mt)),
    Continuous L → Continuous H → (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    s ≤ t → B ∈ Matrix.unitaryGroup I ℂ → (∀ l, P l ∈ Matrix.unitaryGroup I ℂ) →
    (∀ l : Fin Mt, b (inhNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ =
        ((‖toEuclidean_fromVec (b (inhNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
          b (inhNode Mt s t l)) →
    0 < K → 0 < N → 0 < Mt → 0 < ε → 0 < τ → ε ≤ τ / 2 →
    let A := fun u => L u + Complex.I • H u
    let γ := inhUnifiedCoeff b s t K N Mt
    let V := inhUnifiedUnitary L H s t K N Mt B P
    let uT := orderedForcedSolution A b s (B *ᵥ Ket i₀) t
    τ ≤ ‖toEuclidean_fromVec uT‖ →
    ‖toEuclidean_fromVec ((∑ x, γ x • V x) *ᵥ (B *ᵥ Ket i₀) - uT)‖ ≤ ε →
    ∀ k : ℕ,
    let S := Finset.univ.filter (fun x : Fin (N + N * Mt) × I => x.1 = j₀)
    let y := Run (preparedMark S) (staticLchsCompile γ V B j₀ i₀ k) (Ket (j₀, i₀))
    0 < MeasureProb y S →
    Matrix.traceNorm (staticLchsOutputDensity (staticLchsDataBranch j₀ y) -
      staticLchsOutputDensity uT) ≤ 4 * ε / τ

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
