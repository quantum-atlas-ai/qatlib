/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSConsumers
import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindow
import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers

/-!
# Corrected discrete LCHS skeleton statement

`Theorem15DiscreteSkeleton` requires the discrete reconstruction to be within `η` of a nonzero
target, with `η ≤ τ * min ε 1 / 8` and `η < τ`. It specifies trace-norm control of the selected
normalized output, exact compilation counts, and success probability at least `1 / 8` for the
weighted amplification window. See [AnChildsLin2026] for the paper context.

## Main statements

* `Theorem15DiscreteSkeleton`: The discrete LCHS proposition combining output trace-norm error
  at most `4 * η / τ`, unitary compilation with `k` queries and word length `10 * k + 4`, and a
  weighted-window success bound of `1 / 8`, under the stated reconstruction-closeness and
  error-gap hypotheses.

## References

* [An et al., 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The discrete LCHS proposition combining output trace-norm error at most `4 * η / τ`, unitary
compilation with `k` queries and word length `10 * k + 4`, and a weighted-window success
bound of `1 / 8`, under the stated reconstruction-closeness and error-gap hypotheses. -/
def Theorem15DiscreteSkeleton : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (i₀ : I) (E : Matrix I I ℂ)
    (ε : ℝ),
    (∀ j, V j ∈ 𝐔[I]) → B ∈ 𝐔[I] →
    0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass c → 0 < ε →
    let x₀ := B.mulVec (Ket i₀)
    let v := E.mulVec x₀
    let τ := ‖toEuclidean_fromVec v‖
    let α := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass c
    0 < τ →
    ∀ η : ℝ, η ≤ τ * min ε 1 / 8 → η < τ →
    ‖toEuclidean_fromVec ((∑ j, c j • V j).mulVec x₀) -
      toEuclidean_fromVec v‖ ≤ η →
      (∀ j₀ : Fin N,
          let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
          let y := staticLchsDataBranch j₀
            (Run (preparedMark S)
              (staticLchsCompile c V B j₀ i₀ 0)
              (Ket (j₀, i₀)))
          0 < MeasureProb
            (Run (preparedMark S)
              (staticLchsCompile c V B j₀ i₀ 0)
              (Ket (j₀, i₀))) S →
          (staticLchsOutputDensity y -
              staticLchsOutputDensity v).traceNorm ≤
            4 * η / τ) ∧
      (∀ j₀ : Fin N, ∀ k : ℕ,
          IsUnitaryCircuit
            (staticLchsCompile c V B j₀ i₀ k) ∧
          QueryCount
            (staticLchsCompile c V B j₀ i₀ k) = k ∧
          (staticLchsWord k).length = 10 * k + 4) ∧
      (∀ j₀ : Fin N,
          let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
          let m := staticLchsWindow α τ
          1 ≤ m ∧ ((m : ℝ) ≤ 2 * α / τ + 1 ∧
            1 / 8 ≤ ∑ j : Fin m,
              staticLchsIterationWeight m j *
                MeasureProb
                  (Run (preparedMark S)
                    (staticLchsCompile c V B j₀ i₀ j.val)
                    (Ket (j₀, i₀))) S))

end Qatlib.Papers.LinDynamics23.DiscreteObs
