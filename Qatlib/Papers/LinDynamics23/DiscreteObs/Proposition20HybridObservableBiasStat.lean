/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Papers.LinDynamics23.DiscreteObs.DiscreteLchsCost

/-!
# Hybrid observable bias statement

`Proposition20HybridObservableBias` specifies observable reconstruction for a discrete
approximation to dissipative ordered evolution. It requires uniform matrix-approximation error
and vector quadrature error, then states the coefficient double-sum identity and a bias bound in
terms of those errors, coefficient mass, observable norm, and target-vector norm. See
[AnChildsLin2026] for the paper context.

## Main statements

* `Proposition20HybridObservableBias`: The proposition that discrete hybrid observable
  reconstruction has the specified double-sum identity and bias at most `‖O‖ * (η * (2 * τ + η)
  + γ * εhs * (2 * τ + 2 * η + γ * εhs))` under the stated evolution and approximation
  hypotheses.

## References

* [An et al., 2026][AnChildsLin2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that discrete hybrid observable reconstruction has the specified double-sum
identity and bias at most `‖O‖ * (η * (2 * τ + η) + γ * εhs * (2 * τ + 2 * η + γ * εhs))`
under the stated evolution and approximation hypotheses. -/
def Proposition20HybridObservableBias : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (kk : Fin N → ℝ) (W : Fin N → Matrix I I ℂ) (L H : ℝ → Matrix I I ℂ)
    (B : Matrix I I ℂ) (i₀ : I) (O : Matrix I I ℂ) (T η εhs : ℝ),
    Continuous L → Continuous H →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    0 ≤ T → (∀ j, W j ∈ 𝐔[I]) → B ∈ 𝐔[I] → O.IsHermitian →
    let U : ℝ → Matrix I I ℂ :=
      fun k => orderedEvolution (fun u => Complex.I • (H u + k • L u)) 0 T
    let x₀ : QState I := B.mulVec (Ket i₀)
    let uT : QState I :=
      (orderedEvolution (fun u => L u + Complex.I • H u) 0 T).mulVec x₀
    let vU : QState I := (∑ j, c j • U (kk j)).mulVec x₀
    let v : QState I := (∑ j, c j • W j).mulVec x₀
    let γ : ℝ := ∑ j, ‖c j‖
    let τ : ℝ := ‖toEuclidean_fromVec uT‖
    (∀ j, ‖W j - U (kk j)‖ ≤ εhs) →
    ‖toEuclidean_fromVec vU - toEuclidean_fromVec uT‖ ≤ η →
    (∑ l : Fin N, ∑ j : Fin N, star (c l) * c j *
        Inner (W l *ᵥ x₀) (O.mulVec (W j *ᵥ x₀)) = Inner v (O.mulVec v)) ∧
    (‖Inner v (O.mulVec v) - Inner uT (O.mulVec uT)‖ ≤
      ‖O‖ * (η * (2 * τ + η) + γ * εhs * (2 * τ + 2 * η + γ * εhs)))

end Qatlib.Papers.LinDynamics23.DiscreteObs
