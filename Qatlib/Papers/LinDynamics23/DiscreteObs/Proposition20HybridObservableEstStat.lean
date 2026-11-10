/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinDynamics23.DiscreteObs.Proposition20HybridObservableBiasStat
import Qatlib.Papers.LinDynamics23.DiscreteObs.Proposition20HybridObservableEstDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

section Estimation

variable {N : ℕ}

end Estimation

def Proposition20HybridObservableEstimation : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (W : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (i₀ : I)
    (O : Matrix I I ℂ) (target : ℝ) (ε δ : ℝ) (Lm Mm : ℕ),
    (∀ j, W j ∈ 𝐔[I]) → B ∈ 𝐔[I] → O.IsHermitian →
    0 < ε → 0 < δ → 0 < Lm → 0 < Mm →
    (hγ : 0 < ∑ j, ‖c j‖) →
    let x₀ : QState I := B.mulVec (Ket i₀)
    let v : QState I := (∑ j, c j • W j).mulVec x₀
    let γ : ℝ := ∑ j, ‖c j‖
    let p : FinDist (Fin N × Fin N) := hybridObservableSampleDist c hγ
    let φ : (Fin N × Fin N) → ℝ := hybridObservableSampleValue c W O x₀
    let est : (Fin Mm → Fin Lm → Fin N × Fin N) → ℝ :=
      fun ω => γ ^ 2 * FinDist.medianOfMeans p φ ω
    (|Complex.re (Inner v (O.mulVec v)) - target| ≤ ε / 2) →
    (16 * γ ^ 4 * ‖O‖ ^ 2 / ε ^ 2 ≤ (Lm : ℝ)) →
    (Real.log (1 / δ) / Real.log (2 / Real.sqrt 3) ≤ (Mm : ℝ)) →
    (hybridObservableGroupDist p Lm).probEvent
        (fun ω => ε < |est ω - target|) ≤ δ

end Qatlib.Papers.LinDynamics23.DiscreteObs
