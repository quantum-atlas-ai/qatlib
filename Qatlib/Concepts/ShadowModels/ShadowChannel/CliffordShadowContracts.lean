/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped Classical BigOperators

def basisProjector {d : ℕ} (b : Fin d) : Operator d :=
  fun i j => if i = b ∧ j = b then (1 : ℂ) else 0

def CliffordMomentHypothesis (d : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) : Prop :=
  ∀ Pp : Operator d, IsPureDensityOperator Pp → ∀ A : Operator d,
    (∑ i, (μ.prob i * (Matrix.trace (A * (Uf i * Pp * (Uf i)ᴴ))).re) •
        ((Uf i)ᴴ * Pp * Uf i)) =
      ((Matrix.trace A).re / ((d : ℝ) * ((d : ℝ) + 1))) • 1 +
      (1 / ((d : ℝ) * ((d : ℝ) + 1))) • A

def CliffordBasisShadowChannelSubgoalLegacy : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h35 : CliffordMomentHypothesis d I μ Uf),
    (∀ ρ : Operator d, IsDensityOperator ρ →
      (∑ b, ∑ i, (μ.prob i *
          (Matrix.trace (basisProjector b * (Uf i * ρ * (Uf i)ᴴ))).re) •
          ((Uf i)ᴴ * basisProjector b * Uf i)) =
        (1 / ((d : ℝ) + 1)) • ρ + (1 / ((d : ℝ) + 1)) • 1)
    ∧ (∀ ρ : Operator d, IsDensityOperator ρ → ∀ Oo : Operator d,
      (∑ b, ∑ i, (μ.prob i *
          (Matrix.trace (basisProjector b * (Uf i * ρ * (Uf i)ᴴ))).re) *
          (Matrix.trace (Oo * (((d : ℝ) + 1) •
            ((Uf i)ᴴ * basisProjector b * Uf i) - 1))).re) =
        (Matrix.trace (Oo * ρ)).re)

def CliffordBasisShadowNormSubgoalLegacy : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h36 : ∀ Pp : Operator d, IsPureDensityOperator Pp →
      ∀ B₀ C₀ : Operator d, B₀.IsHermitian → C₀.IsHermitian →
        Matrix.trace B₀ = 0 → Matrix.trace C₀ = 0 →
      (∑ i, (μ.prob i * (Matrix.trace (B₀ * (Uf i * Pp * (Uf i)ᴴ))).re *
          (Matrix.trace (C₀ * (Uf i * Pp * (Uf i)ᴴ))).re) •
          ((Uf i)ᴴ * Pp * Uf i)) =
        ((Matrix.trace (B₀ * C₀)).re /
            ((d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 2))) • 1 +
        (1 / ((d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 2))) • (B₀ * C₀ + C₀ * B₀))
    (σ : Operator d) (hσ : IsDensityOperator σ)
    (Oo : Operator d) (hO : Oo.IsHermitian) (hO0 : Matrix.trace Oo = 0),
    (∑ b, ∑ i, (μ.prob i *
        (Matrix.trace (basisProjector b * (Uf i * σ * (Uf i)ᴴ))).re) *
        (((d : ℝ) + 1) *
          (Matrix.trace (Oo * ((Uf i)ᴴ * basisProjector b * Uf i))).re) ^ 2) ≤
      3 * (Matrix.trace (Oo * Oo)).re

end Qatlib.Concepts.ShadowModels.ShadowChannel
