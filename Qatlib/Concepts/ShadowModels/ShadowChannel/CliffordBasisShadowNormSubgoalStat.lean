/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordBasisShadowChannelSubgoalStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped Classical BigOperators

def CliffordBasisShadowNormSubgoal : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h36 : ∀ Pp : Operator d, IsPureDensityOperator Pp →
      ∀ B₀ C₀ : Operator d, B₀.IsHermitian → C₀.IsHermitian →
        Matrix.trace B₀ = 0 → Matrix.trace C₀ = 0 →
      (∑ i, (μ.prob i * (Matrix.trace (B₀ * ((Uf i)ᴴ * Pp * Uf i))).re *
          (Matrix.trace (C₀ * ((Uf i)ᴴ * Pp * Uf i))).re) •
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
