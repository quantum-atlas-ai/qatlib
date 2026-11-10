/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordShadowContracts
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordShadowDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped Classical BigOperators

def CliffordBasisShadowChannelSubgoal : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h35 : CliffordMomentHypothesisV2 d I μ Uf),
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

end Qatlib.Concepts.ShadowModels.ShadowChannel
