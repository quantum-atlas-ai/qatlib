/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordShadowContracts
public import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
public import Qatlib.Foundations.PureStateMath.MixedState
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordShadowDefs

@[expose] public section

/-!
# Clifford basis shadow channel specification

`CliffordBasisShadowChannelSubgoal` packages the basis shadow channel formula and the
unbiasedness of its inverse reconstruction. Both statements use the actual Born weight for
measurement after applying the ensemble unitary, with `CliffordMomentHypothesisV2` as the moment
assumption. See [HuangKuengPreskill2020] for background.

## Main statements

* `CliffordBasisShadowChannelSubgoal`: the channel and reconstruction proposition for the
  corrected moment orientation.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped Classical BigOperators

/-- The proposition that a unitary ensemble satisfying `CliffordMomentHypothesisV2` in dimension
at least two has the displayed depolarizing basis channel and unbiased inverse
reconstruction under actual Born record weights. -/
def CliffordBasisShadowChannelSubgoal : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d)
    (_hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (_h35 : CliffordMomentHypothesisV2 d I μ Uf),
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
