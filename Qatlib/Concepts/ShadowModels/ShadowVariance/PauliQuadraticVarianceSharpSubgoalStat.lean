/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliPairRecords
import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic

/-!
# Sharp quadratic Pauli variance specification

This module packages the support-sensitive quadratic Pauli variance bounds as
`PauliQuadraticVarianceSharpSubgoal`. The proposition specifies the conditional-variance and
kernel-standard-deviation estimates required by the quadratic classical-shadow analysis
[HuangKuengPreskill2020].

## Main statements

* `PauliQuadraticVarianceSharpSubgoal`: a uniform variance specification for supported Pauli
  pair observables.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ShadowModels.ShadowVariance

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The proposition that every supported Pauli pair observable of norm at least one has
conditional variance and kernel standard deviation at most four to the larger support size
times its squared norm. -/
def PauliQuadraticVarianceSharpSubgoal : Prop :=
  ∀ (n q : ℕ) (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ)
    (S₁ S₂ : Finset (Fin n)) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ),
    pauliPairSupported S₁ S₂ ww c →
    1 ≤ ‖pauliPairObservable n q ww c‖ →
    let p := tensorPauliLaw n ρ hρ
    let h := quadraticShadowKernel n (pauliPairObservable n q ww c)
    pairConditionalVariance p h ≤
      (4 : ℝ)^(max S₁.card S₂.card) * ‖pauliPairObservable n q ww c‖^2 ∧
    Real.sqrt (pairKernelVariance p h) ≤
      (4 : ℝ)^(max S₁.card S₂.card) * ‖pauliPairObservable n q ww c‖^2

end Qatlib.Concepts.ShadowModels.ShadowVariance
