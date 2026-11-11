/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Papers.ClassShadows20.LowerBound.LocalShotPauliMomentDefs

/-!
# Local Pauli shot moment contract

`LocalShotPauliMomentSubgoal` specifies the first and second moments of product-measurement shot
values on a positive-weight Pauli code. Its ensemble premises require unitary rotations on the
probability support, an exact first moment, and a second-moment identity for Hermitian test
operators.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `LocalShotPauliMomentSubgoal`: states the shot mean and second-moment bound under explicit
  ensemble assumptions.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.ClassShadows20.LowerBound

open Matrix
open scoped Classical BigOperators

/-- The proposition asserting shot mean `w` and second moment at most `w² * (1 + 9ε² / 3^k)` for
the specified local Pauli codes and ensembles. Its second-moment premise is restricted to
Hermitian test operators. -/
def LocalShotPauliMomentSubgoal : Prop :=
  ∀ (n k : ℕ) (J : Type) [Fintype J] [DecidableEq J]
    (κ : FinDist J) (Uf : J → Operator 2)
    (hκU : ∀ j, 0 < κ.prob j → Uf j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hκ1 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re =
        (Matrix.trace A).re / 2)
    (hκ2 : ∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
      A.IsHermitian → B.IsHermitian →
      ∑ j, κ.prob j * (Matrix.trace (A * (Uf j)ᴴ * Pp * Uf j)).re *
          (Matrix.trace (B * (Uf j)ᴴ * Pp * Uf j)).re =
        ((Matrix.trace A).re * (Matrix.trace B).re +
          (Matrix.trace (A * B)).re) / 6)
    (w : ℝ) (hw : 0 ≤ w)
    (ψ : Fin n → Operator 2) (hψ : ∀ j, IsPureDensityOperator (ψ j))
    (a : Fin n → Option (Fin 3))
    (hk : 1 ≤ k) (hS : tensorPauliWeight a = k)
    (ε : ℝ) (hε : 0 < ε) (hε1 : 3 * ε ≤ 1),
    (∑ uw : Fin n → J, (∏ j, κ.prob (uw j)) *
        localShotValue Uf w ψ uw (theorem6CodeState n ε a) = w)
    ∧ (∑ uw : Fin n → J, (∏ j, κ.prob (uw j)) *
        (localShotValue Uf w ψ uw (theorem6CodeState n ε a)) ^ 2 ≤
      w ^ 2 * (1 + 9 * ε ^ 2 / (3 ^ k : ℝ)))

end Qatlib.Papers.ClassShadows20.LowerBound
