/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator

/-!
# A Pauli shadow reconstruction specification

`PauliShadowUnbiasedRestrictedSubgoal` states the reconstruction identity for single-qubit Pauli
measurements. The average assigns weight one third to each Pauli axis and Born weights to its
two outcomes. See [HuangKuengPreskill2020].

## Main statements

* `PauliShadowUnbiasedRestrictedSubgoal`: the single-qubit unbiasedness proposition.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

open Matrix

namespace Qatlib.Concepts.MeasureStats.PauliShadows

/-- The proposition that the Born-weighted Pauli snapshots, averaged uniformly over the three
axes, equal the input qubit density operator. -/
def PauliShadowUnbiasedRestrictedSubgoal : Prop :=
  ∀ (ρ : Matrix (Fin 2) (Fin 2) ℂ), IsDensityOperator ρ →
    (1 / 3 : ℂ) • ∑ a : Fin 3, ∑ b : Bool,
      ((Matrix.trace (PauliProjector a b * ρ)).re : ℂ) • PauliShadow b a = ρ

end Qatlib.Concepts.MeasureStats.PauliShadows
