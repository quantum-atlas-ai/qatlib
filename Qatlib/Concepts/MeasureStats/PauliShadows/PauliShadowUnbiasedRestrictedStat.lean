/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

open Matrix

namespace Qatlib.Concepts.MeasureStats.PauliShadows

def PauliShadowUnbiasedRestrictedSubgoal : Prop :=
  ∀ (ρ : Matrix (Fin 2) (Fin 2) ℂ), IsDensityOperator ρ →
    (1 / 3 : ℂ) • ∑ a : Fin 3, ∑ b : Bool,
      ((Matrix.trace (PauliProjector a b * ρ)).re : ℂ) • PauliShadow b a = ρ

end Qatlib.Concepts.MeasureStats.PauliShadows
