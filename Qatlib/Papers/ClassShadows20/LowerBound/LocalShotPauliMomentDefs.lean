/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath

open Matrix
open scoped Classical BigOperators

namespace Qatlib.Papers.ClassShadows20.LowerBound

noncomputable def theorem6CodeState (n : ℕ) (ε : ℝ) (a : Fin n → Option (Fin 3)) :
    Operator (2 ^ n) :=
  (1 / (2 ^ n : ℝ)) • 1 + (3 * ε / (2 ^ n : ℝ)) • tensorPauliWord n a

noncomputable def localShotValue {n : ℕ} {J : Type} (Uf : J → Operator 2)
    (w : ℝ) (ψ : Fin n → Operator 2) (uw : Fin n → J)
    (ρ : Operator (2 ^ n)) : ℝ :=
  w * (2 ^ n : ℝ) *
    (Matrix.trace (tensorPauliProduct n ψ *
      (tensorPauliProduct n (fun j => Uf (uw j)) * ρ *
        (tensorPauliProduct n (fun j => Uf (uw j)))ᴴ))).re
end Qatlib.Papers.ClassShadows20.LowerBound
