/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib

def Theorem6AmplitudeEstimation : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : ℕ) (A : Matrix I I ℂ) (j : I)
    (S : Finset I),
    (hA : A ∈ Matrix.unitaryGroup I ℂ) → (hP : 4 ≤ P) →
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
          |aeEstimate P z - MeasureProb (preparedAAState A j) S| <
            2 * Real.pi / (P : ℝ) *
              Real.sqrt (MeasureProb (preparedAAState A j) S) +
              Real.pi ^ 2 / (P : ℝ) ^ 2),
        (aeLaw P A j S hA (by omega : 2 ≤ P)).prob z

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
