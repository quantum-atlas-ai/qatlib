/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.UnitaryGroup
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem12K2WindowSpec

def expected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ), 2 ≤ k →
    let a : ℝ :=
        Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState A j) S
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z - a| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ)
            +(k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw M A j S hA hM).prob z ≥ 1-1/(2*((k : ℝ)-1))

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem12K2WindowSpec
