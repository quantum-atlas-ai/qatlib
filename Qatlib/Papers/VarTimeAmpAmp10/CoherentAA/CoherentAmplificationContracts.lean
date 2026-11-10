/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA

open Matrix

def coherentAmplificationWindow : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ), W ∈ Matrix.unitaryGroup I ℂ →
    ∀ (j₀ : I) (S : Finset I) (k : ℕ),
      let a := MeasureProb (ApplyGate W (Ket j₀)) S
      let θ := Real.arcsin (Real.sqrt a)
      let out := Run (preparedMark S) (preparedAACircuit W j₀ k) (Ket j₀)
      MeasureProb out S = Real.sin ((2 * (k : ℝ) + 1) * θ) ^ 2 ∧
      ((2 * (k : ℝ) + 1) * θ ≤ Real.pi / 2 →
        (4 / Real.pi ^ 2) * (2 * (k : ℝ) + 1) ^ 2 * a ≤ MeasureProb out S) ∧
      MeasureProb out S ≤ min ((Real.pi ^ 2 / 4) * (2 * (k : ℝ) + 1) ^ 2 * a) 1

end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
