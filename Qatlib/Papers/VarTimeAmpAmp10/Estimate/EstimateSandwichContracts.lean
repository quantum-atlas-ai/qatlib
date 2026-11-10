/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate

open Matrix

def estimateSandwich : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ), W ∈ Matrix.unitaryGroup I ℂ →
    ∀ (j₀ : I) (S : Finset I) (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∃ (M r : ℕ), 2 ≤ M ∧
    ∃ (est : (Fin r → Fin M) → ℝ) (law : (Fin r → Fin M) → ℝ)
      (good : Finset (Fin r → Fin M)),
      (∑ ω, law ω = 1) ∧ (∀ ω, 0 ≤ law ω) ∧
      (1 - δ ≤ ∑ ω ∈ good, law ω) ∧
      (∀ ω ∈ good, |est ω - MeasureProb (ApplyGate W (Ket j₀)) S|
        ≤ MeasureProb (ApplyGate W (Ket j₀)) S / 4
          + 8 / (M : ℝ) * Real.sqrt (MeasureProb (ApplyGate W (Ket j₀)) S)
          + 10 / (M : ℝ) ^ 2) ∧
      (MeasureProb (ApplyGate W (Ket j₀)) S = 0 → ∀ ω, est ω = 0) ∧
      (∃ (R : Type) (_ : Fintype R) (O : Matrix R R ℂ) (cct : Circuit R)
        (init : QState R) (lbl : R → (Fin r → Fin M)),
        (∀ ω, law ω =
          MeasureProb (Run O cct init) (Finset.univ.filter (fun p => lbl p = ω))) ∧
        QueryCount cct + GateCount cct ≤ r * (6 * M - 3))

end Qatlib.Papers.VarTimeAmpAmp10.Estimate
