/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.AnalysisLayer.LocalStochasticDefs

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.AnalysisLayer

def ConstantOverheadDistillation : Prop :=
  ∀ (C cK cTl cTh : ℝ), 1 ≤ C → 0 < cK → 0 < cTl → cTl ≤ cTh → cTh ≤ 1 →
    0 < Real.exp (-(Real.binEntropy cTl / cTl)) / C ∧
    ∀ (pPh : ℝ), 0 ≤ pPh → pPh < Real.exp (-(Real.binEntropy cTl / cTl)) / C →
      ∀ (n k t : ℕ), 0 < n →
        cK * (n : ℝ) ≤ (k : ℝ) → cTl * (n : ℝ) ≤ (t : ℝ) + 1 → (t : ℝ) + 1 ≤ cTh * (n : ℝ) →
        ((Nat.choose n (t + 1) : ℝ) * (C * pPh) ^ (t + 1)
            ≤ (pPh / (Real.exp (-(Real.binEntropy cTl / cTl)) / C)) ^ (t + 1))
        ∧ (C * (n : ℝ) / (k : ℝ) ≤ C / cK)
        ∧ (∀ ε > 0, ∃ n₀ : ℕ, ∀ n' ≥ n₀,
            (pPh / (Real.exp (-(Real.binEntropy cTl / cTl)) / C)) ^ (cTl * (n' : ℝ)) ≤ ε)

end Qatlib.Papers.MagicDistill24.AnalysisLayer
