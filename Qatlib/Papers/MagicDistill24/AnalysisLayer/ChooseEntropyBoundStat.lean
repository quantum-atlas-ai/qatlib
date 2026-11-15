/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.AnalysisLayer.LocalStochasticDefs

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.AnalysisLayer

def ChooseEntropyBound : Prop :=
  ∀ (n k : ℕ), k ≤ n →
    (Nat.choose n k : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)))

end Qatlib.Papers.MagicDistill24.AnalysisLayer
