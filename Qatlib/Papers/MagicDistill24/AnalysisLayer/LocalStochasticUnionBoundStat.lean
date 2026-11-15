/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.AnalysisLayer.LocalStochasticDefs

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.AnalysisLayer

def LocalStochasticUnionBound : Prop :=
  ∀ (ζ t : ℕ) (pp : Finset (Fin ζ) → ℝ) (pPh : ℝ),
    0 ≤ pPh → pPh ≤ 1 → t < ζ → LocalStochasticNoise pp pPh →
      probManyFaults pp t ≤ (Nat.choose ζ (t + 1) : ℝ) * pPh ^ (t + 1)

end Qatlib.Papers.MagicDistill24.AnalysisLayer
