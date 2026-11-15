/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.AnalysisLayer

def LocalStochasticNoise {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (pPh : ℝ) : Prop :=
  (∀ F, 0 ≤ pp F)
    ∧ (∑ F ∈ Finset.univ, pp F = 1)
    ∧ ∀ S ⊆ Finset.univ, ∑ F ∈ Finset.univ.filter (fun F => S ⊆ F), pp F ≤ pPh ^ S.card

def probManyFaults {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (t : ℕ) : ℝ :=
  ∑ F ∈ Finset.univ.filter (fun F => t < F.card), pp F

end Qatlib.Papers.MagicDistill24.AnalysisLayer
