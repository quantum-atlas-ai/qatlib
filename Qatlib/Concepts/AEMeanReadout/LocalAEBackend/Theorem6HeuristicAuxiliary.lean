/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat

/-!
# Distributional costs of heuristic search

This module defines the number of successful heuristic seeds and the classical and quantum
average-cost quantities used in [BrassardEtAl2002]. The quantum quantity averages the second
cost counter of the finite-horizon search loop over the input distribution.

## Main statements

* `BHMTTh6.heuristicGoodCount`: the number of seeds producing a marked output.
* `BHMTTh6.heuristicQuantumChiCost`: the distributional quantum search cost.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchSpec

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh6

/-- The number of seeds `r` for which the heuristic output `G f r` satisfies the Boolean
predicate `f`. -/
def heuristicGoodCount (n : ℕ) (G : (Fin n → Bool) → Fin n → Fin n)
    (f : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun r => f (G f r) = true)).card

/-- The input-distribution average of `n / heuristicGoodCount n G f`, representing the
reciprocal successful-seed fraction. -/
noncomputable def heuristicClassicalTime (n : ℕ) (G : (Fin n → Bool) → Fin n → Fin n)
    (D : PMF (Fin n → Bool)) : ℝ :=
  ∑ f : (Fin n → Bool), (D f).toReal * ((n : ℝ) / ((heuristicGoodCount n G f : ℕ) : ℝ))

/-- The input-distribution average of the expected second cost counter of Fourier-prepared
finite-horizon search over successful heuristic seeds. -/
noncomputable def heuristicQuantumChiCost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ) : ℝ≥0∞ :=
  ∑ f : (Fin n → Bool), (D f) *
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
        (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
      (fun out => (out.2.2 : ℝ≥0∞))
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh6
