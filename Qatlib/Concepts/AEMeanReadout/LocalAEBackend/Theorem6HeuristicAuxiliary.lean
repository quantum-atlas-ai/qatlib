/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchSpec

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh6

def heuristicGoodCount (n : ℕ) (G : (Fin n → Bool) → Fin n → Fin n)
    (f : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun r => f (G f r) = true)).card

noncomputable def heuristicClassicalTime (n : ℕ) (G : (Fin n → Bool) → Fin n → Fin n)
    (D : PMF (Fin n → Bool)) : ℝ :=
  ∑ f : (Fin n → Bool), (D f).toReal * ((n : ℝ) / ((heuristicGoodCount n G f : ℕ) : ℝ))

noncomputable def heuristicQuantumChiCost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (D : PMF (Fin n → Bool)) (T : ℕ) : ℝ≥0∞ :=
  ∑ f : (Fin n → Bool), (D f) *
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (BHMTQSearch.qSearchLoop (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix n)
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
        (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
      (fun out => (out.2.2 : ℝ≥0∞))
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh6
