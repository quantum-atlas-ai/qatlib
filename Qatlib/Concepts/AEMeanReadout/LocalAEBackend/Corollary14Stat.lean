/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Spec

def expected : Prop :=
  ∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N), 2 ≤ N →
  ∀ (hM : 2 ≤ approxCountCor14Grid N),
  let t : ℝ := (S.card : ℝ)
  ∑ z ∈ Finset.univ.filter (fun z : Fin (approxCountCor14Grid N) =>
      |(approxCountCor14Output N z : ℝ)-t| <
        2*Real.pi*Real.sqrt (t*((N : ℝ)-t)/(N : ℝ))+11),
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (approxCountCor14Grid N) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
      (⟨0,hN⟩ : Fin N) S (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM).prob z
      ≥ 8/Real.pi^2

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Spec
