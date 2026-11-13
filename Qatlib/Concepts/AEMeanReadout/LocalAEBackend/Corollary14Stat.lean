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

/-!
# Specification of the rounded counting bound

This module states the rounded counting specification from Corollary 14 of [BrassardEtAl2002].
The proposition `Corollary14Spec.expected` requires success probability at least `8/π²` for an
integer estimate with error strictly less than `2π√(t(N-t)/N) + 11`, using the grid `⌈√N⌉` under
the stated validity hypotheses.

## Main statements

* `Corollary14Spec.expected`: the required rounded-counting probability bound.

## References

* [Brassard et al., Corollary 14][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Spec

/-- The specification that, for `N ≥ 2` and a valid grid `⌈√N⌉`, rounded counting has error
strictly below `2π√(t(N-t)/N) + 11` with probability at least `8/π²` [Brassard et al.,
Corollary 14][BrassardEtAl2002]. -/
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
