/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Auxiliary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Spec
def expected : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ BHMTTh17.exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N),
      2 ≤ BHMTTh17.exactCountGrid N
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (BHMTTh17.exactCountM₀ N) z₂)),
    BHMTTh17.exactCountSuccessMass hN S hM₀ hM ≥ 2/3 ∧
    BHMTTh17.exactCountCostMass hN S hM₀ hM ≤
      1000*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Spec
