/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
set_option warningAsError false

open scoped Classical

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

def OrbitCharacterCoordsSubgoal : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E] (k : ℕ) (V : Fin k → E),
    AddSubgroup.closure (Set.range V) = ⊤ →
    (∀ χ η : AddChar E ℂ, (∀ j, (χ (V j)) = (η (V j))) → χ = η)
    ∧ (∀ (χ : AddChar E ℂ) (j : Fin k),
          ∃ p : Fin (Fintype.card E),
            (χ (V j)) = primRoot (Fintype.card E) ^ ((p : ℤ)))

end Qatlib.Concepts.HspRecovery.AbelianSampling
