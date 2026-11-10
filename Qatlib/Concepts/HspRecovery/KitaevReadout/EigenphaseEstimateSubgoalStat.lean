/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest
set_option warningAsError false

open Matrix
open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

def EigenphaseEstimateSubgoal : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε < 1 →
    ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ),
      (U *ᵥ ψ = eigenPhase φ • ψ) →
      ∀ s : ℕ,
        36 * Real.log (4 / ε) / (Real.sin (Real.pi * δ)) ^ 2 ≤ s →
        (eigenphaseSampleLaw φ s).probEvent (L := 1)
            (fun ω => ¬ ∃ m : ℤ, |eigenphaseDecode s (ω 0) - φ + m| ≤ δ)
          ≤ ε

end Qatlib.Concepts.HspRecovery.KitaevReadout
