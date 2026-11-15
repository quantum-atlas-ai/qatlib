/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUBProductBases

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood

def CanonicalUnextendibilityRestricted : Prop :=
  ∀ ψ : QState (Fin 6),
    ¬ (∀ (r : Fin 3) (j : Fin 6),
      Complex.normSq (Inner (Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases r j) ψ) = (1 : ℝ) / 6)

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood
