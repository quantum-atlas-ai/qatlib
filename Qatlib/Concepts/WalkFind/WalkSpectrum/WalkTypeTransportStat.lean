/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk
set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

def WalkTypeTransport : Prop :=
  ∀ (k N r : ℕ), 1 ≤ k → k ≤ r → k < N - r →
    ∀ (I : Finset (Fin N)), I.card = k →
      (∀ jt : Fin (2 * k + 1),
        jwWalkBig N r *ᵥ jwPsiBigAt k N r I jt =
          ∑ i : Fin (2 * k + 1), jwWalk k N r i jt • jwPsiBigAt k N r I i) ∧
      (∀ jt : Fin (2 * k + 1),
        jwFlipBig k N r I *ᵥ jwPsiBigAt k N r I jt =
          ∑ i : Fin (2 * k + 1), jwFlipTilde k i jt • jwPsiBigAt k N r I i)

end Qatlib.Concepts.WalkFind.WalkSpectrum
