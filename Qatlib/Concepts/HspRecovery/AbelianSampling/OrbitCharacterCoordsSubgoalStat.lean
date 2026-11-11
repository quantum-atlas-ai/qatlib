/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Specification of orbit character coordinates

`OrbitCharacterCoordsSubgoal` specifies coordinates for complex additive characters using their
values on a generating family. It requires these coordinates to determine the character uniquely
and to lie on the primitive root grid indexed by `Fin (Fintype.card E)`. [Kitaev1995]

## Main statements

* `OrbitCharacterCoordsSubgoal`: the proposition specifying injective character coordinates and
  phase grid labels.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

open scoped Classical

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

/-- The proposition that character values on a generating family determine each complex additive
character uniquely, and that each value is a power of the primitive root whose order is the
finite group cardinality. -/
def OrbitCharacterCoordsSubgoal : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E] (k : ℕ) (V : Fin k → E),
    AddSubgroup.closure (Set.range V) = ⊤ →
    (∀ χ η : AddChar E ℂ, (∀ j, (χ (V j)) = (η (V j))) → χ = η)
    ∧ (∀ (χ : AddChar E ℂ) (j : Fin k),
          ∃ p : Fin (Fintype.card E),
            (χ (V j)) = primRoot (Fintype.card E) ^ ((p : ℤ)))

end Qatlib.Concepts.HspRecovery.AbelianSampling
