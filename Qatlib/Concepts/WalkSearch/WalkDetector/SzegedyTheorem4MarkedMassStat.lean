/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS

/-!
# Nonempty marked-mass contract

`SzegedyTheorem4MarkedMass` states that any Boolean predicate marking at least one element of a
positive finite domain has uniform marked fraction at least the reciprocal of its size. The
contract supplies a basic input to the marked-state detection bounds of [Szegedy2004].

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Matrix

open Qatlib.Concepts.WalkSearch.ProjectorCS

namespace Qatlib.Concepts.WalkSearch.WalkDetector

/-- The proposition that a nonempty Boolean marked set on a positive finite domain has uniform
marked fraction at least the reciprocal of the domain size. -/
def SzegedyTheorem4MarkedMass : Prop :=
  ∀ (n : ℕ) (f : Fin n → Bool),
    0 < n → (∃ i, f i = true) →
    (1 / (n : ℝ)) ≤ markedFraction (Finset.univ.filter (fun i => f i = true))

end Qatlib.Concepts.WalkSearch.WalkDetector
