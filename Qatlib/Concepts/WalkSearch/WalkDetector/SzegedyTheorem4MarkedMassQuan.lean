/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4MarkedMassStat

/-!
# Lower bound on nonempty marked mass

`szegedyTheorem4MarkedMass` proves that a nonempty set selected by a Boolean predicate on `Fin
n` has uniform marked fraction at least 1/n when n is positive. This supplies a marked-mass
parameter for the quantum-walk detection framework of [Szegedy2004].

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.WalkSearch.ProjectorCS

namespace Qatlib.Concepts.WalkSearch.WalkDetector
open scoped BigOperators

/-- On `Fin n` with positive `n`, a Boolean predicate marking at least one element has marked
fraction at least `1 / n`, supplying a marked-mass input for the detection framework of
[Szegedy2004]. -/
theorem szegedyTheorem4MarkedMass : SzegedyTheorem4MarkedMass := by
  classical
  intro n f hn ⟨i, hi⟩
  have hc : 1 ≤ (Finset.univ.filter (fun i => f i = true)).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hcr : (1 : ℝ) ≤ (Finset.univ.filter (fun i => f i = true)).card := by
    exact_mod_cast hc
  simpa only [markedFraction, Fintype.card_fin] using
    div_le_div_of_nonneg_right hcr (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)

end Qatlib.Concepts.WalkSearch.WalkDetector
