/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

/-!
# Basis counts for spin-free registers

This module compares concrete Boolean register types in the simulation setting of
[Whitfield2013]. Two spatial registers have four basis labels, two spatial-spin pairs and four
occupation bits each have sixteen, and adding one readout bit to the spatial registers gives
eight.

## Main statements

* `spinfulOccupation`: an explicit equivalence between the spatial-spin and occupation label
  types.
* `conventional_equal_card`: equality of their cardinalities.
* `spatial_lt_spinful`: the spatial-register type has strictly smaller cardinality.

## References

* [Whitfield, 2013][Whitfield2013]
-/

set_option autoImplicit false
namespace Qatlib.Papers.SpinFreeSim13.RegisterCount

/-- The basis-label type of two Boolean spatial registers. -/
abbrev Spatial := Bool × Bool

/-- The basis-label type of two particles, each with a Boolean spatial label and a Boolean spin
label. -/
abbrev Spinful := (Bool × Bool) × (Bool × Bool)

/-- The type of Boolean occupation labels for four modes. -/
abbrev Occupation := Fin 4 → Bool

/-- A Boolean readout control together with the two spatial-register labels. -/
abbrev Readout := Bool × Spatial

/-- The equivalence flattening the two spatial-spin label pairs into four Boolean occupation
labels. See [Whitfield2013]. -/
def spinfulOccupation : Spinful ≃ Occupation where
  toFun x := ![x.1.1,x.1.2,x.2.1,x.2.2]
  invFun y := ((y 0,y 1),(y 2,y 3))
  left_inv := by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
  right_inv := by intro y; funext i; fin_cases i <;> rfl

/-- The two Boolean spatial registers have `2 ^ 2` basis labels. See [Whitfield2013]. -/
theorem spatial_card : Fintype.card Spatial = 2^2 := by decide

/-- The two spatial-spin register pairs have `2 ^ 4` basis labels. -/
theorem spinful_card : Fintype.card Spinful = 2^4 := by decide

/-- The four Boolean occupation registers have `2 ^ 4` basis labels. See [Whitfield2013]. -/
theorem occupation_card : Fintype.card Occupation = 2^4 := by decide

/-- The spatial-spin register type and the four-mode occupation type have equal cardinality. See
[Whitfield2013]. -/
theorem conventional_equal_card : Fintype.card Spinful = Fintype.card Occupation :=
  Fintype.card_congr spinfulOccupation

/-- Adding a Boolean control to the spatial register gives `2 ^ 3` basis labels. See
[Whitfield2013]. -/
theorem readout_card : Fintype.card Readout = 2^3 := by decide

/-- The two-register spatial basis has strictly fewer labels than the spatial-spin basis. -/
theorem spatial_lt_spinful : Fintype.card Spatial < Fintype.card Spinful := by decide
end Qatlib.Papers.SpinFreeSim13.RegisterCount
