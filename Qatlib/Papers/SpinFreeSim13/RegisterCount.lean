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

set_option autoImplicit false
namespace Qatlib.Papers.SpinFreeSim13.RegisterCount

abbrev Spatial := Bool × Bool

abbrev Spinful := (Bool × Bool) × (Bool × Bool)

abbrev Occupation := Fin 4 → Bool

abbrev Readout := Bool × Spatial

def spinfulOccupation : Spinful ≃ Occupation where
  toFun x := ![x.1.1,x.1.2,x.2.1,x.2.2]
  invFun y := ((y 0,y 1),(y 2,y 3))
  left_inv := by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
  right_inv := by intro y; funext i; fin_cases i <;> rfl

theorem spatial_card : Fintype.card Spatial = 2^2 := by decide

theorem spinful_card : Fintype.card Spinful = 2^4 := by decide

theorem occupation_card : Fintype.card Occupation = 2^4 := by decide

theorem conventional_equal_card : Fintype.card Spinful = Fintype.card Occupation :=
  Fintype.card_congr spinfulOccupation

theorem readout_card : Fintype.card Readout = 2^3 := by decide

theorem spatial_lt_spinful : Fintype.card Spatial < Fintype.card Spinful := by decide
end Qatlib.Papers.SpinFreeSim13.RegisterCount
