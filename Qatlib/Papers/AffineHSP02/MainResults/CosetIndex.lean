/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.AffineHSP02.MainResults

variable {p : ℕ} [Fact p.Prime]

theorem card_units_zmod (p : ℕ) [Fact p.Prime] :
    Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, ZMod.card]

theorem orderOf_dvd_card_units {p : ℕ} [Fact p.Prime] (a : (ZMod p)ˣ) :
    orderOf a ∣ p - 1 := by
  have h := orderOf_dvd_card (x := a)
  rwa [card_units_zmod] at h

theorem card_zpowers_units {p : ℕ} [Fact p.Prime] (a : (ZMod p)ˣ) :
    Nat.card (Subgroup.zpowers a : Subgroup (ZMod p)ˣ) = orderOf a :=
  Nat.card_zpowers a

theorem index_zpowers_units {p : ℕ} [Fact p.Prime] (a : (ZMod p)ˣ) :
    (Subgroup.zpowers a).index = (p - 1) / orderOf a := by
  have hcard : Nat.card (Subgroup.zpowers a : Subgroup (ZMod p)ˣ) = orderOf a :=
    Nat.card_zpowers a
  have hmul : Nat.card (Subgroup.zpowers a : Subgroup (ZMod p)ˣ)
      * (Subgroup.zpowers a).index = Nat.card ((ZMod p)ˣ) :=
    Subgroup.card_mul_index (Subgroup.zpowers a)
  have hunits : Nat.card ((ZMod p)ˣ) = p - 1 := by
    rw [Nat.card_eq_fintype_card, card_units_zmod]
  rw [hcard, hunits] at hmul
  have hpos : 0 < orderOf a := orderOf_pos a
  calc (Subgroup.zpowers a).index
      = (orderOf a * (Subgroup.zpowers a).index) / orderOf a := by
        rw [Nat.mul_div_cancel_left _ hpos]
    _ = (p - 1) / orderOf a := by rw [hmul]

theorem card_cosets_zpowers {p : ℕ} [Fact p.Prime] (a : (ZMod p)ˣ) :
    Nat.card ((ZMod p)ˣ ⧸ Subgroup.zpowers a) = (p - 1) / orderOf a := by
  rw [← Subgroup.index_eq_card, index_zpowers_units]

theorem card_cosets_of_orderOf_eq {p : ℕ} [Fact p.Prime] (a : (ZMod p)ˣ) (q : ℕ)
    (hq : orderOf a = q) :
    Nat.card ((ZMod p)ˣ ⧸ Subgroup.zpowers a) = (p - 1) / q := by
  rw [card_cosets_zpowers, hq]

end Qatlib.Papers.AffineHSP02.MainResults
