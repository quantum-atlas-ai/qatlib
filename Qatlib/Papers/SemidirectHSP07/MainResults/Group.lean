/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Aut
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Totient

/-!
# Cyclic semidirect products and subgroup forms

This module defines the multiplicative cyclic presentation `Cyc n`, the semidirect product `SDG
p r φ`, and its distinguished generators `xGen` and `yGen`. It records their orders and the
cardinality of the ambient group, including its finite `p`-group structure for prime `p`.

The predicates `ClassOne` and `ClassTwo` specify the two action relations used in
[CosmePortugal2007]. The subgroup expressions `form1a`, `form1b`, `form2`, and `form3` provide
the generated forms used in subsequent analysis.

## Main statements

- `orderOf_xGen`, `orderOf_yGen`, and `card_SDG` compute the basic orders.
- `card_SDG_prime_pow` and `isPGroup_SDG` describe the prime-power setting.
- `ClassOne` and `ClassTwo` fix the action on the standard generator.
- `form1a`, `form1b`, `form2`, and `form3` define the subgroup candidates.

## References

* [Cosme and Portugal, 2007][CosmePortugal2007]
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

open scoped commutatorElement

/-- The multiplicative presentation of the additive group `ZMod n`, giving a finite cyclic group
of order `n` for positive `n` and an infinite cyclic group for `n = 0`. -/
abbrev Cyc (n : ℕ) : Type := Multiplicative (ZMod n)

/-- The natural cardinality `Nat.card (Cyc n)` is `n`, with the value zero at `n = 0` following
the convention for infinite types. -/
@[simp]
theorem card_Cyc (n : ℕ) : Nat.card (Cyc n) = n := by
  rw [Cyc, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- The distinguished element of `Cyc n` corresponding to the residue class of one in the
additive group `ZMod n`. -/
def cycGen (n : ℕ) : Cyc n := Multiplicative.ofAdd 1

/-- The order of `cycGen n` is `n`, including the value zero for its infinite order when `n =
0`. -/
@[simp]
theorem orderOf_cycGen (n : ℕ) : orderOf (cycGen n) = n := by
  simp only [cycGen, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- The semidirect product `Cyc (p ^ r) ⋊[φ] Cyc (p ^ 2)` for the specified action `φ`. -/
abbrev SDG (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : Type :=
  Cyc (p ^ r) ⋊[φ] Cyc (p ^ 2)

/-- The image of `cycGen (p ^ r)` under the left-factor embedding into `SDG p r φ`. -/
def xGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : SDG p r φ :=
  SemidirectProduct.inl (cycGen (p ^ r))

/-- The image of `cycGen (p ^ 2)` under the right-factor embedding into `SDG p r φ`. -/
def yGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : SDG p r φ :=
  SemidirectProduct.inr (cycGen (p ^ 2))

/-- The distinguished left generator `xGen p r φ` has order `p ^ r`. -/
@[simp]
theorem orderOf_xGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    orderOf (xGen p r φ) = p ^ r := by
  rw [xGen, orderOf_injective (SemidirectProduct.inl : Cyc (p ^ r) →* SDG p r φ)
    SemidirectProduct.inl_injective, orderOf_cycGen]

/-- The distinguished right generator `yGen p r φ` has order `p ^ 2`. -/
@[simp]
theorem orderOf_yGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    orderOf (yGen p r φ) = p ^ 2 := by
  rw [yGen, orderOf_injective (SemidirectProduct.inr : Cyc (p ^ 2) →* SDG p r φ)
    SemidirectProduct.inr_injective, orderOf_cycGen]

/-- The natural cardinality of `SDG p r φ` is the product `p ^ r * p ^ 2`. -/
theorem card_SDG (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Nat.card (SDG p r φ) = p ^ r * p ^ 2 := by
  rw [SDG, SemidirectProduct.card, card_Cyc, card_Cyc]

/-- For prime `p`, the natural cardinality of `SDG p r φ` is `p ^ (r + 2)` [CosmePortugal2007]. -/
theorem card_SDG_prime_pow (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Nat.card (SDG p r φ) = p ^ (r + 2) := by
  rw [card_SDG, ← pow_add]

/-- For prime `p`, the semidirect product `SDG p r φ` is a `p`-group for every action `φ`. -/
theorem isPGroup_SDG (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : IsPGroup p (SDG p r φ) :=
  IsPGroup.of_card (card_SDG_prime_pow p r hp φ)

/-- The class (1) action condition that `φ (cycGen (p ^ 2))` sends `cycGen (p ^ r)` to its `(p ^
(r - 2) + 1)`st power. -/
def ClassOne (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : Prop :=
  φ (cycGen (p ^ 2)) (cycGen (p ^ r)) = cycGen (p ^ r) ^ (p ^ (r - 2) + 1)

/-- The class (2) action condition that `φ (cycGen (p ^ 2))` sends `cycGen (p ^ r)` to its `(p ^
(r - 1) + 1)`st power. -/
def ClassTwo (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : Prop :=
  φ (cycGen (p ^ 2)) (cycGen (p ^ r)) = cycGen (p ^ r) ^ (p ^ (r - 1) + 1)

/-- The cyclic subgroup generated by `xGen p r φ ^ p ^ i`. -/
def form1a (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.zpowers (xGen p r φ ^ p ^ i)

/-- The cyclic subgroup generated by `xGen p r φ ^ (t * p ^ i) * yGen p r φ ^ p ^ j`. -/
def form1b (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i j t : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.zpowers (xGen p r φ ^ (t * p ^ i) * yGen p r φ ^ p ^ j)

/-- The subgroup generated by the two elements `xGen p r φ ^ p ^ i` and `yGen p r φ ^ p ^ j`. -/
def form2 (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i j : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.closure {xGen p r φ ^ p ^ i, yGen p r φ ^ p ^ j}

/-- The subgroup generated by `xGen p r φ ^ (t * p ^ i) * yGen p r φ` and `xGen p r φ ^ p ^ (i +
1)`. -/
def form3 (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i t : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.closure {xGen p r φ ^ (t * p ^ i) * yGen p r φ, xGen p r φ ^ p ^ (i + 1)}

end Qatlib.Papers.SemidirectHSP07.MainResults
