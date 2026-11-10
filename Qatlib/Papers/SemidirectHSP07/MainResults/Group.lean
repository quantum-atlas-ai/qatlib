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

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

open scoped commutatorElement

abbrev Cyc (n : ℕ) : Type := Multiplicative (ZMod n)

@[simp]
theorem card_Cyc (n : ℕ) : Nat.card (Cyc n) = n := by
  rw [Cyc, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

def cycGen (n : ℕ) : Cyc n := Multiplicative.ofAdd 1

@[simp]
theorem orderOf_cycGen (n : ℕ) : orderOf (cycGen n) = n := by
  simp only [cycGen, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

abbrev SDG (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : Type :=
  Cyc (p ^ r) ⋊[φ] Cyc (p ^ 2)

def xGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : SDG p r φ :=
  SemidirectProduct.inl (cycGen (p ^ r))

def yGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : SDG p r φ :=
  SemidirectProduct.inr (cycGen (p ^ 2))

@[simp]
theorem orderOf_xGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    orderOf (xGen p r φ) = p ^ r := by
  rw [xGen, orderOf_injective (SemidirectProduct.inl : Cyc (p ^ r) →* SDG p r φ)
    SemidirectProduct.inl_injective, orderOf_cycGen]

@[simp]
theorem orderOf_yGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    orderOf (yGen p r φ) = p ^ 2 := by
  rw [yGen, orderOf_injective (SemidirectProduct.inr : Cyc (p ^ 2) →* SDG p r φ)
    SemidirectProduct.inr_injective, orderOf_cycGen]

theorem card_SDG (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Nat.card (SDG p r φ) = p ^ r * p ^ 2 := by
  rw [SDG, SemidirectProduct.card, card_Cyc, card_Cyc]

theorem card_SDG_prime_pow (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Nat.card (SDG p r φ) = p ^ (r + 2) := by
  rw [card_SDG, ← pow_add]

theorem isPGroup_SDG (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : IsPGroup p (SDG p r φ) :=
  IsPGroup.of_card (card_SDG_prime_pow p r hp φ)

def ClassOne (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : Prop :=
  φ (cycGen (p ^ 2)) (cycGen (p ^ r)) = cycGen (p ^ r) ^ (p ^ (r - 2) + 1)

def ClassTwo (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) : Prop :=
  φ (cycGen (p ^ 2)) (cycGen (p ^ r)) = cycGen (p ^ r) ^ (p ^ (r - 1) + 1)

def form1a (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.zpowers (xGen p r φ ^ p ^ i)

def form1b (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i j t : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.zpowers (xGen p r φ ^ (t * p ^ i) * yGen p r φ ^ p ^ j)

def form2 (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i j : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.closure {xGen p r φ ^ p ^ i, yGen p r φ ^ p ^ j}

def form3 (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (i t : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.closure {xGen p r φ ^ (t * p ^ i) * yGen p r φ, xGen p r φ ^ p ^ (i + 1)}

end Qatlib.Papers.SemidirectHSP07.MainResults
