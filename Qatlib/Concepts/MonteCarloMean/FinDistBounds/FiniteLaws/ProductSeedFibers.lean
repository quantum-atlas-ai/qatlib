/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.CenteredBinomialFibers
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.ProductSeedFibers
open scoped BigOperators

theorem cbd_secret_fiber_card (η n : ℕ) (k : Fin n → ℕ) :
    Fintype.card {y : Fin n → Finset (Fin (2 * η)) // ∀ i, (y i).card = k i}
      = ∏ i, Nat.choose (2 * η) (k i) := by
  classical
  have e : {y : Fin n → Finset (Fin (2 * η)) // ∀ i, (y i).card = k i}
      ≃ ∀ i, {S : Finset (Fin (2 * η)) // S.card = k i} :=
    ⟨fun y i => ⟨y.1 i, y.2 i⟩, fun g => ⟨fun i => (g i).1, fun i => (g i).2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card, Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

theorem cbd_seed_space_card (η n : ℕ) :
    Fintype.card (Fin n → Finset (Fin (2 * η))) = 2 ^ (2 * η * n) := by
  have h := Nat.card_pi (α := Fin n) (β := fun _ => Finset (Fin (2 * η)))
  rw [Nat.card_eq_fintype_card] at h
  simp only [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ] at h
  rw [h]
  exact (Nat.pow_mul (2 : ℕ) (2 * η) n).symm

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.ProductSeedFibers
