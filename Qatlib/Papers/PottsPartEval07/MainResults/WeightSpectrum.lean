/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.WeightSpectrum

open scoped BigOperators

theorem proposition1_weight_count
    {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G]
    [MulAction G X]
    (hfree : ∀ (g : G), (∃ x : X, g • x = x) → g = 1)
    (w : X → ℕ) (hw : ∀ (g : G) (x : X), w (g • x) = w x) :
    (Finset.univ.image w).card * Fintype.card G ≤ Fintype.card X := by

  have hfib : ∀ v ∈ Finset.univ.image w,
      Fintype.card G ≤ (Finset.univ.filter (fun x => w x = v)).card := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨x, -, rfl⟩ := hv

    have hinj : Function.Injective (fun g : G => g • x) := by
      intro g h hgh
      have hgh' : g • x = h • x := hgh
      have h1 : (h⁻¹ * g) • x = x := by
        rw [mul_smul, hgh']
        exact inv_smul_smul h x
      have h2 : h⁻¹ * g = 1 := hfree (h⁻¹ * g) ⟨x, h1⟩
      calc g = h * (h⁻¹ * g) := by group
        _ = h * 1 := by rw [h2]
        _ = h := mul_one h

    have hsubset : (Finset.univ.image (fun g : G => g • x)) ⊆
        Finset.univ.filter (fun y => w y = w x) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hy
      exact hw g x
    calc Fintype.card G = (Finset.univ.image (fun g : G => g • x)).card := by
          rw [Finset.card_image_of_injective _ hinj]
          simp
      _ ≤ (Finset.univ.filter (fun y => w y = w x)).card := Finset.card_le_card hsubset

  have hsum : Fintype.card X =
      ∑ v ∈ Finset.univ.image w, (Finset.univ.filter (fun x => w x = v)).card := by
    have := Finset.card_eq_sum_card_image w (Finset.univ : Finset X)
    simpa using this
  calc (Finset.univ.image w).card * Fintype.card G
      = ∑ v ∈ Finset.univ.image w, Fintype.card G := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ ∑ v ∈ Finset.univ.image w,
          (Finset.univ.filter (fun x => w x = v)).card :=
        Finset.sum_le_sum hfib
    _ = Fintype.card X := by rw [← hsum]

theorem proposition1_irreducible_cyclic_code
    {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G]
    [MulAction G X]
    (hfree : ∀ (g : G), (∃ x : X, g • x = x) → g = 1)
    (w : X → ℕ) (hw : ∀ (g : G) (x : X), w (g • x) = w x)
    (q k n N : ℕ) (hn : 0 < n)
    (hcard : Fintype.card X = q ^ k - 1)
    (hG : Fintype.card G = n)
    (hN : q ^ k - 1 = n * N) :
    (Finset.univ.image w).card ≤ N := by
  have h := proposition1_weight_count hfree w hw
  rw [hG, hcard, hN] at h

  have h' : n * (Finset.univ.image w).card ≤ n * N := by
    rwa [Nat.mul_comm (Finset.univ.image w).card n] at h
  exact Nat.le_of_mul_le_mul_left h' hn

end Qatlib.Papers.PottsPartEval07.MainResults.WeightSpectrum
