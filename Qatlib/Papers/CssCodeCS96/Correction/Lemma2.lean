/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CssCodeCS96.Correction.CharacterBasis
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The projected character sum in the zero-support case

Lemma 2 of the fixed source evaluates the matrix element of a coordinate projection between two
character states of a code. Its printed form is

`⟨χ w₁| P_E,e |χ w₂⟩ = (-1)^(e ⬝ (c + w₁ + w₂)) / 2 ^ wt(E)`

when some dual word `c` makes `c + w₁ + w₂` supported inside `E`, and zero otherwise. The proof
in the source uses the missing hypothesis `wt(e) < d(C₁^⊥)`; that hypothesis is what makes the
dual word unique, and it is the content of the projection module.

This module closes the case of an empty coordinate support, where the projection is the identity
and the cardinality condition reduces to `w₁ + w₂ ∈ C^⊥`. It does not prove the general statement;
the missing part is the count of the restricted character sum over the kernel of the coordinate
restriction.

## Main statements

* `exists_dual_iff_of_zero_support`: with no projected coordinates, the cardinality condition of
  Lemma 2 is exactly the dual-coset condition on `w₁ + w₂`.
* `projected_character_sum_of_zero_support`: Lemma 2 for an empty coordinate support, which is the
  orthonormality of the character states.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996], Lemma 2
-/

namespace Qatlib.Papers.CssCodeCS96.Correction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix
open scoped Classical

variable {n : ℕ}

/-- In the binary field, doubling a scalar gives zero. -/
theorem binary_add_self_scalar (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

/-- With an empty coordinate support the cardinality condition of Lemma 2 is exactly the
condition that `w₁ + w₂` lie in the classical dual: the support constraint forces the dual word to
be `w₁ + w₂` itself. -/
theorem exists_dual_iff_of_zero_support (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (w₁ w₂ : Fin n → ZMod 2) :
    (∃ c ∈ classicalDual C,
        ∀ i, (c + w₁ + w₂) i ≠ 0 → (0 : Fin n → ZMod 2) i ≠ 0) ↔
      w₁ + w₂ ∈ classicalDual C := by
  classical
  constructor
  · rintro ⟨c, hc, hsupp⟩
    have hzero : c + w₁ + w₂ = 0 := by
      funext i
      by_contra h
      exact absurd rfl (hsupp i h)
    have hzero' : c + (w₁ + w₂) = 0 := by
      rw [← hzero, add_assoc]
    have hc' : c = w₁ + w₂ := by
      have hone : c = c + (w₁ + w₂) + (w₁ + w₂) := by
        funext i
        show c i = (c + (w₁ + w₂) + (w₁ + w₂)) i
        rw [Pi.add_apply, Pi.add_apply]
        rw [add_assoc, binary_add_self_scalar, add_zero]
      calc c = c + (w₁ + w₂) + (w₁ + w₂) := hone
        _ = 0 + (w₁ + w₂) := by rw [hzero']
        _ = w₁ + w₂ := zero_add _
    rwa [hc'] at hc
  · intro h
    refine ⟨w₁ + w₂, h, fun i hne => ?_⟩
    have hzero : (w₁ + w₂ + w₁ + w₂ : Fin n → ZMod 2) = 0 := by
      funext i
      show (w₁ + w₂ + w₁ + w₂) i = (0 : Fin n → ZMod 2) i
      simp only [Pi.add_apply, Pi.zero_apply]
      rcases binary_eq_zero_or_one (w₁ i) with h1 | h1 <;>
        rcases binary_eq_zero_or_one (w₂ i) with h2 | h2 <;>
        rw [h1, h2] <;> decide
    rw [hzero] at hne
    exact hne

/-- Lemma 2 of the fixed source for an empty coordinate support: the projected matrix element is
the character-state inner product, which is one exactly when the labels sum into the classical
dual and zero otherwise. The phase factor of the source formula is trivial here because the
support is empty. -/
theorem projected_character_sum_of_zero_support (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (w₁ w₂ e : Fin n → ZMod 2) :
    ampInner (charState C w₁) (projectOn (0 : Fin n → ZMod 2) e *ᵥ charState C w₂) =
      if w₁ + w₂ ∈ classicalDual C then 1 else 0 := by
  rw [projectOn_zero, Matrix.one_mulVec]
  exact charState_inner C w₁ w₂

end Qatlib.Papers.CssCodeCS96.Correction
