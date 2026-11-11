/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

set_option backward.isDefEq.respectTransparency false

/-!
# Normality of the Abelian factor in a semidirect product

Paper: Morales, arXiv:2608.05321v1, Lemma 16.

For `G = A ⋊[φ] C` with `A` Abelian and a subgroup `A₁ ≤ A`, the subgroup
`H₁ = A₁ × {0}` is normal in `G` exactly when every automorphism `φ c`
preserves `A₁`.  For cyclic `C` this is the paper's condition
`φ(A₁) = A₁` for the generator of the action.
-/

set_option autoImplicit false

namespace Qatlib.Papers.SemidirectHSP26.MainResults.SemidirectNormal

open SemidirectProduct

variable {A C : Type*} [CommGroup A] [Group C]

/-- Lemma 16: the subgroup `A₁ × {0}` is normal in the semidirect product
exactly when the action of every element of `C` preserves `A₁`. -/
theorem normal_map_inl_iff_invariant (φ : C →* MulAut A) (A₁ : Subgroup A) :
    (A₁.map (SemidirectProduct.inl : A →* A ⋊[φ] C)).Normal ↔
      ∀ (c : C) (a : A), a ∈ A₁ → φ c a ∈ A₁ := by
  constructor
  · intro h c a ha
    have hconj : SemidirectProduct.inl (φ c a) ∈
        A₁.map (SemidirectProduct.inl : A →* A ⋊[φ] C) := by
      rw [SemidirectProduct.inl_aut]
      have hmem := h.conj_mem (SemidirectProduct.inl a) (Subgroup.mem_map_of_mem _ ha)
        (SemidirectProduct.inr c)
      simpa [map_inv] using hmem
    exact (Subgroup.mem_map_iff_mem SemidirectProduct.inl_injective).mp hconj
  · intro h
    refine ⟨?_⟩
    intro n hn g
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
    rcases g with ⟨b, c⟩
    rw [SemidirectProduct.mk_eq_inl_mul_inr c b]
    have hφa : φ c a ∈ A₁ := h c a ha
    have hconj :
        ((SemidirectProduct.inl b * SemidirectProduct.inr c) *
          SemidirectProduct.inl a *
          (SemidirectProduct.inl b * SemidirectProduct.inr c)⁻¹ : A ⋊[φ] C) =
        (SemidirectProduct.inl (φ c a) : A ⋊[φ] C) := by
      calc
        (SemidirectProduct.inl b * SemidirectProduct.inr c) *
            SemidirectProduct.inl a *
            (SemidirectProduct.inl b * SemidirectProduct.inr c)⁻¹
            = SemidirectProduct.inl b *
                (SemidirectProduct.inr c * SemidirectProduct.inl a *
                  (SemidirectProduct.inr c)⁻¹) * (SemidirectProduct.inl b)⁻¹ := by
              group
        _ = SemidirectProduct.inl b * SemidirectProduct.inl (φ c a) *
              (SemidirectProduct.inl b)⁻¹ := by
              rw [SemidirectProduct.inl_aut]
              simp only [map_inv]
        _ = (SemidirectProduct.inl : A →* A ⋊[φ] C) (b * φ c a * b⁻¹) := by
              simp only [map_mul, map_inv]
        _ = SemidirectProduct.inl (φ c a) := by
              congr 1
              calc
                b * φ c a * b⁻¹ = φ c a * b * b⁻¹ := by
                  rw [mul_comm b (φ c a)]
                _ = φ c a := by simp
    rw [hconj]
    exact Subgroup.mem_map_of_mem _ hφa

end Qatlib.Papers.SemidirectHSP26.MainResults.SemidirectNormal
