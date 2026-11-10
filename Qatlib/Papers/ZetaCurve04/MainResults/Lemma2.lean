/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Lemma2

theorem addOrderOf_dvd_card {G : Type*} [AddCommGroup G] [Fintype G] (x : G) :
    addOrderOf x ∣ Nat.card G := by
  rw [Nat.card_eq_fintype_card]
  exact _root_.addOrderOf_dvd_card

theorem addOrderOf_le_card {G : Type*} [AddCommGroup G] [Fintype G] (x : G) :
    addOrderOf x ≤ Nat.card G := by
  exact Nat.le_of_dvd (Nat.card_pos (α := G)) (addOrderOf_dvd_card x)

theorem card_closure_le_prod_order {G : Type*} [AddCommGroup G] [Fintype G]
    (T : Finset G) :
    Nat.card (↥(AddSubgroup.closure (T : Set G))) ≤ ∏ x ∈ T, addOrderOf x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp [AddSubgroup.closure_empty]
  | insert a T ha ih =>
      rw [Finset.prod_insert ha]
      have hset : ((insert a T : Finset G) : Set G) = ({a} : Set G) ∪ (T : Set G) := by
        ext x
        simp
      rw [hset, AddSubgroup.closure_union]
      calc Nat.card (↥(AddSubgroup.closure ({a} : Set G) ⊔
              AddSubgroup.closure (T : Set G)))
          ≤ Nat.card (↥(AddSubgroup.closure ({a} : Set G))) *
              Nat.card (↥(AddSubgroup.closure (T : Set G))) := by
            rw [← Nat.card_prod]
            refine Nat.card_le_card_of_surjective
              (fun p : ↥(AddSubgroup.closure ({a} : Set G)) ×
                       ↥(AddSubgroup.closure (T : Set G)) =>
                (⟨p.1.1 + p.2.1, ?_⟩ : ↥(AddSubgroup.closure ({a} : Set G) ⊔
                  AddSubgroup.closure (T : Set G)))) ?_
            · exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left p.1.2)
                (AddSubgroup.mem_sup_right p.2.2)
            · rintro ⟨x, hx⟩
              rw [AddSubgroup.mem_sup] at hx
              obtain ⟨y, hy, z, hz, hyz⟩ := hx
              exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), by
                simp only [Subtype.mk.injEq]
                exact hyz⟩
        _ = addOrderOf a * Nat.card (↥(AddSubgroup.closure (T : Set G))) := by
            rw [show Nat.card (↥(AddSubgroup.closure ({a} : Set G))) = addOrderOf a by
              rw [← AddSubgroup.zmultiples_eq_closure, Nat.card_zmultiples]]
        _ ≤ addOrderOf a * ∏ x ∈ T, addOrderOf x :=
            Nat.mul_le_mul_left _ ih

theorem card_le_prod_order_of_closure_top {G : Type*} [AddCommGroup G] [Fintype G]
    (T : Finset G) (hT : AddSubgroup.closure (T : Set G) = ⊤) :
    Nat.card G ≤ ∏ x ∈ T, addOrderOf x := by
  have h := card_closure_le_prod_order T
  rw [hT] at h
  simpa using h

end Qatlib.Papers.ZetaCurve04.MainResults.Lemma2
