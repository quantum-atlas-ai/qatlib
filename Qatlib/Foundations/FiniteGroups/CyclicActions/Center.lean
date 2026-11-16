/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section


/-! # Coprime derived-order centrality

Inside a normal abelian subgroup, a commutator has order dividing the order
of the original element and the cardinal of the derived subgroup. Coprimality
therefore makes the original element central. No algorithmic bound is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace Qatlib.Foundations.FiniteGroups.CyclicActions.Center

/-- An element of a normal abelian subgroup with coprime derived order is central. -/
theorem centralOfCopr {G : Type*} [Group G] (A : Subgroup G) (hN : A.Normal)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {a : G} (ha : a ∈ A)
    (hc : Nat.Coprime (orderOf a) (Nat.card (commutator G))) (g : G) :
    a * g = g * a := by
  have hga : g * a * g⁻¹ ∈ A := hN.conj_mem a ha g
  have hcomm : Commute (g * a * g⁻¹) a⁻¹ := hA _ hga _ (A.inv_mem ha)
  have hpow : (g * a * g⁻¹) ^ orderOf a = 1 := by
    rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hpowinv : (a⁻¹) ^ orderOf a = 1 := by
    rw [inv_pow, pow_orderOf_eq_one, inv_one]
  have hdiv : orderOf ⁅g, a⁆ ∣ orderOf a := by
    rw [orderOf_dvd_iff_pow_eq_one, commutatorElement_def, hcomm.mul_pow,
      hpow, hpowinv, mul_one]
  have hcg : ⁅g, a⁆ ∈ commutator G := by
    show ⁅g, a⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top a)
  have hdivg : orderOf ⁅g, a⁆ ∣ Nat.card (commutator G) :=
    Subgroup.orderOf_dvd_natCard _ hcg
  have hcop : Nat.Coprime (orderOf ⁅g, a⁆) (Nat.card (commutator G)) :=
    Nat.Coprime.of_dvd_left hdiv hc
  have hone : orderOf ⁅g, a⁆ = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdivg
  have he : ⁅g, a⁆ = 1 := orderOf_eq_one_iff.mp hone
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

end Qatlib.Foundations.FiniteGroups.CyclicActions.Center
