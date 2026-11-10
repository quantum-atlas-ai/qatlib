/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.BasisGenerators
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

def dlogReduction {p : ℕ} (ζ a : (ZMod p)ˣ)
    (g : ZMod (p - 1) × ZMod (p - 1)) : (ZMod p)ˣ :=
  ζ ^ g.1.val * a ^ g.2.val

theorem dlog_exponent_exists {p : ℕ} (_hp : p.Prime) (ζ : (ZMod p)ˣ)
    (hζ : Subgroup.zpowers ζ = ⊤) (a : (ZMod p)ˣ) :
    ∃ r : ℕ, ζ ^ r = a := by
  classical
  haveI : Fact p.Prime := ⟨_hp⟩
  haveI : NeZero p := inferInstance
  have hmem : a ∈ Submonoid.powers ζ := by
    rw [mem_powers_iff_mem_zpowers]
    rw [hζ]
    exact Subgroup.mem_top a
  exact (Submonoid.mem_powers_iff a ζ).mp hmem

theorem orderOf_generator {p : ℕ} (hp : p.Prime) (ζ : (ZMod p)ˣ)
    (hζ : Subgroup.zpowers ζ = ⊤) : orderOf ζ = p - 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := inferInstance
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card]
  rw [orderOf_eq_card_of_forall_mem_zpowers (fun x => by
    rw [hζ]
    exact Subgroup.mem_top x), hcard]

theorem theorem12_exponent_bound {p : ℕ} (hp : p.Prime) (ζ : (ZMod p)ˣ)
    (hζ : Subgroup.zpowers ζ = ⊤) (a : (ZMod p)ˣ) :
    ∃ r : Fin (p - 1), ζ ^ (r : ℕ) = a := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := inferInstance
  have hord : orderOf ζ = p - 1 := orderOf_generator hp ζ hζ
  obtain ⟨n, hn⟩ := dlog_exponent_exists hp ζ hζ a
  refine ⟨⟨n % (p - 1), ?_⟩, ?_⟩
  · exact Nat.mod_lt _ (by have := hp.two_le; omega)
  · show ζ ^ (n % (p - 1)) = a
    rw [← hord, pow_mod_orderOf]
    exact hn

theorem theorem12_exponent_unique {p : ℕ} (hp : p.Prime) (ζ : (ZMod p)ˣ)
    (hζ : Subgroup.zpowers ζ = ⊤) (r s : Fin (p - 1))
    (h : ζ ^ (r : ℕ) = ζ ^ (s : ℕ)) : r = s := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := inferInstance
  haveI : Finite (ZMod p)ˣ := inferInstance
  have hord : orderOf ζ = p - 1 := orderOf_generator hp ζ hζ
  have hmod : (r : ℕ) % (p - 1) = (s : ℕ) % (p - 1) := by
    have := (pow_inj_mod (x := ζ) (n := (r : ℕ)) (m := (s : ℕ))).mp h
    rwa [hord] at this
  apply Fin.ext
  rw [← Nat.mod_eq_of_lt r.isLt, ← Nat.mod_eq_of_lt s.isLt]
  exact hmod

theorem canonical_logarithm_exists {p : ℕ} (hp : p.Prime) (ζ : (ZMod p)ˣ)
    (hζ : Subgroup.zpowers ζ = ⊤) :
    ∃ dlog : (ZMod p)ˣ → Fin (p - 1), ∀ a, ζ ^ (dlog a : ℕ) = a := by
  classical
  choose dlog hdlog using fun a => theorem12_exponent_bound hp ζ hζ a
  exact ⟨dlog, hdlog⟩

end Qatlib.Papers.ExactSimon97.MainResults
