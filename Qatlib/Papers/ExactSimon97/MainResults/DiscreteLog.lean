/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.BasisGenerators

/-!
# Canonical exponents for prime-field discrete logarithms

The map `dlogReduction` encodes two exponents in the unit group of a prime field. For a
generator of that group, the module proves existence and uniqueness of an exponent in `Fin (p -
1)` and the existence of a function selecting these canonical exponents. The development follows
[BrassardHoyer1997].

## Main statements

* `theorem12_exponent_bound`: represents each unit by an exponent less than `p - 1`.
* `theorem12_exponent_unique`: proves uniqueness in that exponent range.
* `canonical_logarithm_exists`: selects a canonical exponent for every unit.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

/-- The two-exponent map `(x, y) ↦ ζ ^ x.val * a ^ y.val` from `ZMod (p - 1) × ZMod (p - 1)` to
the unit group. -/
def dlogReduction {p : ℕ} (ζ a : (ZMod p)ˣ)
    (g : ZMod (p - 1) × ZMod (p - 1)) : (ZMod p)ˣ :=
  ζ ^ g.1.val * a ^ g.2.val

/-- If `ζ` generates the unit group of `ZMod p`, every unit is a nonnegative power of `ζ`. -/
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

/-- For prime `p`, a generator of the unit group of `ZMod p` has order `p - 1`. -/
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

/-- For prime `p`, every unit is a power of the given generator with exponent in `Fin (p - 1)`.
See [BrassardHoyer1997]. -/
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

/-- For prime `p`, two exponents in `Fin (p - 1)` giving the same power of a unit-group
generator are equal. See [BrassardHoyer1997]. -/
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

/-- For prime `p` and a unit-group generator `ζ`, there exists a function assigning to every
unit an exponent in `Fin (p - 1)` whose power of `ζ` is that unit. See [BrassardHoyer1997]. -/
theorem canonical_logarithm_exists {p : ℕ} (hp : p.Prime) (ζ : (ZMod p)ˣ)
    (hζ : Subgroup.zpowers ζ = ⊤) :
    ∃ dlog : (ZMod p)ˣ → Fin (p - 1), ∀ a, ζ ^ (dlog a : ℕ) = a := by
  classical
  choose dlog hdlog using fun a => theorem12_exponent_bound hp ζ hζ a
  exact ⟨dlog, hdlog⟩

end Qatlib.Papers.ExactSimon97.MainResults
