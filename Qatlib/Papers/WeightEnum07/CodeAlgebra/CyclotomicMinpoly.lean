/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WeightEnum07.OrbitSieve.CosetSieve
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.WeightEnum07.CodeAlgebra

open Polynomial Finset

variable {N : ℕ} [NeZero N] {L : Type*} [Field L]

theorem mem_orbit_iff_npow {u : (ZMod N)ˣ} {s t : ZMod N} :
    t ∈ OrbitSieve.orbitFinset u s ↔ ∃ n : ℕ, ((u ^ n : (ZMod N)ˣ) : ZMod N) * s = t := by
  constructor
  · intro ht
    rw [OrbitSieve.mem_orbitFinset] at ht
    obtain ⟨j, -, h⟩ := ht
    exact ⟨j, h⟩
  · rintro ⟨n, rfl⟩
    exact OrbitSieve.pow_mul_mem u s n

theorem sum_leaders_card_mul_eq {u : (ZMod N)ˣ} (f : ZMod N → L)
    (hf : ∀ l ∈ OrbitSieve.leaders u, ∀ t ∈ OrbitSieve.orbitFinset u l, f t = f l) :
    ∑ l ∈ OrbitSieve.leaders u, (OrbitSieve.orbitFinset u l).card • f l =
      ∑ t : ZMod N, f t := by
  classical
  have hcover : (Finset.univ : Finset (ZMod N)) =
      (OrbitSieve.leaders u).biUnion (OrbitSieve.orbitFinset u) :=
    Finset.Subset.antisymm (OrbitSieve.univ_subset_biUnion u)
      (fun x _ => Finset.mem_univ x)
  rw [hcover, Finset.sum_biUnion (OrbitSieve.leaders_pairwiseDisjoint u)]
  refine Finset.sum_congr rfl ?_
  intro l hl
  rw [Finset.sum_congr rfl (fun t ht => hf l hl t ht), Finset.sum_const]

theorem prod_leaders_prod_orbit_eq {u : (ZMod N)ˣ} (f : ZMod N → Polynomial L) :
    ∏ l ∈ OrbitSieve.leaders u, ∏ t ∈ OrbitSieve.orbitFinset u l, f t = ∏ t : ZMod N, f t := by
  classical
  have hcover : (Finset.univ : Finset (ZMod N)) =
      (OrbitSieve.leaders u).biUnion (OrbitSieve.orbitFinset u) :=
    Finset.Subset.antisymm (OrbitSieve.univ_subset_biUnion u)
      (fun x _ => Finset.mem_univ x)
  rw [hcover]
  exact (Finset.prod_biUnion (OrbitSieve.leaders_pairwiseDisjoint u)).symm

theorem prod_univ_eq_X_pow_sub_one {ζ : L} (hζ : IsPrimitiveRoot ζ N) :
    ∏ t : ZMod N, (X - C (ζ ^ t.val)) = X ^ N - 1 := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos N) hζ]
  refine Finset.prod_bij (fun t _ => ζ ^ t.val) ?_ ?_ ?_ ?_
  · intro t _
    try dsimp only
    rw [Polynomial.mem_nthRootsFinset (NeZero.pos N), ← pow_mul, Nat.mul_comm,
      pow_mul, hζ.pow_eq_one, one_pow]
  · intro t _ u _ H
    exact ZMod.val_injective N (hζ.pow_inj t.val_lt u.val_lt H)
  · intro μ hμ
    rw [Polynomial.mem_nthRootsFinset (NeZero.pos N)] at hμ
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    exact ⟨(i : ZMod N), Finset.mem_univ _, by
      change ζ ^ (i : ZMod N).val = ζ ^ i
      rw [ZMod.val_natCast_of_lt hi]⟩
  · intro t _
    rfl

section FiniteField

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Finite L] [Algebra (ZMod p) L]
variable [DecidableEq L] {ζ : L}

omit [DecidableEq L] in

theorem frob_pow_apply (hζ : IsPrimitiveRoot ζ N) (hunit : IsUnit (p : ZMod N))
    (s : ZMod N) (i : ℕ) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L ^ i) (ζ ^ s.val) =
      ζ ^ (((hunit.unit ^ i : (ZMod N)ˣ) : ZMod N) * s).val := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp only [Fintype.card_eq_nat_card]
  rw [← pow_mul]
  apply pow_eq_pow_of_modEq (n := N) ?_ hζ.pow_eq_one
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [ZMod.natCast_zmod_val]
  push_cast
  have hcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcard]
  rw [ZMod.natCast_zmod_val]
  have hpu : ((hunit.unit : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := IsUnit.unit_spec hunit
  conv_lhs => rw [← hpu]
  ring

theorem carrier_eq_orbit (hζ : IsPrimitiveRoot ζ N)
    (hunit : IsUnit (p : ZMod N)) (s : ZMod N) :
    (ConjRootClass.mk (ZMod p) (ζ ^ s.val)).carrier =
      ((OrbitSieve.orbitFinset hunit.unit s).image (fun t => ζ ^ t.val) : Set L) := by
  classical
  ext x
  rw [ConjRootClass.mem_carrier, ConjRootClass.mk_eq_mk, isConjRoot_iff_exists_algEquiv]
  rw [Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨i, -, rfl⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) L).2 σ
    refine ⟨((hunit.unit ^ (i : ℕ) : (ZMod N)ˣ) : ZMod N) * s, ?_, ?_⟩
    · rw [mem_orbit_iff_npow]
      exact ⟨(i : ℕ), rfl⟩
    · rw [frob_pow_apply hζ hunit s (i : ℕ)]
  · rintro ⟨t, ht, rfl⟩
    rw [mem_orbit_iff_npow] at ht
    obtain ⟨i, rfl⟩ := ht
    exact ⟨FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L ^ i,
      frob_pow_apply hζ hunit s i⟩

theorem minpoly_map_eq_orbit_prod (hζ : IsPrimitiveRoot ζ N)
    (hunit : IsUnit (p : ZMod N)) (s : ZMod N) :
    (minpoly (ZMod p) (ζ ^ s.val)).map (algebraMap (ZMod p) L) =
      ∏ t ∈ OrbitSieve.orbitFinset hunit.unit s, (X - C (ζ ^ t.val)) := by
  classical
  let c : ConjRootClass (ZMod p) L := ConjRootClass.mk (ZMod p) (ζ ^ s.val)
  haveI : Fintype c.carrier := Fintype.ofFinite _
  have hprod := ConjRootClass.minpoly.map_eq_prod c
  have hmin : c.minpoly = minpoly (ZMod p) (ζ ^ s.val) := ConjRootClass.minpoly_mk (ζ ^ s.val)
  rw [hmin] at hprod
  have hset : c.carrier.toFinset =
      (OrbitSieve.orbitFinset hunit.unit s).image (fun t => ζ ^ t.val) := by
    ext x
    rw [Set.mem_toFinset]
    change x ∈ (ConjRootClass.mk (ZMod p) (ζ ^ s.val)).carrier ↔
      x ∈ (OrbitSieve.orbitFinset hunit.unit s).image (fun t => ζ ^ t.val)
    rw [carrier_eq_orbit hζ hunit s, Finset.mem_coe]
  rw [hprod, hset, Finset.prod_image]
  intro a _ b _ hab
  apply ZMod.val_injective N
  exact hζ.pow_inj a.val_lt b.val_lt hab

theorem corollary3_cyclotomic_factorization (hζ : IsPrimitiveRoot ζ N)
    (hunit : IsUnit (p : ZMod N)) :
    ∏ l ∈ OrbitSieve.leaders hunit.unit,
        (minpoly (ZMod p) (ζ ^ l.val)).map (algebraMap (ZMod p) L) = X ^ N - 1 := by
  classical
  have h : ∏ l ∈ OrbitSieve.leaders hunit.unit,
        (minpoly (ZMod p) (ζ ^ l.val)).map (algebraMap (ZMod p) L) =
      ∏ l ∈ OrbitSieve.leaders hunit.unit,
        ∏ t ∈ OrbitSieve.orbitFinset hunit.unit l, (X - C (ζ ^ t.val)) := by
    refine Finset.prod_congr rfl ?_
    intro l _
    exact minpoly_map_eq_orbit_prod hζ hunit l
  rw [h, prod_leaders_prod_orbit_eq (u := hunit.unit)
    (f := fun t => (X - C (ζ ^ t.val))), prod_univ_eq_X_pow_sub_one hζ]

theorem coset_factor_dvd_X_pow_sub_one (hζ : IsPrimitiveRoot ζ N)
    (hunit : IsUnit (p : ZMod N)) {l : ZMod N} (hl : l ∈ OrbitSieve.leaders hunit.unit) :
    (minpoly (ZMod p) (ζ ^ l.val)).map (algebraMap (ZMod p) L) ∣ X ^ N - 1 := by
  rw [← corollary3_cyclotomic_factorization hζ hunit]
  exact Finset.dvd_prod_of_mem _ hl

theorem prod_subset_dvd_X_pow_sub_one (hζ : IsPrimitiveRoot ζ N)
    (hunit : IsUnit (p : ZMod N)) (T : Finset (ZMod N))
    (hT : T ⊆ OrbitSieve.leaders hunit.unit) :
    (∏ l ∈ T, (minpoly (ZMod p) (ζ ^ l.val)).map (algebraMap (ZMod p) L)) ∣ X ^ N - 1 := by
  classical
  have hsplit := Finset.prod_sdiff hT
    (f := fun l => (minpoly (ZMod p) (ζ ^ l.val)).map (algebraMap (ZMod p) L))
  rw [← corollary3_cyclotomic_factorization hζ hunit, ← hsplit]
  exact dvd_mul_left _ _

theorem card_nontrivial_subsets (t : ℕ) (ht : 0 < t) :
    ((Finset.univ : Finset (Fin t)).powerset.filter
        (fun T => T.Nonempty ∧ T ≠ Finset.univ)).card = 2 ^ t - 2 := by
  classical
  have hsub : ((Finset.univ : Finset (Fin t)).powerset.filter
        (fun T => T.Nonempty ∧ T ≠ Finset.univ)) =
      (Finset.univ : Finset (Fin t)).powerset \
        ({∅, Finset.univ} : Finset (Finset (Fin t))) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, hne, hne'⟩
      refine ⟨Finset.subset_univ _, ?_⟩
      rintro (h | h)
      · exact Finset.not_nonempty_empty (h ▸ hne)
      · exact hne' h
    · rintro ⟨-, h⟩
      refine ⟨Finset.subset_univ _, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]; intro h0; exact h (Or.inl h0)
      · intro h0; exact h (Or.inr h0)
  have hsub2 : ({∅, Finset.univ} : Finset (Finset (Fin t))) ⊆
      (Finset.univ : Finset (Fin t)).powerset := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl <;> simp
  have hne : (∅ : Finset (Fin t)) ≠ Finset.univ := by
    intro h
    have hc : (Finset.univ : Finset (Fin t)).card = 0 := by rw [← h]; simp
    rw [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hcard : ({∅, Finset.univ} : Finset (Finset (Fin t))).card = 2 :=
    Finset.card_pair hne
  have hinter : (({∅, Finset.univ} : Finset (Finset (Fin t))) ∩
      (Finset.univ : Finset (Fin t)).powerset) = {∅, Finset.univ} := by
    ext T
    simp only [Finset.mem_inter, Finset.mem_powerset]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · intro h
      exact ⟨h, Finset.subset_univ _⟩
  rw [hsub, Finset.card_sdiff, hinter, Finset.card_powerset, Finset.card_univ,
    Fintype.card_fin, hcard]

end FiniteField

end Qatlib.Papers.WeightEnum07.CodeAlgebra
