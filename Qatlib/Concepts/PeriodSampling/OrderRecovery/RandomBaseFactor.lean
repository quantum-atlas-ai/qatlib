/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.OrderFactorConsumers
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.Index

/-!
# Random-base success in the factoring reduction

This module defines `randomBaseGood` and `randomBaseSuccess` for factor extraction using the
exact order of a uniformly chosen modular unit. For odd moduli, a base succeeds precisely when
its order is even and its half-order power is not minus one, as in [Shor1997].

Finite-group power-fiber bounds and the Chinese remainder decomposition control the number of
failing bases. The resulting lower bound depends on the number of distinct prime factors of the
modulus.

## Main statements

* `random_base_exact_order_factor_characterization`: the exact even-order and half-power
  criterion for success.
* `random_base_crt_success_bound`: success probability at least `1 - 2^{-(k - 1)}` for an odd
  modulus with `k ≥ 2` distinct prime factors.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.OrderRecovery
open scoped Classical

/-- A modular unit is good when factor extraction using its exact multiplicative order returns a
divisor. -/
noncomputable def randomBaseGood (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Prop :=
  (orderFactor N a (orderOf a)).isSome

/-- The fraction of modular units satisfying `randomBaseGood`, expressed as a real number. -/
noncomputable def randomBaseSuccess (N : ℕ) [NeZero N] : ℝ :=
  (Fintype.card ((ZMod N)ˣ) : ℝ)⁻¹ *
    ((Finset.univ.filter (fun a : (ZMod N)ˣ => randomBaseGood N a)).card : ℝ)

/-- For an odd modulus greater than one and a unit squaring to one, its residue predecessor is
coprime to the modulus exactly when the unit equals minus one. -/
private theorem root_predecessor_coprime_iff (N : ℕ) [NeZero N]
    (hN : 1 < N) (hodd : Odd N) (x : (ZMod N)ˣ)
    (hx : x ^ 2 = 1) :
    (x.val.val - 1).Coprime N ↔ (x : ZMod N) = -1 := by
  letI : Fact (1 < N) := ⟨hN⟩
  have ht : 1 ≤ x.val.val := by
    have h : x.val.val ≠ 0 := by rw [ZMod.val_ne_zero]; exact x.isUnit.ne_zero
    omega
  have hcast : ((x.val.val - 1 : ℕ) : ZMod N) = (x : ZMod N) - 1 := by
    rw [Nat.cast_sub ht, ZMod.natCast_zmod_val, Nat.cast_one]
  rw [← ZMod.isUnit_iff_coprime, hcast]
  constructor
  · intro hu
    have hsq : (x : ZMod N) ^ 2 = 1 := by exact congrArg Units.val hx
    have hp : ((x : ZMod N) - 1) * ((x : ZMod N) + 1) = 0 := by
      calc
        _ = (x : ZMod N) ^ 2 - 1 := by ring
        _ = 0 := by rw [hsq]; ring
    have hz := hu.mul_right_eq_zero.mp hp
    exact add_eq_zero_iff_eq_neg.mp hz
  · intro hxneg
    rw [hxneg]
    have hu : IsUnit (2 : ZMod N) :=
      (ZMod.isUnit_iff_coprime 2 N).mpr hodd.coprime_two_left
    convert! hu.neg using 1
    ring

/-- For an odd modulus greater than one, a base yields a factor from its exact order exactly
when that order is even and the half-order power is not minus one [Shor1997]. -/
theorem random_base_exact_order_factor_characterization :
    ∀ (N : ℕ) [NeZero N] (a : (ZMod N)ˣ), 1 < N → Odd N →
      (randomBaseGood N a ↔ Even (orderOf a) ∧
        ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1) := by
  intro N _ a hN hodd
  letI : Fact (1 < N) := ⟨hN⟩
  by_cases he : Even (orderOf a)
  · have hmod : orderOf a % 2 = 0 := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp he)
    have hr : 0 < orderOf a := orderOf_pos a
    have hhalf : 0 < orderOf a / 2 := by
      obtain ⟨k, hk⟩ := he
      omega
    have hlt : orderOf a / 2 < orderOf a := Nat.div_lt_self hr (by omega)
    have hne : (a ^ (orderOf a / 2) : (ZMod N)ˣ) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by omega) hlt
    have hsq : (a ^ (orderOf a / 2)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp he), pow_orderOf_eq_one]
    let t := ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val
    have ht : 1 ≤ t := by
      have h : ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N).val ≠ 0 := by
        rw [ZMod.val_ne_zero]
        exact (a ^ (orderOf a / 2)).isUnit.ne_zero
      omega
    have hcast : ((t - 1 : ℕ) : ZMod N) =
        ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) - 1 := by
      rw [Nat.cast_sub ht, ZMod.natCast_zmod_val, Nat.cast_one]
    have hnotdvd : ¬ N ∣ t - 1 := by
      intro hd
      have hz : ((t - 1 : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      rw [hcast, sub_eq_zero] at hz
      exact hne (Units.ext hz)
    have hdlt : Nat.gcd N (t - 1) < N := by
      have hle := Nat.gcd_le_left (t - 1) (by omega : 0 < N)
      have hneq : Nat.gcd N (t - 1) ≠ N := by
        intro heq
        exact hnotdvd (heq ▸ Nat.gcd_dvd_right N (t - 1))
      omega
    have hdpos : 0 < Nat.gcd N (t - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hcop := root_predecessor_coprime_iff N hN hodd (a ^ (orderOf a / 2)) hsq
    have hbig : 1 < Nat.gcd N (t - 1) ↔
        ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1 := by
      have hcop' : (t - 1).Coprime N ↔
          ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) = -1 := hcop
      calc
        1 < Nat.gcd N (t - 1) ↔ Nat.gcd N (t - 1) ≠ 1 := by omega
        _ ↔ ¬ (t - 1).Coprime N := by
          rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
        _ ↔ _ := not_congr hcop'
    simp only [randomBaseGood, orderFactor, hmod, ↓reduceIte,
      orderVerificationProduct_eq_pow]
    change (if 1 < Nat.gcd N (t - 1) ∧ Nat.gcd N (t - 1) < N ∧
      Nat.gcd N (t - 1) ∣ N then some (Nat.gcd N (t - 1)) else none).isSome ↔ _
    simp [hdlt, Nat.gcd_dvd_left, he, hbig]
  · have hmod : orderOf a % 2 ≠ 0 := by
      simpa [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] using! he
    simp [randomBaseGood, orderFactor, hmod, he]

/-- An element whose square is one is unchanged by every odd natural power. -/
private theorem involution_odd_power {G : Type*} [Monoid G] (z : G)
    (hz : z ^ 2 = 1) {m : ℕ} (hm : Odd m) : z ^ m = z := by
  obtain ⟨k, hk⟩ := hm
  rw [hk, pow_add, pow_mul, hz, one_pow, pow_one, one_mul]

/-- In a finite commutative group with a nonidentity involution `z`, there is a power taking
some element to `z` and sending every stated failure case to either one or `z`. -/
private theorem involution_failure_two_fibers {G : Type*} [CommGroup G] [Fintype G]
    (z : G) (hz : z ^ 2 = 1) (hne : z ≠ 1) :
    ∃ E : ℕ, (∃ b : G, b ^ E = z) ∧
      ∀ a : G, (Odd (orderOf a) ∨
        (Even (orderOf a) ∧ a ^ (orderOf a / 2) = z)) →
        a ^ E = 1 ∨ a ^ E = z := by
  let M := Fintype.card G
  let O := M / 2 ^ M.factorization 2
  have hM : M ≠ 0 := (Fintype.card_pos : 0 < Fintype.card G).ne'
  have hO : Odd O := Nat.not_even_iff_odd.mp
    (fun h => Nat.not_dvd_ordCompl Nat.prime_two hM h.two_dvd)
  have hex : ∃ j : ℕ, ¬ ∃ b : G, b ^ (2 ^ j * O) = z := by
    refine ⟨M.factorization 2, ?_⟩
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    rintro ⟨b, hb⟩
    exact hne (hb.symm.trans (pow_card_eq_one (x := b)))
  let j := Nat.find hex
  have hjnot : ¬ ∃ b : G, b ^ (2 ^ j * O) = z := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hj
    have hj0 : j = 0 := by omega
    apply hjnot
    refine ⟨z, ?_⟩
    simpa [hj0] using! involution_odd_power z hz hO
  have hjprev : ∃ b : G, b ^ (2 ^ (j - 1) * O) = z := by
    by_contra hh
    have hjle : j ≤ j - 1 := Nat.find_min' hex hh
    omega
  refine ⟨2 ^ (j - 1) * O, hjprev, ?_⟩
  intro a ha
  have hrM : orderOf a ∣ M := orderOf_dvd_card
  rcases ha with hodd | ⟨heven, hahalf⟩
  · left
    have hd : orderOf a ∣ O := Nat.dvd_ordCompl_of_dvd_not_dvd hrM hodd.not_two_dvd_nat
    exact orderOf_dvd_iff_pow_eq_one.mp (hd.trans (dvd_mul_left O _))
  · obtain ⟨s, d, hdodd, hrd⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
    have hspos : 0 < s := by
      by_contra hs
      have hs0 : s = 0 := by omega
      rw [hs0, pow_zero, one_mul] at hrd
      exact (Nat.not_even_iff_odd.mpr hdodd) (hrd ▸ heven)
    have hdO : d ∣ O := Nat.dvd_ordCompl_of_dvd_not_dvd
      ((dvd_mul_left d (2 ^ s)).trans (hrd ▸ hrM)) hdodd.not_two_dvd_nat
    have hhalf : orderOf a / 2 = 2 ^ (s - 1) * d := by
      have hs : s = (s - 1) + 1 := by omega
      have hr : orderOf a = 2 * (2 ^ (s - 1) * d) := by
        calc
          orderOf a = 2 ^ s * d := hrd
          _ = 2 ^ ((s - 1) + 1) * d := by rw [← hs]
          _ = 2 * (2 ^ (s - 1) * d) := by rw [pow_succ]; ring
      rw [hr]
      omega
    have hsj : s ≤ j := by
      by_contra hsj
      have hjs : j ≤ s - 1 := by omega
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hjs
      apply hjnot
      refine ⟨a ^ (2 ^ u * d), ?_⟩
      calc
        (a ^ (2 ^ u * d)) ^ (2 ^ j * O) =
            (a ^ (orderOf a / 2)) ^ O := by
          rw [← pow_mul, ← pow_mul, hhalf, hu, pow_add]
          congr 1
          ring
        _ = z := by rw [hahalf]; exact involution_odd_power z hz hO
    by_cases hsjlt : s < j
    · left
      have hp : 2 ^ s ∣ 2 ^ (j - 1) := pow_dvd_pow 2 (by omega)
      have hrE : orderOf a ∣ 2 ^ (j - 1) * O := by
        rw [hrd]
        exact Nat.mul_dvd_mul hp hdO
      exact orderOf_dvd_iff_pow_eq_one.mp hrE
    · right
      have hseq : s = j := by omega
      obtain ⟨c, hc⟩ := hdO
      have hcodd : Odd c := Nat.Odd.of_mul_right (hc ▸ hO)
      calc
        a ^ (2 ^ (j - 1) * O) = (a ^ (orderOf a / 2)) ^ c := by
          rw [← pow_mul, hhalf, hseq, hc]
          congr 1
          ring
        _ = z := by rw [hahalf]; exact involution_odd_power z hz hcodd

/-- If a nonidentity element is an `E`th power in a finite commutative group, each fiber of the
`E`th-power map has at most half the group cardinality. -/
private theorem power_fiber_double_le_card {G : Type*} [CommGroup G] [Fintype G]
    (E : ℕ) (z : G) (hne : z ≠ 1) (hroot : ∃ b : G, b ^ E = z) (y : G) :
    2 * (Finset.univ.filter (fun a : G => a ^ E = y)).card ≤ Fintype.card G := by
  let f : G →* G := powMonoidHom E
  have hzmem : z ∈ f.range := hroot
  letI : Nontrivial f.range := ⟨⟨⟨z, hzmem⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hrange : 2 ≤ Nat.card f.range := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hcount : (Finset.univ.filter (fun a : G => a ^ E = 1)).card =
      Nat.card f.ker := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, MonoidHom.mem_ker,
      powMonoidHom_apply, f]
  have hfiber : (Finset.univ.filter (fun a : G => a ^ E = y)).card ≤
      Nat.card f.ker := by
    by_cases hy : ∃ a : G, a ^ E = y
    · have heq := MonoidHom.card_fiber_eq_of_mem_range f hy
        (show (1 : G) ∈ Set.range f from ⟨1, by simp [f]⟩)
      simpa only [f, powMonoidHom_apply, hcount] using! heq.le
    · have hempty : (Finset.univ.filter (fun a : G => a ^ E = y)) = ∅ := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun h => hy ⟨a, h⟩
      simp [hempty]
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, Nat.card_eq_fintype_card (α := G)] at hcard
  nlinarith

set_option backward.isDefEq.respectTransparency false in

/-- In a finite product of commutative groups, an `E`th-power fiber has cardinality at most the
group cardinality divided by `2` to the number of coordinates, under the coordinatewise
nonidentity-root hypotheses. -/
private theorem power_pi_fiber_bound {ι : Type*} [Fintype ι]
    {G : ι → Type*} [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    (E : ℕ) (z : ∀ i, G i) (hne : ∀ i, z i ≠ 1)
    (hroot : ∃ b : ∀ i, G i, b ^ E = z) (y : ∀ i, G i) :
    2 ^ Fintype.card ι *
      Nat.card {a : ∀ i, G i // a ^ E = y} ≤
      Nat.card (∀ i, G i) := by
  have hcount : (Finset.univ.filter (fun a : ∀ i, G i => a ^ E = y)).card =
      ∏ i, (Finset.univ.filter (fun a : G i => a ^ E = y i)).card := by
    let e : {a : ∀ i, G i // a ^ E = y} ≃
        (∀ i, {a : G i // a ^ E = y i}) :=
      (Equiv.subtypeEquivRight (q := fun (a : ∀ i, G i) => ∀ i, a i ^ E = y i)
        (fun a => ⟨fun h i => congrFun h i, fun h => funext h⟩)).trans
        (Equiv.subtypePiEquivPi (p := fun i (a : G i) => a ^ E = y i))
    have hc := Fintype.card_congr e
    simpa only [Fintype.card_subtype, Fintype.card_pi] using! hc
  obtain ⟨b, hb⟩ := hroot
  have hlocal : ∀ i, 2 * (Finset.univ.filter (fun a : G i => a ^ E = y i)).card ≤
      Fintype.card (G i) := by
    intro i
    exact power_fiber_double_le_card E (z i) (hne i)
      ⟨b i, congrFun hb i⟩ (y i)
  have hp := Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Nat.zero_le (2 * (Finset.univ.filter (fun a : G i => a ^ E = y i)).card))
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hlocal i)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← hcount, ← Fintype.card_pi] using! hp

/-- For an odd nonzero modulus, the full power of each prime factor appearing in its
factorization exceeds two. -/
private theorem odd_prime_power_gt_two (N : ℕ) [NeZero N] (hodd : Odd N)
    (p : N.primeFactors) : 2 < (p : ℕ) ^ N.factorization p := by
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hpd := Nat.dvd_of_mem_primeFactors p.property
  have hpne : (p : ℕ) ≠ 2 := by
    intro h
    exact hodd.not_two_dvd_nat (h ▸ hpd)
  have he : 0 < N.factorization p :=
    hp.factorization_pos_of_dvd (NeZero.ne N) hpd
  calc
    2 < (p : ℕ) := by have := hp.two_le; omega
    _ = (p : ℕ) ^ 1 := (pow_one _).symm
    _ ≤ (p : ℕ) ^ N.factorization p := Nat.pow_le_pow_right hp.pos he

set_option backward.isDefEq.respectTransparency false in

/-- For an odd modulus where minus one is an `E`th power, each modular-unit power fiber has size
at most the unit-group cardinality divided by `2` to the number of distinct prime factors. -/
private theorem random_base_power_fiber_bound (N : ℕ) [NeZero N] (hodd : Odd N)
    (E : ℕ) (hroot : ∃ b : (ZMod N)ˣ, b ^ E = -1) (y : (ZMod N)ˣ) :
    2 ^ N.primeFactors.card *
      (Finset.univ.filter (fun a : (ZMod N)ˣ => a ^ E = y)).card ≤
      Fintype.card ((ZMod N)ˣ) := by
  letI : ∀ p : N.primeFactors, NeZero ((p : ℕ) ^ N.factorization p) :=
    fun p => ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  let e : (ZMod N)ˣ ≃* (∀ p : N.primeFactors, (ZMod ((p : ℕ) ^ N.factorization p))ˣ) :=
    (Units.mapEquiv (ZMod.equivPi N (NeZero.ne N)).toMulEquiv).trans MulEquiv.piUnits
  have hez : ∀ p : N.primeFactors, e (-1) p = -1 := by
    intro p
    apply Units.ext
    change (ZMod.equivPi N (NeZero.ne N)) (-1) p = -1
    simp
  have hne : ∀ p : N.primeFactors, e (-1) p ≠ 1 := by
    intro p
    letI : Fact (2 < (p : ℕ) ^ N.factorization p) := ⟨odd_prime_power_gt_two N hodd p⟩
    rw [hez p]
    intro h
    exact ZMod.neg_one_ne_one (congrArg Units.val h)
  let efiber : {a : (ZMod N)ˣ // a ^ E = y} ≃
      {a : ∀ p : N.primeFactors, (ZMod ((p : ℕ) ^ N.factorization p))ˣ //
        a ^ E = e y} :=
    e.toEquiv.subtypeEquiv (fun a => by
      change a ^ E = y ↔ (e a) ^ E = e y
      rw [← map_pow e]
      exact e.injective.eq_iff.symm)
  obtain ⟨b, hb⟩ := hroot
  have h := power_pi_fiber_bound
    (G := fun p : N.primeFactors => (ZMod ((p : ℕ) ^ N.factorization p))ˣ)
    E (e (-1)) hne
    ⟨e b, by rw [← map_pow, hb]⟩ (e y)
  rw [Fintype.card_coe, ← Nat.card_congr efiber, ← Nat.card_congr e.toEquiv] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using! h

/-- For an odd modulus greater than one with at least two distinct prime factors, exact-order
factor extraction succeeds on a uniformly chosen unit with probability at least `1 - 2^{-(k
- 1)}`, where `k` counts those factors [Shor1997]. -/
theorem random_base_crt_success_bound :
    ∀ (N : ℕ) [NeZero N], 1 < N → Odd N →
      2 ≤ N.primeFactors.card →
      1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ randomBaseSuccess N := by
  intro N _ hN hodd hk
  letI : Fact (2 < N) := ⟨by obtain ⟨k, hk⟩ := hodd; omega⟩
  have hz : (-1 : (ZMod N)ˣ) ^ 2 = 1 := by apply Units.ext; simp
  have hne : (-1 : (ZMod N)ˣ) ≠ 1 := by
    intro h
    exact ZMod.neg_one_ne_one (congrArg Units.val h)
  obtain ⟨E, hroot, hfailure⟩ := involution_failure_two_fibers (-1 : (ZMod N)ˣ) hz hne
  let bad := Finset.univ.filter (fun a : (ZMod N)ˣ => ¬ randomBaseGood N a)
  let f1 := Finset.univ.filter (fun a : (ZMod N)ˣ => a ^ E = 1)
  let fneg := Finset.univ.filter (fun a : (ZMod N)ˣ => a ^ E = -1)
  have hbad : bad ⊆ f1 ∪ fneg := by
    intro a ha
    have hnot : ¬ randomBaseGood N a := (Finset.mem_filter.mp ha).2
    have hcases : Odd (orderOf a) ∨
        (Even (orderOf a) ∧ a ^ (orderOf a / 2) = (-1 : (ZMod N)ˣ)) := by
      by_cases he : Even (orderOf a)
      · right
        refine ⟨he, Units.ext ?_⟩
        have hchar := random_base_exact_order_factor_characterization N a hN hodd
        have hn : ¬ (Even (orderOf a) ∧
            ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1) :=
          fun h => hnot (hchar.mpr h)
        simpa only [Units.val_neg, Units.val_one] using!
          (not_ne_iff.mp (fun h => hn ⟨he, h⟩))
      · exact Or.inl (Nat.not_even_iff_odd.mp he)
    simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      f1, fneg] using! hfailure a hcases
  have hcount : bad.card ≤ f1.card + fneg.card :=
    (Finset.card_le_card hbad).trans (Finset.card_union_le _ _)
  have h1 := random_base_power_fiber_bound N hodd E hroot 1
  have hneg := random_base_power_fiber_bound N hodd E hroot (-1)
  have hbadcount : 2 ^ N.primeFactors.card * bad.card ≤
      2 * Fintype.card ((ZMod N)ˣ) := by
    have hm := Nat.mul_le_mul_left (2 ^ N.primeFactors.card) hcount
    change 2 ^ N.primeFactors.card * f1.card ≤ Fintype.card ((ZMod N)ˣ) at h1
    change 2 ^ N.primeFactors.card * fneg.card ≤ Fintype.card ((ZMod N)ˣ) at hneg
    nlinarith
  let good := Finset.univ.filter (fun a : (ZMod N)ˣ => randomBaseGood N a)
  have hpartition : good.card + bad.card = Fintype.card ((ZMod N)ˣ) := by
    exact Finset.card_filter_add_card_filter_not _
  have hbc : (2 : ℝ) ^ N.primeFactors.card * (bad.card : ℝ) ≤
      2 * (Fintype.card ((ZMod N)ˣ) : ℝ) := by exact_mod_cast hbadcount
  have hpc : (good.card : ℝ) + (bad.card : ℝ) =
      (Fintype.card ((ZMod N)ˣ) : ℝ) := by exact_mod_cast hpartition
  have hpow : 0 < (2 : ℝ) ^ N.primeFactors.card := by positivity
  have hcard : 0 < (Fintype.card ((ZMod N)ˣ) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hscale : (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) *
      (2 : ℝ) ^ N.primeFactors.card = 2 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    convert! zpow_one (2 : ℝ) using 1
    congr 1
    omega
  change 1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤
    (Fintype.card ((ZMod N)ˣ) : ℝ)⁻¹ * (good.card : ℝ)
  rw [← div_eq_inv_mul, le_div_iff₀ hcard]
  apply (mul_le_mul_iff_left₀ hpow).mp
  have hscale' := congrArg (fun x : ℝ => x * (Fintype.card ((ZMod N)ˣ) : ℝ)) hscale
  nlinarith

end Qatlib.Concepts.PeriodSampling.OrderRecovery
