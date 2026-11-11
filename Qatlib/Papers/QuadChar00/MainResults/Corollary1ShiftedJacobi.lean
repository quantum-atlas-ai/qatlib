/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs

/-!
# Uniqueness of the shift in a Jacobi character

This module proves that distinct shifts of the Jacobi character modulo an odd squarefree integer
greater than one give distinct functions. The argument detects equality of the shifts modulo
every prime divisor using the zero set of the character, then combines the congruences over the
squarefree modulus.

The theorem `corollary1_shiftedJacobi_solved` chooses a left inverse of the shift-to-function
map, giving a decoder from the complete shifted function to its shift. This is the functional
recovery statement associated with Corollary 1 of [VanDamHallgren2000].

## Main statements

* `jacobiCharZMod_eq_zero_iff_not_isUnit`: the Jacobi character vanishes exactly at nonunits.
* `shift_prime_congruent`: equal shifted functions have equal shifts modulo each prime divisor.
* `corollary1_shift_injective`: injectivity of the shift-to-function map.
* `corollary1_shiftedJacobi_solved`: existence of a decoder recovering every shift.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

/-- For nonzero modulus, the Jacobi character of a residue is zero exactly when the residue is
not a unit. This zero-set characterization supports the shift-recovery argument for
Corollary 1 of [VanDamHallgren2000]. -/
lemma jacobiCharZMod_eq_zero_iff_not_isUnit (n : ℕ) [NeZero n] (a : ZMod n) :
    jacobiCharZMod n a = 0 ↔ ¬ IsUnit a := by
  unfold jacobiCharZMod
  rw [jacobiSym.eq_zero_iff_not_coprime]
  have hunit : IsUnit a ↔ Nat.Coprime a.val n := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [ZMod.isUnit_iff_coprime]
  rw [hunit, Nat.coprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]

/-- Congruence modulo every member of a finite pairwise coprime family implies congruence modulo
their product. -/
lemma modEq_prod_of_forall {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j))
    {a b : ℕ} (h : ∀ i ∈ s, a ≡ b [MOD f i]) :
    a ≡ b [MOD ∏ i ∈ s, f i] := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Nat.modEq_one
  | insert i t hi ih =>
    rw [Finset.prod_insert hi]
    have hfi : a ≡ b [MOD f i] := h i (Finset.mem_insert_self _ _)
    have ht : ∀ j ∈ t, a ≡ b [MOD f j] := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hcop_it : (f i).Coprime (∏ j ∈ t, f j) := by
      rw [Nat.coprime_prod_right_iff]
      intro j hj
      exact hcop i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    have hcopt : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → (f j).Coprime (f k) :=
      fun j hj k hk hjk =>
        hcop j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    have hprod := ih hcopt ht
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_it).mp ⟨hfi, hprod⟩

/-- For an odd squarefree modulus greater than one, pointwise equality of two shifted Jacobi
characters forces the shifts to be congruent modulo every prime divisor. This is the
prime-modulus step in the Corollary 1 recovery argument of [VanDamHallgren2000]. -/
lemma shift_prime_congruent {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (h1 : 1 < n) {s t : ZMod n}
    (hst : ∀ x : ZMod n, jacobiCharZMod n (x + s) = jacobiCharZMod n (x + t))
    {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ n) : s.val ≡ t.val [MOD p] := by
  have hnpos : 0 < n := hn.pos
  by_contra hne
  have hne' : s.val % p ≠ t.val % p := hne
  set m := n / p with hm
  have hmul : p * m = n := Nat.mul_div_cancel' hpdvd
  have hm_ne0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    omega
  have hp_ne0 : p ≠ 0 := hp.ne_zero
  haveI : NeZero m := ⟨hm_ne0⟩
  haveI : NeZero p := ⟨hp_ne0⟩
  have hpsq : ¬ p * p ∣ n := (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp
  have hcop : p.Coprime m := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpm
    exact hpsq (by rw [← hmul]; exact mul_dvd_mul_left p hpm)
  obtain ⟨k, hk1, hk2⟩ :=
    Nat.chineseRemainder hcop (p - s.val % p) (1 + m - t.val % m)
  have hk1Z : (k : ZMod p) = ((p - s.val % p : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff k (p - s.val % p) p).mpr hk1
  have hk2Z : (k : ZMod m) = ((1 + m - t.val % m : ℕ) : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff k (1 + m - t.val % m) m).mpr hk2
  have hps_le : s.val % p ≤ p := le_of_lt (Nat.mod_lt _ hp.pos)
  have hmr_le : t.val % m ≤ m := le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hm_ne0))
  have haZ : ((p - s.val % p : ℕ) : ZMod p) = - (s.val : ZMod p) := by
    rw [Nat.cast_sub hps_le, ZMod.natCast_self, ZMod.natCast_mod]
    ring
  have hkZ : (k : ZMod p) = - (s.val : ZMod p) := hk1Z.trans haZ
  have hks_eq : ((k + s.val : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, hkZ, neg_add_cancel]
  have hpa : p ∣ k + s.val := (ZMod.natCast_eq_zero_iff (k + s.val) p).mp hks_eq
  have hbZ : ((1 + m - t.val % m : ℕ) : ZMod m) = 1 - (t.val : ZMod m) := by
    have heq : 1 + m - t.val % m = 1 + (m - t.val % m) := by omega
    rw [heq, Nat.cast_add, Nat.cast_one, Nat.cast_sub hmr_le, ZMod.natCast_self,
      ZMod.natCast_mod]
    ring
  have hktZ : ((k + t.val : ℕ) : ZMod m) = 1 := by
    rw [Nat.cast_add, hk2Z, hbZ]
    ring
  set X : ZMod n := (k : ZMod n) with hX
  have hcast_s : X + s = ((k + s.val : ℕ) : ZMod n) := by
    rw [hX]
    conv_lhs => rw [← ZMod.natCast_zmod_val s]
    push_cast
    ring
  have hcast_t : X + t = ((k + t.val : ℕ) : ZMod n) := by
    rw [hX]
    conv_lhs => rw [← ZMod.natCast_zmod_val t]
    push_cast
    ring
  have hzs : jacobiCharZMod n (X + s) = 0 := by
    rw [hcast_s, jacobiCharZMod_natCast, jacobiSym.eq_zero_iff_not_coprime]
    rw [Int.gcd_natCast_natCast]
    intro hg
    have hpdvdgcd : p ∣ Nat.gcd (k + s.val) n := Nat.dvd_gcd hpa hpdvd
    rw [hg] at hpdvdgcd
    exact hp.ne_one (Nat.dvd_one.mp hpdvdgcd)
  have hcop_p : (k + t.val).Coprime p := by
    have hpt : p.Coprime (k + t.val) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hpk
      apply hne
      have hpkZ : ((k + t.val : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (k + t.val) p).mpr hpk
      have hkt_mod : ((k + t.val : ℕ) : ZMod p) =
          (t.val : ZMod p) - (s.val : ZMod p) := by
        rw [Nat.cast_add, hkZ]
        ring
      rw [hkt_mod] at hpkZ
      have heq : ((t.val : ℕ) : ZMod p) = ((s.val : ℕ) : ZMod p) := sub_eq_zero.mp hpkZ
      exact ((ZMod.natCast_eq_natCast_iff t.val s.val p).mp heq).symm
    exact hpt.symm
  have hcop_m : (k + t.val).Coprime m := by
    have hunit : IsUnit ((k + t.val : ℕ) : ZMod m) := hktZ ▸ isUnit_one
    exact (ZMod.isUnit_iff_coprime (k + t.val) m).mp hunit
  have hcop_n : (k + t.val).Coprime n := by
    have h := Nat.Coprime.mul_right hcop_p hcop_m
    simpa [hmul] using h
  have hnt : jacobiCharZMod n (X + t) ≠ 0 := by
    rw [hcast_t, jacobiCharZMod_natCast]
    apply jacobiSym.ne_zero
    rw [Int.gcd_natCast_natCast]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop_n
  have := hst X
  rw [hzs] at this
  exact hnt this.symm

/-- For an odd squarefree modulus greater than one, the map sending a shift to its full shifted
Jacobi-character function is injective. This gives the uniqueness of shift required for
Corollary 1 of [VanDamHallgren2000]. -/
theorem corollary1_shift_injective (n : ℕ) [NeZero n] (hn : Odd n)
    (hsq : Squarefree n) (h1 : 1 < n) :
    Function.Injective
      (fun s : ZMod n => fun x : ZMod n => jacobiCharZMod n (x + s)) := by
  intro s t hst
  have hcong : ∀ p ∈ n.primeFactors, s.val ≡ t.val [MOD p] := by
    intro p hp
    exact shift_prime_congruent hn hsq h1 (fun x => congrFun hst x)
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hcop : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q → p.Coprime q := by
    intro p hp q hq hpq
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
    rw [hpp.coprime_iff_not_dvd]
    intro hdvd
    rcases (Nat.dvd_prime hqq).mp hdvd with h1' | h1'
    · exact hpp.ne_one h1'
    · exact hpq h1'
  have hprod : s.val ≡ t.val [MOD ∏ p ∈ n.primeFactors, p] :=
    modEq_prod_of_forall n.primeFactors id hcop hcong
  rw [Nat.prod_primeFactors_of_squarefree hsq] at hprod
  rw [← ZMod.natCast_zmod_val s, ← ZMod.natCast_zmod_val t]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hprod

/-- For an odd squarefree modulus greater than one, there exists a decoder from complete
integer-valued functions on the residue ring that recovers every Jacobi-character shift. The
decoder is a chosen left inverse of the injective shift map, giving the functional recovery
conclusion for Corollary 1 of [VanDamHallgren2000]. -/
theorem corollary1_shiftedJacobi_solved (n : ℕ) [NeZero n] (hn : Odd n)
    (hsq : Squarefree n) (h1 : 1 < n) :
    ∃ D : (ZMod n → ℤ) → ZMod n,
      ∀ s : ZMod n, D (fun x => jacobiCharZMod n (x + s)) = s := by
  classical
  have hinj := corollary1_shift_injective n hn hsq h1
  refine ⟨fun f =>
    Function.invFun (fun s : ZMod n => fun x : ZMod n => jacobiCharZMod n (x + s)) f, ?_⟩
  intro s
  exact (Function.leftInverse_invFun hinj) s

end Qatlib.Papers.QuadChar00.MainResults
