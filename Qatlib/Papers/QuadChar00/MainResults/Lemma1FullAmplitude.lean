/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Lemma1ModularFourier
import Qatlib.Papers.QuadChar00.MainResults.Corollary1ShiftedJacobi
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# The Jacobi Fourier amplitude at every frequency

This module realizes the Jacobi character as the complex Dirichlet character `jacobiDirichlet`
and proves its primitivity for odd squarefree modulus greater than one. A prime divisor cannot
be removed from its modulus, and the conductor argument then gives primitivity.

Applying the primitive-character Gauss-sum identity yields `jacobiFourierSum` for every
frequency, including nonunits. Translation supplies the phase factor in `lemma1_amplitude_all`,
giving the complete unnormalized Fourier-amplitude identity of Lemma 1 in [VanDamHallgren2000].

## Main statements

* `jacobiDirichlet_isQuadratic` and `jacobiDirichlet_inv`: quadraticity and self-inversion.
* `jacobiDirichlet_isPrimitive`: primitivity for odd squarefree modulus greater than one.
* `jacobiFourierSum`: the unshifted identity at every frequency.
* `lemma1_amplitude_all`: the shifted identity with Gauss sum, shift phase, and Jacobi factor.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators
open MulChar

/-- The complex Dirichlet character modulo `n` obtained by casting the integer-valued Jacobi
character to the complex numbers. -/
def jacobiDirichlet (n : ℕ) [NeZero n] : DirichletCharacter ℂ n where
  toFun a := (jacobiCharZMod n a : ℂ)
  map_one' := by
    rw [jacobiCharZMod_one]
    norm_num
  map_mul' a b := by
    rw [jacobiCharZMod_mul]
    push_cast
    ring
  map_nonunit' a ha := by
    have h : jacobiCharZMod n a = 0 :=
      (jacobiCharZMod_eq_zero_iff_not_isUnit n a).mpr ha
    rw [h]
    norm_num

/-- The value of `jacobiDirichlet n` at a residue is the complex cast of `jacobiCharZMod n` at
that residue. -/
@[simp]
lemma jacobiDirichlet_apply (n : ℕ) [NeZero n] (a : ZMod n) :
    jacobiDirichlet n a = (jacobiCharZMod n a : ℂ) := rfl

/-- The complex Jacobi Dirichlet character is quadratic: each value is zero, one, or minus one. -/
lemma jacobiDirichlet_isQuadratic (n : ℕ) [NeZero n] :
    IsQuadratic (jacobiDirichlet n) := by
  intro a
  by_cases ha : IsUnit a
  · rcases jacobiCharZMod_unit_eq_one_or_neg_one n ha.unit with h | h
    · right; left
      rw [jacobiDirichlet_apply]
      have hcoe : (ha.unit : ZMod n) = a := IsUnit.unit_spec ha
      rw [← hcoe, h]
      norm_num
    · right; right
      rw [jacobiDirichlet_apply]
      have hcoe : (ha.unit : ZMod n) = a := IsUnit.unit_spec ha
      rw [← hcoe, h]
      norm_num
  · left
    rw [jacobiDirichlet_apply, (jacobiCharZMod_eq_zero_iff_not_isUnit n a).mpr ha]
    norm_num

/-- The inverse of the Jacobi Dirichlet character equals the character itself. -/
lemma jacobiDirichlet_inv (n : ℕ) [NeZero n] :
    (jacobiDirichlet n)⁻¹ = jacobiDirichlet n :=
  IsQuadratic.inv (jacobiDirichlet_isQuadratic n)

/-- For an odd squarefree modulus `n > 1` and any prime divisor `p`, the Jacobi Dirichlet
character does not factor through modulus `n / p`. -/
theorem jacobiDirichlet_not_factorsThrough {n : ℕ} [NeZero n] (hn : Odd n)
    (hsq : Squarefree n) (h1 : 1 < n) {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ n) :
    ¬ DirichletCharacter.FactorsThrough (jacobiDirichlet n) (n / p) := by
  classical
  intro hft
  have hp2 : p ≠ 2 := hn.ne_two_of_dvd_nat hpdvd
  set m := n / p with hm
  have hmul : p * m = n := Nat.mul_div_cancel' hpdvd
  have hp_ne0 : p ≠ 0 := hp.ne_zero
  have hm_ne0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    omega
  haveI : NeZero p := ⟨hp_ne0⟩
  haveI : NeZero m := ⟨hm_ne0⟩
  have hpsq : ¬ p * p ∣ n := (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp
  have hcop : p.Coprime m := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpm
    exact hpsq (by rw [← hmul]; exact mul_dvd_mul_left p hpm)
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨r, hr⟩ := quadraticChar_exists_neg_one (F := ZMod p) hchar
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop r.val 1

  have hJp : jacobiSym (k : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    show quadraticChar (ZMod p) ((k : ℤ) : ZMod p) = -1
    push_cast
    have hk_cast : (k : ZMod p) = r := by
      rw [show (k : ZMod p) = (r.val : ZMod p) from ?_, ZMod.natCast_zmod_val]
      rw [ZMod.natCast_eq_natCast_iff]
      exact hk1
    rw [hk_cast, hr]
  have hJm : jacobiSym (k : ℤ) m = 1 := by
    have hmod : (k : ℤ) % (m : ℤ) = (1 : ℤ) % (m : ℤ) := by
      have h2 : ((k % m : ℕ) : ℤ) = (((1 % m : ℕ)) : ℤ) := by rw [hk2]
      rw [Int.natCast_mod, Int.natCast_mod] at h2
      simpa only [Int.natCast_one] using h2
    rw [jacobiSym.mod_left' hmod]
    exact jacobiSym.one_left m
  have hJn : jacobiSym (k : ℤ) n = -1 := by
    rw [← hmul, jacobiSym.mul_right, hJp, hJm]
    ring
  have hunit : IsUnit (k : ZMod n) := by
    rw [ZMod.isUnit_iff_coprime k n, Nat.coprime_iff_gcd_eq_one]
    by_contra hg
    have hz : jacobiSym (k : ℤ) n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      simpa [Int.gcd_def] using hg
    rw [hJn] at hz
    norm_num at hz
  have huJ : jacobiCharZMod n (k : ZMod n) = -1 := by
    unfold jacobiCharZMod
    rw [ZMod.val_natCast]
    have hcast : ((k % n : ℕ) : ℤ) = (k : ℤ) % (n : ℤ) := Int.natCast_mod k n
    rw [hcast, ← jacobiSym.mod_left (k : ℤ) n]
    exact hJn

  set u : (ZMod n)ˣ := hunit.unit with hu
  have huval : (u : ZMod n) = (k : ZMod n) := IsUnit.unit_spec hunit
  have hdvd : m ∣ n := ⟨p, by rw [← hmul, mul_comm]⟩

  have hunits : ZMod.unitsMap hdvd u = 1 := by
    apply Units.ext
    rw [ZMod.unitsMap_val, Units.val_one, huval, ZMod.cast_natCast hdvd k]
    simpa using (ZMod.natCast_eq_natCast_iff k 1 m).mpr hk2

  have hchiu : (jacobiDirichlet n).toUnitHom u ≠ 1 := by
    intro h
    have hval : (((jacobiDirichlet n).toUnitHom u : ℂˣ) : ℂ) = 1 := by
      rw [h]; norm_num
    have hEq : (((jacobiDirichlet n).toUnitHom u : ℂˣ) : ℂ) =
        (jacobiDirichlet n) (k : ZMod n) := by
      rw [hu]
      exact (DirichletCharacter.toUnitHom_eq_char'
        (χ := jacobiDirichlet n) hunit).symm
    rw [hEq, jacobiDirichlet_apply, huJ] at hval
    norm_num at hval

  have hle := (DirichletCharacter.factorsThrough_iff_ker_unitsMap
    (χ := jacobiDirichlet n) hdvd).mp hft
  have hker : u ∈ (ZMod.unitsMap hdvd).ker := by
    rw [MonoidHom.mem_ker]; exact hunits
  have hcontra := hle hker
  rw [MonoidHom.mem_ker] at hcontra
  exact hchiu hcontra

/-- If every member of a finite pairwise coprime family of natural numbers divides `d`, then the
product of the family divides `d`. -/
lemma prod_prime_dvd_of_coprime {ι : Type*} (s : Finset ι) (f : ι → ℕ) (d : ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j))
    (h : ∀ i ∈ s, f i ∣ d) : (∏ i ∈ s, f i) ∣ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.prod_insert hi]
    have hfi : f i ∣ d := h i (Finset.mem_insert_self _ _)
    have ht : ∀ j ∈ t, f j ∣ d := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hcopit : (f i).Coprime (∏ j ∈ t, f j) := by
      rw [Nat.coprime_prod_right_iff]
      intro j hj
      exact hcop i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun hji => hi (hji ▸ hj))
    have hcopt : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → (f j).Coprime (f k) :=
      fun j hj k hk hjk =>
        hcop j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    exact hcopit.mul_dvd_of_dvd_of_dvd hfi (ih hcopt ht)

/-- For an odd squarefree modulus greater than one, the Jacobi Dirichlet character is primitive,
so its conductor is the full modulus. -/
theorem jacobiDirichlet_isPrimitive (n : ℕ) [NeZero n] (hn : Odd n)
    (hsq : Squarefree n) (h1 : 1 < n) :
    DirichletCharacter.IsPrimitive (jacobiDirichlet n) := by
  classical
  rw [DirichletCharacter.isPrimitive_def]
  set C := DirichletCharacter.conductor (jacobiDirichlet n) with hC
  have hcd : C ∣ n := hC ▸ DirichletCharacter.conductor_dvd_level _
  have hpdvd : ∀ p ∈ n.primeFactors, p ∣ C := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    by_contra hpc
    have hcop : C.Coprime p :=
      ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpc).symm
    have hdiv : C ∣ n / p := by
      have hn_eq : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
      rw [hn_eq] at hcd
      exact hcop.dvd_mul_left.mp hcd
    have hmono : DirichletCharacter.FactorsThrough (jacobiDirichlet n) (n / p) :=
      DirichletCharacter.FactorsThrough.mono
        (χ := jacobiDirichlet n)
        (DirichletCharacter.factorsThrough_conductor (jacobiDirichlet n)) hdiv
        (Nat.div_dvd_of_dvd hpn)
    exact jacobiDirichlet_not_factorsThrough hn hsq h1 hpp hpn hmono
  have hcop : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q → p.Coprime q := by
    intro p hp q hq hpq
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
    rw [hpp.coprime_iff_not_dvd]
    intro hdvd
    rcases (Nat.dvd_prime hqq).mp hdvd with h1' | h1'
    · exact hpp.ne_one h1'
    · exact hpq h1'
  have hnc : n ∣ C := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact prod_prime_dvd_of_coprime n.primeFactors id _ hcop hpdvd
  exact Nat.dvd_antisymm hcd hnc

/-- For odd squarefree `n > 1`, the unnormalized Fourier sum of the Jacobi character at any
residue `y` equals `jacobiGaussSum n` times the Jacobi character at `y`. The identity
includes nonunit frequencies, where the character factor is zero. -/
theorem jacobiFourierSum (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n)
    (y : ZMod n) :
    ∑ x : ZMod n, ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar (x * y)
      = jacobiGaussSum n * ((jacobiCharZMod n y : ℤ) : ℂ) := by
  have hprim := jacobiDirichlet_isPrimitive n hn hsq h1
  have h := gaussSum_mulShift_of_isPrimitive
    (e := ZMod.stdAddChar (N := n)) hprim y
  rw [jacobiDirichlet_inv] at h
  have hL : gaussSum (jacobiDirichlet n) ((ZMod.stdAddChar (N := n)).mulShift y)
      = ∑ x : ZMod n, ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar (x * y) := by
    simp only [gaussSum, AddChar.mulShift_apply, jacobiDirichlet_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_comm y a]
  have hR : gaussSum (jacobiDirichlet n) (ZMod.stdAddChar (N := n)) = jacobiGaussSum n := by
    simp only [gaussSum, jacobiGaussSum, jacobiDirichlet_apply]
  rw [hL, hR, jacobiDirichlet_apply] at h
  rw [h]
  ring

/-- For odd squarefree `n > 1` and every shift and frequency, the unnormalized Fourier sum of
the shifted Jacobi character equals the Gauss sum times the additive phase at `-(s * y)`
times the Jacobi character at `y`. This is the full frequency identity underlying Lemma 1 of
[VanDamHallgren2000]. -/
theorem lemma1_amplitude_all (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (h1 : 1 < n) (s y : ZMod n) :
    ∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y)
      = jacobiGaussSum n * ZMod.stdAddChar (-(s * y)) * ((jacobiCharZMod n y : ℤ) : ℂ) := by
  classical
  have hshift :
      (∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y))
      = ZMod.stdAddChar (-(s * y)) *
          ∑ u : ZMod n, ((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * y) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (fun u : ZMod n => u + s) (Equiv.addRight s).bijective
      (fun x => ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y))
      (fun u => ZMod.stdAddChar (-(s * y)) *
        (((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * y))) ?_
    intro u
    change ((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)
        = ZMod.stdAddChar (-(s * y)) *
            (((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar ((u + s) * y))
    rw [show (u + s) * y = u * y + s * y by ring, AddChar.map_add_eq_mul]
    have hneg : ZMod.stdAddChar (-(s * y)) * ZMod.stdAddChar (s * y) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc
      ((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)
          = (((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)) * 1 := by ring
      _ = (((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * y)) *
            (ZMod.stdAddChar (-(s * y)) * ZMod.stdAddChar (s * y)) := by rw [hneg]
      _ = ZMod.stdAddChar (-(s * y)) *
            (((jacobiCharZMod n (u + s) : ℤ) : ℂ) *
              (ZMod.stdAddChar (u * y) * ZMod.stdAddChar (s * y))) := by ring
  rw [hshift, jacobiFourierSum n hn hsq h1 y]
  ring

end Qatlib.Papers.QuadChar00.MainResults
