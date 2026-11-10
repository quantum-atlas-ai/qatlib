/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

open Finset
open scoped BigOperators

namespace Qatlib.Papers.LinearDiseq07.MainResults

lemma sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℤ)
    (f := ArithmeticFunction.moebius) (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h]
  simp [ArithmeticFunction.one_apply]

lemma int_ite_cast_one (n : ℕ) :
    (Int.castRingHom ℂ) (if n = 1 then (1:ℤ) else 0)
      = (if n = 1 then (1:ℂ) else 0) := by
  by_cases hn : n = 1 <;> simp [hn]

lemma sum_moebius_divisors_complex (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
  have h := sum_moebius_divisors n
  calc (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ))
      = (Int.castRingHom ℂ) (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) :=
          (map_sum (Int.castRingHom ℂ) _ _).symm
    _ = (Int.castRingHom ℂ) (if n = 1 then (1:ℤ) else 0) := by rw [h]
    _ = if n = 1 then (1:ℂ) else 0 := int_ite_cast_one n

lemma coprime_indicator (j m : ℕ) :
    (if Nat.Coprime j m then (1:ℂ) else 0)
      = ∑ d ∈ (Nat.gcd j m).divisors, (ArithmeticFunction.moebius d : ℂ) := by
  rw [sum_moebius_divisors_complex]

lemma filter_dvd_range_image (d m : ℕ) (hdm : d ∣ m) (hd : 0 < d) :
    (Finset.range m).filter (fun j => d ∣ j)
      = (Finset.range (m / d)).image (fun i => d * i) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hjm, dvd⟩
    exact ⟨j / d, by rw [Nat.div_lt_iff_lt_mul hd, Nat.div_mul_cancel hdm]; exact hjm,
      Nat.mul_div_cancel' dvd⟩
  · rintro ⟨i, him, rfl⟩
    exact ⟨by calc d * i < d * (m / d) := Nat.mul_lt_mul_of_pos_left him hd
                _ = m := Nat.mul_div_cancel' hdm,
      dvd_mul_right d i⟩

lemma sum_filter_dvd_eq (d m : ℕ) (hdm : d ∣ m) (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ j ∈ (Finset.range m).filter (fun j => d ∣ j), f j)
      = ∑ i ∈ Finset.range (m / d), f (d * i) := by
  rw [filter_dvd_range_image d m hdm hd, Finset.sum_image]
  intro i _ j _ hij
  exact Nat.mul_left_cancel hd hij

lemma geom_inner {w : ℂ} {m0 d m : ℕ} (hw : IsPrimitiveRoot w m0)
    (hdm : d ∣ m) (hm : m0 ∣ m) :
    (∑ i ∈ Finset.range (m / d), w ^ (d * i))
      = if w ^ d = 1 then ((m / d : ℕ) : ℂ) else 0 := by
  have hpow : ∀ i, w ^ (d * i) = (w ^ d) ^ i := fun i => by rw [pow_mul]
  simp only [hpow]
  by_cases hx : w ^ d = 1
  · rw [if_pos hx]; simp [hx]
  · rw [if_neg hx]
    have hxn : (w ^ d) ^ (m / d) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' hdm]
      exact (hw.pow_eq_one_iff_dvd m).mpr hm
    have hg := geom_sum_mul (w ^ d) (m / d)
    rw [hxn, sub_self, mul_eq_zero] at hg
    rcases hg with h | h
    · exact h
    · exact absurd h (sub_ne_zero.mpr hx)

theorem ramanujan_divisor_sum {w : ℂ} {m0 : ℕ} (hw : IsPrimitiveRoot w m0)
    {m : ℕ} (hm : m0 ∣ m) (_hm0 : 0 < m0) (hmpos : 0 < m) :
    (∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m), w ^ j)
      = ∑ d ∈ m.divisors.filter (fun d => m0 ∣ d),
          (ArithmeticFunction.moebius d : ℂ) * ((m / d : ℕ) : ℂ) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  trans ∑ j ∈ Finset.range m,
      (∑ d ∈ m.divisors, if d ∣ j then (ArithmeticFunction.moebius d : ℂ) else 0) * w ^ j
  · apply Finset.sum_congr rfl
    intro j _
    have hc : (if Nat.Coprime j m then w ^ j else 0)
        = (if Nat.Coprime j m then (1:ℂ) else 0) * w ^ j := by
      by_cases h : Nat.Coprime j m <;> simp [h]
    rw [hc, coprime_indicator j m]
    congr 1
    rw [show (Nat.gcd j m).divisors = m.divisors.filter (fun d => d ∣ j) from ?_,
      Finset.sum_filter]
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdj, hdm⟩, _⟩
      exact ⟨⟨hdm, ne_of_gt hmpos⟩, hdj⟩
    · rintro ⟨⟨hdm, _⟩, hdj⟩
      exact ⟨⟨hdj, hdm⟩, (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right j m) hmpos).ne'⟩
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    have hdm : d ∣ m := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm hmpos
    have hmul : (∑ j ∈ Finset.range m,
          (if d ∣ j then (ArithmeticFunction.moebius d : ℂ) else 0) * w ^ j)
        = (ArithmeticFunction.moebius d : ℂ)
            * ∑ j ∈ Finset.range m, if d ∣ j then w ^ j else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hdj : d ∣ j <;> simp [hdj, mul_comm]
    rw [hmul]
    have hfilter : (∑ j ∈ Finset.range m, if d ∣ j then w ^ j else 0)
        = ∑ i ∈ Finset.range (m / d), w ^ (d * i) := by
      rw [← Finset.sum_filter]
      exact sum_filter_dvd_eq d m hdm hdpos (fun j => w ^ j)
    rw [hfilter, geom_inner hw hdm hm]
    have hiff : w ^ d = 1 ↔ m0 ∣ d := hw.pow_eq_one_iff_dvd d
    by_cases hmd : m0 ∣ d
    · rw [if_pos (hiff.mpr hmd), if_pos hmd]
    · rw [if_neg (fun h => hmd (hiff.mp h)), if_neg hmd]
      simp

lemma sum_moebius_mul_div_eq_totient {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) * ((n / d : ℕ) : ℤ))
      = (Nat.totient n : ℤ) := by
  have hmain := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun i => (Nat.totient i : ℤ)) (g := fun n => (n : ℤ))).mp ?_
  · have hthis := hmain n hn
    calc (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) * ((n / d : ℕ) : ℤ))
        = ∑ i ∈ n.divisors,
            (fun (a : ℕ) (b : ℕ) => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ)) i (n / i) := rfl
      _ = ∑ x ∈ n.divisorsAntidiagonal,
            (fun (a : ℕ) (b : ℕ) => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ)) x.1 x.2 :=
            (Nat.sum_divisorsAntidiagonal
              (fun (a : ℕ) (b : ℕ) => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ))).symm
      _ = (Nat.totient n : ℤ) := hthis
  · intro n hn
    have hcast : (∑ i ∈ n.divisors, (Nat.totient i : ℤ)) = (n : ℤ) := by
      exact_mod_cast Nat.sum_totient n
    exact hcast

lemma rad_ne_zero {m : ℕ} (_hm : m ≠ 0) : (∏ p ∈ m.primeFactors, p) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma rad_dvd (m : ℕ) : (∏ p ∈ m.primeFactors, p) ∣ m :=
  Nat.prod_primeFactors_dvd m

lemma rad_squarefree (m : ℕ) : Squarefree (∏ p ∈ m.primeFactors, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
        (Nat.prime_of_mem_primeFactors hb)).mpr hab)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

lemma squarefree_dvd_rad {d m : ℕ} (hd : Squarefree d) (hdm : d ∣ m) (hm : m ≠ 0) :
    d ∣ ∏ p ∈ m.primeFactors, p := by
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact Finset.prod_dvd_prod_of_subset d.primeFactors m.primeFactors (fun p => p)
    (Nat.primeFactors_mono hdm hm)

lemma moebius_mul_of_coprime {a b : ℕ} (h : a.Coprime b) :
    (ArithmeticFunction.moebius (a * b) : ℂ)
      = (ArithmeticFunction.moebius a : ℂ) * (ArithmeticFunction.moebius b : ℂ) := by
  have hz : ArithmeticFunction.moebius (a * b)
      = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (R := ℤ) h.gcd_eq_one
  exact_mod_cast hz

lemma sum_moebius_mul_div_eq_totient_complex {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) : ℂ))
      = (Nat.totient n : ℂ) := by
  have hmain := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ)
      (f := fun i => (Nat.totient i : ℂ)) (g := fun n => (n : ℂ))).mp ?_
  · have hthis := hmain n hn
    calc (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) : ℂ))
        = ∑ i ∈ n.divisors,
            (fun (a : ℕ) (b : ℕ) => (ArithmeticFunction.moebius a : ℂ) * (b : ℂ)) i (n / i) := rfl
      _ = ∑ x ∈ n.divisorsAntidiagonal,
            (fun (a : ℕ) (b : ℕ) => (ArithmeticFunction.moebius a : ℂ) * (b : ℂ)) x.1 x.2 :=
            (Nat.sum_divisorsAntidiagonal
              (fun (a : ℕ) (b : ℕ) => (ArithmeticFunction.moebius a : ℂ) * (b : ℂ))).symm
      _ = (Nat.totient n : ℂ) := hthis
  · intro n hn
    have hcast : (∑ i ∈ n.divisors, (Nat.totient i : ℂ)) = (n : ℂ) := by
      exact_mod_cast Nat.sum_totient n
    exact hcast

lemma div_mul_div_eq {m m0 m1 e : ℕ} (hmpos : 0 < m) (hm0 : 0 < m0)
    (hm1dvd : m1 ∣ m) (hm0dvd : m0 ∣ m1) (he : e ∣ m1 / m0) :
    m / (m0 * e) = (m / m1) * ((m1 / m0) / e) := by
  have hm1pos : 0 < m1 := Nat.pos_of_dvd_of_pos hm1dvd hmpos
  have hrpos : 0 < m1 / m0 := Nat.div_pos (Nat.le_of_dvd hm1pos hm0dvd) hm0
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hrpos
  have hdvd : m0 * e ∣ m := by
    have h1 : m0 * e ∣ m1 := by
      have h := Nat.mul_dvd_mul_left m0 he
      rwa [Nat.mul_div_cancel' hm0dvd] at h
    exact h1.trans hm1dvd
  apply Nat.mul_right_cancel (Nat.mul_pos hm0 hepos)
  rw [Nat.div_mul_cancel hdvd]
  have hr : (m1 / m0) / e * e = m1 / m0 := Nat.div_mul_cancel he
  calc m = (m / m1) * m1 := (Nat.div_mul_cancel hm1dvd).symm
    _ = (m / m1) * ((m1 / m0) * m0) := by rw [Nat.div_mul_cancel hm0dvd]
    _ = (m / m1) * ((m1 / m0) / e * e * m0) := by rw [hr]
    _ = (m / m1) * ((m1 / m0) / e) * (m0 * e) := by ring

theorem source_lemma1_ramanujan_sum {w : ℂ} {m0 : ℕ} (hw : IsPrimitiveRoot w m0)
    {m : ℕ} (hm : m0 ∣ m) (hm0 : 0 < m0) (hmpos : 0 < m) :
    (∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m), w ^ j)
      = if m0 ∣ (∏ p ∈ m.primeFactors, p) then
          (ArithmeticFunction.moebius m0 : ℂ)
            * ((m / (∏ p ∈ m.primeFactors, p) : ℕ) : ℂ)
            * (Nat.totient ((∏ p ∈ m.primeFactors, p) / m0) : ℂ)
        else 0 := by
  classical
  rw [ramanujan_divisor_sum hw hm hm0 hmpos]
  set m1 := ∏ p ∈ m.primeFactors, p with hm1def
  have hmne : m ≠ 0 := hmpos.ne'
  have hm1ne : m1 ≠ 0 := by rw [hm1def]; exact rad_ne_zero hmne
  have hm1dvd : m1 ∣ m := by rw [hm1def]; exact rad_dvd m
  have hm1pos : 0 < m1 := Nat.pos_of_dvd_of_pos hm1dvd hmpos
  have hm1sq : Squarefree m1 := by rw [hm1def]; exact rad_squarefree m

  have hreplace : (∑ d ∈ m1.divisors.filter (fun d => m0 ∣ d),
        (ArithmeticFunction.moebius d : ℂ) * ((m / d : ℕ) : ℂ))
      = ∑ d ∈ m.divisors.filter (fun d => m0 ∣ d),
        (ArithmeticFunction.moebius d : ℂ) * ((m / d : ℕ) : ℂ) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Nat.mem_divisors.mpr
        ⟨(Nat.mem_divisors.mp hx.1).1.trans hm1dvd, hmne⟩, hx.2⟩
    · intro x hx hxnot
      rw [Finset.mem_filter] at hx
      have hμ : (ArithmeticFunction.moebius x : ℂ) = 0 := by
        by_contra hne
        have hneZ : (ArithmeticFunction.moebius x : ℤ) ≠ 0 := by
          intro h; exact hne (by rw [h]; simp)
        have hsq : Squarefree x :=
          ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hneZ
        have hxdivm : x ∣ m := (Nat.mem_divisors.mp hx.1).1
        have hxrad : x ∣ m1 := by
          rw [hm1def]; exact squarefree_dvd_rad hsq hxdivm hmne
        exact hxnot (by
          rw [Finset.mem_filter]
          exact ⟨Nat.mem_divisors.mpr ⟨hxrad, hm1ne⟩, hx.2⟩)
      rw [hμ, zero_mul]
  rw [← hreplace]
  by_cases h0 : m0 ∣ m1
  · rw [if_pos h0]
    have hm1eq : m1 = m0 * (m1 / m0) := (Nat.mul_div_cancel' h0).symm
    have hrpos : 0 < m1 / m0 := Nat.div_pos (Nat.le_of_dvd hm1pos h0) hm0

    have hbij : (∑ e ∈ (m1 / m0).divisors,
          (ArithmeticFunction.moebius (m0 * e) : ℂ) * ((m / (m0 * e) : ℕ) : ℂ))
        = ∑ d ∈ m1.divisors.filter (fun d => m0 ∣ d),
          (ArithmeticFunction.moebius d : ℂ) * ((m / d : ℕ) : ℂ) := by
      refine Finset.sum_bij (fun e _ => m0 * e) ?_ ?_ ?_ ?_
      · intro e he
        rw [Finset.mem_filter]
        refine ⟨Nat.mem_divisors.mpr ⟨?_, hm1ne⟩, Nat.dvd_mul_right m0 e⟩
        have h := Nat.mul_dvd_mul_left m0 (Nat.mem_divisors.mp he).1
        rwa [Nat.mul_div_cancel' h0] at h
      · intro e1 _ e2 _ h
        exact Nat.mul_left_cancel hm0 h
      · intro d hd
        rw [Finset.mem_filter] at hd
        have hdm1 : d ∣ m1 := (Nat.mem_divisors.mp hd.1).1
        refine ⟨d / m0, ?_, Nat.mul_div_cancel' hd.2⟩
        rw [Nat.mem_divisors]
        refine ⟨?_, hrpos.ne'⟩
        have hdm : m1 / m0 = (d / m0) * (m1 / d) := by
          apply Nat.div_eq_of_eq_mul_left hm0
          calc m1 = d * (m1 / d) := (Nat.mul_div_cancel' hdm1).symm
            _ = (m0 * (d / m0)) * (m1 / d) := by rw [Nat.mul_div_cancel' hd.2]
            _ = ((d / m0) * (m1 / d)) * m0 := by ring
        exact ⟨m1 / d, by rw [hdm, mul_comm]⟩
      · intro e he
        rfl
    rw [← hbij]

    have hterm : ∀ e ∈ (m1 / m0).divisors,
        (ArithmeticFunction.moebius (m0 * e) : ℂ) * ((m / (m0 * e) : ℕ) : ℂ)
          = (ArithmeticFunction.moebius m0 : ℂ) * ((m / m1 : ℕ) : ℂ)
              * ((ArithmeticFunction.moebius e : ℂ)
                  * (((m1 / m0) / e : ℕ) : ℂ)) := by
      intro e he
      have hevd : e ∣ m1 / m0 := (Nat.mem_divisors.mp he).1
      have hcop : m0.Coprime e := by
        have hmsq : Squarefree (m0 * (m1 / m0)) := by rw [← hm1eq]; exact hm1sq
        exact (Nat.coprime_of_squarefree_mul hmsq).of_dvd_right hevd
      have hμ : (ArithmeticFunction.moebius (m0 * e) : ℂ)
          = (ArithmeticFunction.moebius m0 : ℂ) * (ArithmeticFunction.moebius e : ℂ) :=
        moebius_mul_of_coprime hcop
      have hdiv : m / (m0 * e) = (m / m1) * ((m1 / m0) / e) :=
        div_mul_div_eq hmpos hm0 hm1dvd h0 hevd
      rw [hμ, hdiv]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.mul_sum]
    rw [sum_moebius_mul_div_eq_totient_complex hrpos]
  · rw [if_neg h0]
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    exact absurd (hd.2.trans (Nat.mem_divisors.mp hd.1).1) h0

end Qatlib.Papers.LinearDiseq07.MainResults
