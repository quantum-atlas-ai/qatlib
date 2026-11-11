/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Function.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.LinearDiseq07.MainResults.RamanujanSum

/-!
# Bounds for root-of-unity distance sums

This module derives the normalized squared-distance bounds for a nontrivial root of unity in
Lemma 2 of [Ivanyos2008]. The proof combines `sum_normSq_eq`, which expresses the distance sum
through a Ramanujan sum, with elementary totient identities.

## Main statements

* `sum_normSq_eq`: Relates squared distances to the real part of a root sum.
* `source_lemma2_root_sum_bound`: Places the normalized distance sum between one half and two.

## References

* [Ivanyos, 2008][Ivanyos2008]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.LinearDiseq07.MainResults

/-- A complex number whose positive power is one has squared norm one. -/
lemma normSq_eq_one_of_pow_eq_one {ω : ℂ} {m : ℕ} (hm : 0 < m) (hω : ω ^ m = 1) :
    Complex.normSq ω = 1 := by
  have hpow : (Complex.normSq ω) ^ m = 1 := by
    rw [← map_pow, hω, Complex.normSq_one]
  exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg ω) hm.ne').mp hpow

/-- For a complex number of squared norm one, `Complex.normSq (1 - ω^j)` equals `2 - 2 *
(ω^j).re`, as used in Lemma 2 of [Ivanyos2008]. -/
lemma normSq_one_sub_pow_eq {ω : ℂ} (hω : Complex.normSq ω = 1) (j : ℕ) :
    Complex.normSq (1 - ω ^ j) = 2 - 2 * (ω ^ j).re := by
  have hnorm : Complex.normSq (ω ^ j) = 1 := by
    rw [map_pow, hω, one_pow]
  have hnorm' : (ω ^ j).re * (ω ^ j).re + (ω ^ j).im * (ω ^ j).im = 1 := by
    rw [← Complex.normSq_apply]; exact hnorm
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [hnorm']

/-- The sum of squared distances over residues coprime to `m` equals twice the totient minus
twice the real part of the corresponding root sum [Ivanyos2008]. -/
lemma sum_normSq_eq {m : ℕ} {ω : ℂ} (hω : Complex.normSq ω = 1) :
    (∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m),
        Complex.normSq (1 - ω ^ j))
      = 2 * (Nat.totient m : ℝ)
        - 2 * (∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m), ω ^ j).re := by
  rw [Finset.sum_congr rfl (fun j _ => normSq_one_sub_pow_eq hω j)]
  rw [Finset.sum_sub_distrib, Complex.re_sum, ← Finset.mul_sum, Finset.sum_const]
  have hcard : ((Finset.range m).filter (fun j => Nat.Coprime j m)).card
      = ((Finset.range m).filter (fun a => Nat.Coprime m a)).card := by
    congr 1
    exact Finset.filter_congr (fun x _ => Nat.coprime_comm)
  rw [Nat.totient_eq_card_coprime, ← hcard]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/-- For positive `m`, its totient is the product of `m` divided by its prime radical and the
totient of that radical. -/
lemma totient_eq_div_rad_mul_totient_rad {m : ℕ} (_hm : 0 < m) :
    Nat.totient m
      = (m / ∏ p ∈ m.primeFactors, p) * Nat.totient (∏ p ∈ m.primeFactors, p) := by
  set rad := ∏ p ∈ m.primeFactors, p with hrad
  have hradpos : 0 < rad := by
    rw [hrad]
    exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have hpf : rad.primeFactors = m.primeFactors := by
    rw [hrad]
    exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hφm := Nat.totient_eq_div_primeFactors_mul m
  have hφrad := Nat.totient_eq_div_primeFactors_mul rad
  rw [hpf] at hφrad
  have hdiv : rad / (∏ p ∈ m.primeFactors, p) = 1 := by
    rw [← hrad]
    exact Nat.div_self hradpos
  rw [hdiv, one_mul] at hφrad
  rw [← hrad] at hφm
  rw [hφrad, hφm]

/-- If `m0` divides the prime radical of positive `m`, the totient of the radical factors into
the totients of `m0` and its complementary factor. -/
lemma totient_rad_eq_mul {m m0 : ℕ} (_hm : 0 < m)
    (hm0 : m0 ∣ ∏ p ∈ m.primeFactors, p) :
    Nat.totient (∏ p ∈ m.primeFactors, p)
      = Nat.totient m0 * Nat.totient ((∏ p ∈ m.primeFactors, p) / m0) := by
  set rad := ∏ p ∈ m.primeFactors, p with hrad
  have hradpos : 0 < rad := by
    rw [hrad]
    exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have hsq : Squarefree rad := by
    rw [hrad]
    exact rad_squarefree m
  have hm0pos : 0 < m0 := Nat.pos_of_dvd_of_pos hm0 hradpos
  have hmul : m0 * (rad / m0) = rad := Nat.mul_div_cancel' hm0
  have hsq2 : Squarefree (m0 * (rad / m0)) := by rw [hmul]; exact hsq
  have hcop : m0.Coprime (rad / m0) := Nat.coprime_of_squarefree_mul hsq2
  rw [← Nat.totient_mul hcop, hmul]

/-- The totient of a natural number at least three is at least two, an estimate used in Lemma 2
of [Ivanyos2008]. -/
lemma totient_ge_two {n : ℕ} (hn : 3 ≤ n) : 2 ≤ Nat.totient n := by
  by_contra h
  have hle : Nat.totient n ≤ 1 := by omega
  have hpos : 0 < n := by omega
  have hdvd : n ∣ 2 := Nat.dvd_two_of_totient_le_one hpos hle
  have hle2 : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- Lemma 2 of [Ivanyos2008]: for a nontrivial `m`-th root of unity with `m ≥ 2`, the sum of
squared distances over coprime residues, divided by twice the totient, lies between `1 / 2`
and `2`. -/
theorem source_lemma2_root_sum_bound {m : ℕ} (hm : 2 ≤ m) {ω : ℂ}
    (hωm : ω ^ m = 1) (hω1 : ω ≠ 1) :
    (1 / 2 : ℝ) ≤ (1 / (2 * (Nat.totient m : ℝ)))
        * ∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m),
            Complex.normSq (1 - ω ^ j) ∧
      (1 / (2 * (Nat.totient m : ℝ)))
        * ∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m),
            Complex.normSq (1 - ω ^ j) ≤ 2 := by
  classical
  set m0 := orderOf ω with hm0def
  have hmpos : 0 < m := by omega
  have hprim : IsPrimitiveRoot ω m0 := IsPrimitiveRoot.orderOf ω
  have hm0pos : 0 < m0 := by
    have hfin : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hmpos, hωm⟩
    exact hfin.orderOf_pos
  have hm0dvd : m0 ∣ m := (hprim.pow_eq_one_iff_dvd m).mp hωm
  have hm0ne1 : m0 ≠ 1 := fun h => hω1 (orderOf_eq_one_iff.mp h)
  have hm0ge2 : 2 ≤ m0 := by omega
  have hωnorm : Complex.normSq ω = 1 := normSq_eq_one_of_pow_eq_one hmpos hωm
  set rad := ∏ p ∈ m.primeFactors, p with hrad
  have hradpos : 0 < rad := by
    rw [hrad]
    exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have hraddvd : rad ∣ m := by rw [hrad]; exact rad_dvd m

  have hS := source_lemma1_ramanujan_sum (w := ω) hprim hm0dvd hm0pos hmpos
  rw [← hrad] at hS

  set sR : ℝ := if m0 ∣ rad then
      (ArithmeticFunction.moebius m0 : ℝ) * ((m / rad : ℕ) : ℝ)
        * (Nat.totient (rad / m0) : ℝ) else 0 with hsR
  have hScast : ((sR : ℂ)) = ∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m),
      ω ^ j := by
    rw [hS, hsR]
    split_ifs with h
    · push_cast; ring
    · push_cast; rfl
  have hSre : (∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m), ω ^ j).re
      = sR := by
    rw [← hScast, Complex.ofReal_re]
  have hkeysum := sum_normSq_eq (m := m) (ω := ω) hωnorm
  rw [hSre] at hkeysum

  have hφmpos : (0 : ℝ) < (Nat.totient m : ℝ) := by
    have : 0 < Nat.totient m := Nat.totient_pos.mpr hmpos
    exact_mod_cast this
  have hApos : (0 : ℝ) < ((m / rad : ℕ) : ℝ) := by
    have : 0 < m / rad := Nat.div_pos (Nat.le_of_dvd hmpos hraddvd) hradpos
    exact_mod_cast this
  have hφ1 : (Nat.totient m : ℝ) = ((m / rad : ℕ) : ℝ) * (Nat.totient rad : ℝ) := by
    have h := totient_eq_div_rad_mul_totient_rad hmpos
    rw [← hrad] at h
    exact_mod_cast h
  have hφm0pos : (0 : ℝ) < (Nat.totient m0 : ℝ) := by
    have : 0 < Nat.totient m0 := Nat.totient_pos.mpr hm0pos
    exact_mod_cast this
  have hφm0ge1 : (1 : ℝ) ≤ (Nat.totient m0 : ℝ) := by
    have h1 : (1 : ℕ) ≤ Nat.totient m0 := Nat.totient_pos.mpr hm0pos
    exact_mod_cast h1
  have hμabs : |(ArithmeticFunction.moebius m0 : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := m0)
    rw [← Int.cast_abs]
    exact_mod_cast h

  have habs : |sR| ≤ (Nat.totient m : ℝ) := by
    rw [hsR]
    split_ifs with hdiv
    · have hφrad : (Nat.totient rad : ℝ)
          = (Nat.totient m0 : ℝ) * (Nat.totient (rad / m0) : ℝ) := by
        have h := totient_rad_eq_mul (m := m) hmpos hdiv
        rw [← hrad] at h
        exact_mod_cast h
      have hB : (0 : ℝ) ≤ (Nat.totient (rad / m0) : ℝ) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hApos), abs_of_nonneg hB]
      have step1 : |(ArithmeticFunction.moebius m0 : ℝ)|
            * ((m / rad : ℕ) : ℝ) ≤ 1 * ((m / rad : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hμabs (le_of_lt hApos)
      have step2 : |(ArithmeticFunction.moebius m0 : ℝ)|
            * ((m / rad : ℕ) : ℝ) * (Nat.totient (rad / m0) : ℝ)
          ≤ 1 * ((m / rad : ℕ) : ℝ) * (Nat.totient (rad / m0) : ℝ) :=
        mul_le_mul_of_nonneg_right step1 hB
      have step3 : 1 * ((m / rad : ℕ) : ℝ) * (Nat.totient (rad / m0) : ℝ)
          ≤ 1 * ((m / rad : ℕ) : ℝ)
              * ((Nat.totient m0 : ℝ) * (Nat.totient (rad / m0) : ℝ)) := by
        have hnonneg : (0 : ℝ) ≤ 1 * ((m / rad : ℕ) : ℝ) := by positivity
        have hb : (Nat.totient (rad / m0) : ℝ)
            ≤ (Nat.totient m0 : ℝ) * (Nat.totient (rad / m0) : ℝ) := by
          simpa using mul_le_mul_of_nonneg_right hφm0ge1 hB
        exact mul_le_mul_of_nonneg_left hb hnonneg
      have step4 : 1 * ((m / rad : ℕ) : ℝ)
          * ((Nat.totient m0 : ℝ) * (Nat.totient (rad / m0) : ℝ))
            = (Nat.totient m : ℝ) := by
        rw [hφ1, hφrad]; ring
      linarith
    · simp only [abs_zero]
      exact_mod_cast Nat.zero_le (Nat.totient m)

  have hhalf : sR ≤ (Nat.totient m : ℝ) / 2 := by
    by_cases hpos : sR ≤ 0
    · have : (0 : ℝ) ≤ (Nat.totient m : ℝ) / 2 := by positivity
      linarith
    · push_neg at hpos
      rw [hsR] at hpos ⊢
      split_ifs with hdiv
      · have hApos' := hApos
        have hB : (0 : ℝ) < (Nat.totient (rad / m0) : ℝ) := by
          have hd : 0 < rad / m0 := Nat.div_pos (Nat.le_of_dvd hradpos hdiv) hm0pos
          have : 0 < Nat.totient (rad / m0) := Nat.totient_pos.mpr hd
          exact_mod_cast this
        rw [if_pos hdiv] at hpos
        have hμpos : (0 : ℝ) < (ArithmeticFunction.moebius m0 : ℝ) := by
          by_contra h
          push_neg at h
          have h1 : (ArithmeticFunction.moebius m0 : ℝ) * ((m / rad : ℕ) : ℝ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hApos')
          have h2 : (ArithmeticFunction.moebius m0 : ℝ) * ((m / rad : ℕ) : ℝ)
              * (Nat.totient (rad / m0) : ℝ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h1 (by positivity)
          linarith
        have hμ1 : (ArithmeticFunction.moebius m0 : ℝ) = 1 := by
          have hle : (ArithmeticFunction.moebius m0 : ℝ) ≤ 1 :=
            le_trans (le_abs_self _) hμabs
          have hge : (1 : ℝ) ≤ (ArithmeticFunction.moebius m0 : ℝ) := by
            have hz : (0 : ℤ) < ArithmeticFunction.moebius m0 := by
              by_contra h
              push_neg at h
              have : (ArithmeticFunction.moebius m0 : ℝ) ≤ 0 := by exact_mod_cast h
              linarith
            have hz1 : (1 : ℤ) ≤ ArithmeticFunction.moebius m0 := by omega
            exact_mod_cast hz1
          linarith
        have hφrad : (Nat.totient rad : ℝ)
            = (Nat.totient m0 : ℝ) * (Nat.totient (rad / m0) : ℝ) := by
          have h := totient_rad_eq_mul (m := m) hmpos hdiv
          rw [← hrad] at h
          exact_mod_cast h
        have hm0ne2 : m0 ≠ 2 := by
          intro h2
          rw [h2] at hμ1
          have h2val : ArithmeticFunction.moebius 2 = -1 :=
            ArithmeticFunction.moebius_apply_prime Nat.prime_two
          rw [h2val] at hμ1
          norm_num at hμ1
        have hm0ge3 : 3 ≤ m0 := by omega
        have hφm0ge2 : (2 : ℝ) ≤ (Nat.totient m0 : ℝ) := by
          have := totient_ge_two hm0ge3
          exact_mod_cast this
        have hsRbranch : sR
            = ((m / rad : ℕ) : ℝ) * (Nat.totient (rad / m0) : ℝ) := by
          rw [hsR, if_pos hdiv, hμ1, one_mul]
        have hkey : sR * (Nat.totient m0 : ℝ) = (Nat.totient m : ℝ) := by
          rw [hsRbranch, hφ1, hφrad]
          ring
        have hle : sR ≤ (Nat.totient m : ℝ) / 2 := by
          have hgoal : sR * (Nat.totient m0 : ℝ)
              ≤ ((Nat.totient m : ℝ) / 2) * (Nat.totient m0 : ℝ) := by
            rw [hkey]
            nlinarith
          exact le_of_mul_le_mul_right hgoal hφm0pos
        rw [hμ1, one_mul, ← hsRbranch]
        exact hle
      · linarith

  have hval : (1 / (2 * (Nat.totient m : ℝ)))
        * ∑ j ∈ (Finset.range m).filter (fun j => Nat.Coprime j m),
            Complex.normSq (1 - ω ^ j) = 1 - sR / (Nat.totient m : ℝ) := by
    rw [hkeysum]
    have hne : (Nat.totient m : ℝ) ≠ 0 := ne_of_gt hφmpos
    field_simp
  rw [hval]
  constructor
  · have : sR / (Nat.totient m : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hφmpos]
      nlinarith
    linarith
  · have : -(1 : ℝ) ≤ sR / (Nat.totient m : ℝ) := by
      rw [le_div_iff₀ hφmpos]
      nlinarith [neg_le_of_abs_le habs]
    linarith

end Qatlib.Papers.LinearDiseq07.MainResults
