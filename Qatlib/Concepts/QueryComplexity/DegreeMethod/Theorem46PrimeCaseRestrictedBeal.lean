/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Theorem46PrimeCaseRestrictedStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound

/-!
# Prime-case exact query lower bound

This module proves `theorem46PrimeCaseRestricted`, the prime case of the exact query lower bound
for nonconstant symmetric Boolean functions. If the input length is positive and one more than
that length is prime, exact computation by a well-formed observed circuit from a normalized
state requires at least half as many queries as input bits, as in [BealsEtAl2001].

The proof uses parity-weighted polynomial cancellation, Hamming-weight fiber counts, and the
congruence for binomial coefficients modulo the prime input length plus one.

## Main statements

* `low_degree_sum`: parity-weighted cube sums vanish below full degree.
* `sum_by_weight`: symmetric Boolean sums regroup into binomially weighted layers.
* `theorem46PrimeCaseRestricted`: exact observed query depth satisfies the prime-case lower
  bound.

## References

* [Beals et al., 2001, Corollary 4.7][BealsEtAl2001]
-/

set_option autoImplicit false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib
open scoped BigOperators

/-- If `n + 1` is prime, the binomial coefficient `n.choose k` equals `(-1) ^ k` modulo `n + 1`
for `k ≤ n`. -/
private theorem prime_choose (n : ℕ) (hp : Nat.Prime (n + 1)) (k : ℕ) (hk : k ≤ n) :
    (n.choose k : ZMod (n + 1)) = (-1) ^ k := by
  letI : Fact (Nat.Prime (n + 1)) := ⟨hp⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ n := by omega
    have hnz : ((k + 1 : ℕ) : ZMod (n + 1)) ≠ 0 := by
      intro hz
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
        ((ZMod.natCast_eq_zero_iff (k + 1) (n + 1)).mp hz)
    have hrec := congrArg (fun a : ℕ => (a : ZMod (n + 1)))
      (Nat.choose_succ_right_eq n k)
    have hsub : ((n - k : ℕ) : ZMod (n + 1)) = -((k + 1 : ℕ) : ZMod (n + 1)) := by
      have hzero : ((n + 1 : ℕ) : ZMod (n + 1)) = 0 := ZMod.natCast_self _
      rw [Nat.cast_add, Nat.cast_one] at hzero
      rw [Nat.cast_sub hk', Nat.cast_add, Nat.cast_one]
      linear_combination hzero
    simp only [Nat.cast_mul] at hrec
    rw [ih hk', hsub] at hrec
    apply mul_right_cancel₀ hnz <;>
      calc
        (n.choose (k + 1) : ZMod (n + 1)) * (k + 1 : ℕ) =
            (-1 : ZMod (n + 1)) ^ k * -((k + 1 : ℕ) : ZMod (n + 1)) := hrec
        _ = (-1 : ZMod (n + 1)) ^ (k + 1) * (k + 1 : ℕ) := by rw [pow_succ]; ring

/-- The product of the Boolean sign factors is minus one raised to the Hamming weight. -/
private theorem sign_product {n : ℕ} (x : Fin n → Bool) :
    (∏ i, if x i = true then (-1 : ℝ) else 1) = (-1 : ℝ) ^ boolWeight x := by
  classical
  simp [Finset.prod_ite, boolWeight, boolSupp]

/-- The parity-weighted Boolean-cube sum of a monomial vanishes when its support has cardinality
less than the number of variables. -/
private theorem missing_monomial_sum {n : ℕ} (d : Fin n →₀ ℕ)
    (hd : d.support.card < n) :
    (∑ x : Fin n → Bool, (-1 : ℝ) ^ boolWeight x *
      ∏ i, (if x i = true then (1 : ℝ) else 0) ^ d i) = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := d.support) (t := Finset.univ) (by simpa using hd)
  have hdi : d i = 0 := Finsupp.notMem_support_iff.mp hi
  have hprod : (∑ x : Fin n → Bool, ∏ i,
      (if x i = true then (-1 : ℝ) else 1) *
        (if x i = true then (1 : ℝ) else 0) ^ d i) =
      ∏ i, ∑ b : Bool, (if b = true then (-1 : ℝ) else 1) *
        (if b = true then (1 : ℝ) else 0) ^ d i := by
    simpa using! (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
      (fun i b => (if b = true then (-1 : ℝ) else 1) *
        (if b = true then (1 : ℝ) else 0) ^ d i)).symm
  calc
    _ = ∑ x : Fin n → Bool, ∏ i,
        (if x i = true then (-1 : ℝ) else 1) *
          (if x i = true then (1 : ℝ) else 0) ^ d i := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib, sign_product]
    _ = _ := hprod
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hdi])

/-- The parity-weighted Boolean-cube sum of a real polynomial vanishes when its total degree is
less than the number of variables. -/
private theorem low_degree_sum {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree < n) :
    (∑ x : Fin n → Bool, (-1 : ℝ) ^ boolWeight x *
      MvPolynomial.eval (fun i => if x i = true then 1 else 0) p) = 0 := by
  classical
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro d hd
  have hcard : d.support.card ≤ d.sum (fun _ e => e) := by
    calc
      d.support.card = ∑ i ∈ d.support, (1 : ℕ) := Finset.card_eq_sum_ones _
      _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i hi =>
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      _ = d.sum (fun _ e => e) := rfl
  have hdc : d.support.card < n :=
    (hcard.trans (MvPolynomial.le_totalDegree hd)).trans_lt hp
  calc
    _ = p.coeff d * ∑ x : Fin n → Bool, (-1 : ℝ) ^ boolWeight x *
          ∏ i, (if x i = true then (1 : ℝ) else 0) ^ d i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 0 := by rw [missing_monomial_sum d hdc, mul_zero]

/-- The Hamming weight of a Boolean input, viewed as an index in `Fin (n + 1)`. -/
private def weightIndex {n : ℕ} (x : Fin n → Bool) : Fin (n + 1) :=
  ⟨boolWeight x, by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun i => x i = true) (Finset.univ : Finset (Fin n)))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact Nat.lt_succ_of_le h⟩

/-- The fiber of the Hamming-weight index at `k` has cardinality `n.choose k.val`. -/
private theorem weightIndex_card {n : ℕ} (k : Fin (n + 1)) :
    Fintype.card {x : Fin n → Bool // weightIndex x = k} = n.choose k.val := by
  classical
  let e : {x : Fin n → Bool // weightIndex x = k} ≃
      {x : Fin n → Bool // boolWeight x = k.val} :=
    Equiv.subtypeEquivRight (fun _ => Fin.ext_iff)
  rw [Fintype.card_congr e]
  exact card_weight_eq_choose n (Fintype.card_fin n) k.val

/-- Every index in `Fin (n + 1)` occurs as the Hamming weight of a Boolean input. -/
private theorem weightIndex_surjective (n : ℕ) : Function.Surjective (@weightIndex n) := by
  classical
  intro k
  have hcard : 0 < Fintype.card {x : Fin n → Bool // weightIndex x = k} := by
    rw [weightIndex_card]
    exact Nat.choose_pos (by omega)
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hcard
  exact ⟨x.val, x.property⟩

/-- Regroups a parity-weighted sum of a Hamming-weight-dependent Boolean function into
binomially weighted Hamming layers. -/
private theorem sum_by_weight {n : ℕ} (a : Fin (n + 1) → Bool) :
    (∑ x : Fin n → Bool, (-1 : ℝ) ^ boolWeight x *
      (if a (weightIndex x) = true then 1 else 0)) =
    ∑ k : Fin (n + 1), (-1 : ℝ) ^ k.val * (n.choose k.val : ℝ) *
      (if a k = true then 1 else 0) := by
  classical
  have h := Fintype.sum_fiberwise' (@weightIndex n)
    (fun k => (-1 : ℝ) ^ k.val * (if a k = true then 1 else 0))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, weightIndex_card] at h
  convert! h.symm using 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- If `n + 1` is prime, a well-formed observed circuit exactly computing a nonconstant
symmetric Boolean function from a normalized state satisfies `n ≤ 2 * observedQueryDepth P`.
This is the prime case of [Beals et al., Corollary 4.7][BealsEtAl2001]. -/
theorem theorem46PrimeCaseRestricted : Theorem46PrimeCaseRestricted := by
  classical
  intro n W _ _ _ P ψ f hn hP hψ hsym hnon hp hexact
  by_contra hbound
  obtain ⟨p, hdegree, _, heval⟩ :=
    observed_actual_multilinear_acceptance_polynomial n W P ψ hn hP hψ
  choose rep hrep using weightIndex_surjective n
  let a : Fin (n + 1) → Bool := fun k => f (rep k)
  have hf (x : Fin n → Bool) : f x = a (weightIndex x) := by
    apply hsym
    exact (congrArg Fin.val (hrep (weightIndex x))).symm
  have hreal : (∑ k : Fin (n + 1), (-1 : ℝ) ^ k.val * (n.choose k.val : ℝ) *
      (if a k = true then 1 else 0)) = 0 := by
    rw [← sum_by_weight a]
    calc
      _ = ∑ x : Fin n → Bool, (-1 : ℝ) ^ boolWeight x *
          MvPolynomial.eval (fun i => if x i = true then 1 else 0) p := by
        apply Finset.sum_congr rfl
        intro x _
        rw [heval, hexact, hf]
      _ = 0 := low_degree_sum p (by omega)
  have hint : (∑ k : Fin (n + 1), (-1 : ℤ) ^ k.val * (n.choose k.val : ℤ) *
      (if a k = true then 1 else 0)) = 0 := by
    exact_mod_cast hreal
  have hzmod : (∑ k : Fin (n + 1), (-1 : ZMod (n + 1)) ^ k.val *
      (n.choose k.val : ZMod (n + 1)) * (if a k = true then 1 else 0)) = 0 := by
    have h := congrArg (Int.castRingHom (ZMod (n + 1))) hint
    simpa using h
  have hsum : (∑ k : Fin (n + 1), if a k = true then (1 : ZMod (n + 1)) else 0) = 0 := by
    convert! hzmod using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [prime_choose n hp k.val (by omega), ← mul_pow]
    simp
  let s : Finset (Fin (n + 1)) := Finset.univ.filter (fun k => a k = true)
  have hdvd : n + 1 ∣ s.card := by
    apply (ZMod.natCast_eq_zero_iff s.card (n + 1)).mp
    simpa [s] using hsum
  obtain ⟨x, y, hxy⟩ := hnon
  have hane : a (weightIndex x) ≠ a (weightIndex y) := by
    rwa [← hf x, ← hf y]
  have htrue : ∃ k, a k = true := by
    cases hx : a (weightIndex x) with
    | true => exact ⟨weightIndex x, hx⟩
    | false =>
      cases hy : a (weightIndex y) with
      | true => exact ⟨weightIndex y, hy⟩
      | false => exact False.elim (hane (hx.trans hy.symm))
  have hfalse : ∃ k, a k = false := by
    cases hx : a (weightIndex x) with
    | false => exact ⟨weightIndex x, hx⟩
    | true =>
      cases hy : a (weightIndex y) with
      | false => exact ⟨weightIndex y, hy⟩
      | true => exact False.elim (hane (hx.trans hy.symm))
  have hspos : 0 < s.card := by
    obtain ⟨k, hk⟩ := htrue
    exact Finset.card_pos.mpr ⟨k, by simp [s, hk]⟩
  have hslt : s.card < n + 1 := by
    obtain ⟨k, hk⟩ := hfalse
    have hss : s ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hmem : k ∈ s := heq.symm ▸ Finset.mem_univ k
      simp [s, hk] at hmem
    simpa using Finset.card_lt_card hss
  exact Nat.not_dvd_of_pos_of_lt hspos hslt hdvd

end Qatlib.Concepts.QueryComplexity.DegreeMethod
