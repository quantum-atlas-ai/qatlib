/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial

/-!
# Hamming-layer symmetrization and the parity degree bound

This module averages real multivariate polynomials over Boolean inputs of a fixed Hamming
weight. The polynomial `avgPoly` represents these layer averages without increasing total
degree, using counting identities and the binomial polynomials `binomPoly`.

For a polynomial approximating parity within `1 / 3`, consecutive layers force roots of the
centered average polynomial. This gives the full parity degree lower bound and the corresponding
quantum query bound from the polynomial method of [BealsEtAl2001].

## Main statements

* `layerAverage_eq_avgPoly`: Layer averages are evaluations of a univariate polynomial.
* `avgPoly_natDegree_le`: Symmetrization does not increase degree.
* `parity_boolean_approximation_degree`: Approximating parity within `1 / 3` requires degree at
  least the input size.
* `parity_actual_bounded_error_query_lower_bound`: A circuit approximating parity requires at
  least half the input size in queries.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped Classical BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The finite set of indices at which a Boolean input is true. -/
def boolSupp (f : I → Bool) : Finset I := Finset.univ.filter fun i => f i = true

/-- The Hamming weight of a Boolean input, defined as the cardinality of its true support. -/
def boolWeight (f : I → Bool) : ℕ := (boolSupp f).card

/-- The equivalence between Boolean inputs of weight `k` and finite subsets of cardinality `k`. -/
def weightEquiv' (k : ℕ) : {f : I → Bool // boolWeight f = k} ≃ {t : Finset I // t.card = k} where
  toFun f := ⟨boolSupp f.1, by
    show (boolSupp f.1).card = k
    exact f.2⟩
  invFun t := ⟨fun i => decide (i ∈ t.1), by
    have hset : boolSupp (fun i => decide (i ∈ t.1)) = t.1 := by
      ext i
      simp only [boolSupp, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    show (boolSupp (fun i => decide (i ∈ t.1))).card = k
    rw [hset]
    exact t.2⟩
  left_inv f := Subtype.ext (by
    show (fun i => decide (i ∈ boolSupp f.1)) = f.1
    funext i
    show decide (i ∈ boolSupp f.1) = f.1 i
    simp only [boolSupp, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hfi : f.1 i <;> rfl)
  right_inv t := Subtype.ext (by
    show boolSupp (fun i => decide (i ∈ t.1)) = t.1
    ext i
    simp only [boolSupp, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq])

/-- The number of Boolean inputs of weight `k` on an index type of cardinality `n` is
`Nat.choose n k`. -/
theorem card_weight_eq_choose (n : ℕ) (hn : Fintype.card I = n) (k : ℕ) :
    Fintype.card {f : I → Bool // boolWeight f = k} = Nat.choose n k := by
  have h1 : Fintype.card {f : I → Bool // boolWeight f = k}
      = Fintype.card {t : Finset I // t.card = k} := Fintype.card_congr (weightEquiv' k)
  have e2 : {t : Finset I // t.card = k} ≃ (Finset.powersetCard k Finset.univ : Finset (Finset I)) :=
    { toFun := fun t => ⟨t.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, t.2⟩⟩
      invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun s => Subtype.ext rfl }
  have h2 : Fintype.card {t : Finset I // t.card = k} = Nat.choose n k := by
    rw [Fintype.card_congr e2, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
      hn]
  rw [h1, h2]

/-- If `S` is contained in `g`, adjoining the difference `g \ S` to `S` recovers `g`. -/
theorem union_sdiff (S g : Finset I) (h : S ⊆ g) : S ∪ (g \ S) = g := by
  ext i
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hi
    rcases hi with hi' | hi'
    · exact h hi'
    · exact hi'.1
  · intro hi
    by_cases hiS : i ∈ S
    · exact Or.inl hiS
    · exact Or.inr ⟨hi, hiS⟩

/-- A finite subset of the complement of `S` is unchanged by removing `S`. -/
theorem sdiff_eq_of_subset (S g : Finset I) (hg : g ⊆ Finset.univ \ S) :
    g \ S = g := by
  ext i
  rw [Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hi
    exact ⟨hi, (Finset.mem_sdiff.mp (hg hi)).2⟩

/-- Removing `S` from `S ∪ g` recovers `g` when `g` lies in the complement of `S`. -/
theorem sdiff_union_left (S g : Finset I) (hg : g ⊆ Finset.univ \ S) :
    (S ∪ g) \ S = g := by
  ext i
  rw [Finset.mem_sdiff]
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi.1 with hiS | hiG
    · exact absurd hiS hi.2
    · exact hiG
  · intro hi
    exact ⟨Finset.mem_union_right _ hi, (Finset.mem_sdiff.mp (hg hi)).2⟩

/-- Identifies cardinality-`k` supersets of `S` with cardinality-`k - S.card` subsets of the
complement of `S`, assuming `S.card ≤ k`. -/
noncomputable def aboveEquiv (k : ℕ) (S : Finset I) (h : S.card ≤ k) :
    {t : Finset I // t.card = k ∧ S ⊆ t} ≃
      {u : Finset I // u.card = k - S.card ∧ u ⊆ Finset.univ \ S} :=
  let above : {t : Finset I // t.card = k ∧ S ⊆ t} →
      {u : Finset I // u.card = k - S.card ∧ u ⊆ Finset.univ \ S} :=
    fun t => Subtype.mk (t.1 \ S) (And.intro
      ((Finset.card_sdiff_of_subset t.2.2).trans (by omega))
      (fun i hi => Finset.mem_sdiff.mpr
        ⟨(Finset.mem_univ i : i ∈ (Finset.univ : Finset I)),
          (Finset.mem_sdiff.mp hi).2⟩))
  Equiv.ofBijective above
    (And.intro
      (fun a₁ a₂ hEq => Subtype.ext (by
        have hv : a₁.1 \ S = a₂.1 \ S := Subtype.ext_iff.mp hEq
        calc a₁.1 = S ∪ (a₁.1 \ S) := (union_sdiff S a₁.1 a₁.2.2).symm
          _ = S ∪ (a₂.1 \ S) := by rw [hv]
          _ = a₂.1 := union_sdiff S a₂.1 a₂.2.2))
      (fun u => Exists.intro
        (Subtype.mk (S ∪ u.1) (And.intro
          (by
            have hd : Disjoint S u.1 := Finset.disjoint_left.2 (fun a haS haU =>
              (Finset.mem_sdiff.mp (u.2.2 haU)).2 haS)
            rw [Finset.card_union_of_disjoint hd, u.2.1]
            omega)
          (fun i hi => by
            show i ∈ (S ∪ u.1 : Finset I)
            exact Finset.mem_union.mpr
              (show i ∈ S ∨ i ∈ (u.1 : Finset I) from Or.inl hi))))
        (by
          apply Subtype.ext
          exact sdiff_union_left S u.1 (fun i hi =>
            Finset.mem_sdiff.mpr (Finset.mem_sdiff.mp (u.2.2 hi))))))

/-- The number of cardinality-`k` subsets of the finite index type is the corresponding binomial
coefficient. -/
theorem card_level_finset (k : ℕ) :
    Fintype.card {t : Finset I // t.card = k} = Nat.choose (Fintype.card I) k := by
  rw [Fintype.card_congr (weightEquiv' k).symm, card_weight_eq_choose _ rfl k]

/-- The number of cardinality-`k` finite subsets contained in `J` is `Nat.choose J.card k`. -/
theorem card_level_subset (J : Finset I) (k : ℕ) :
    Fintype.card {t : Finset I // t.card = k ∧ t ⊆ J} = Nat.choose J.card k := by
  have e : {t : Finset I // t.card = k ∧ t ⊆ J} ≃
      (Finset.powersetCard k J : Finset (Finset I)) :=
    { toFun := fun t => ⟨t.1, Finset.mem_powersetCard.mpr ⟨t.2.2, t.2.1⟩⟩
      invFun := fun s =>
        ⟨s.1, (Finset.mem_powersetCard.mp s.2).2, (Finset.mem_powersetCard.mp s.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard]

/-- Counts the cardinality-`k` subsets containing `S` by choosing the remaining elements outside
`S`. -/
theorem card_level_containing (k : ℕ) (S : Finset I) (h : S.card ≤ k) :
    Fintype.card {t : Finset I // t.card = k ∧ S ⊆ t}
      = Nat.choose (Fintype.card I - S.card) (k - S.card) := by
  have h1 : Fintype.card {t : Finset I // t.card = k ∧ S ⊆ t}
      = Fintype.card {u : Finset I // u.card = k - S.card ∧ u ⊆ Finset.univ \ S} :=
    Fintype.card_congr (aboveEquiv k S h)
  have h2 : Fintype.card {u : Finset I // u.card = k - S.card ∧ u ⊆ Finset.univ \ S}
      = Nat.choose (Fintype.card I - S.card) (k - S.card) := by
    have hcard : (Finset.univ \ S).card = Fintype.card I - S.card := by
      rw [Finset.card_sdiff, Finset.card_univ]
      simp
    exact (card_level_subset (Finset.univ \ S) (k - S.card)).trans (by rw [hcard])
  rw [h1, h2]

/-- Expresses the real cast of `n!` as the product of the first `n` positive integers. -/
theorem natFactorial_eq_prod (n : ℕ) :
    (Nat.factorial n : ℝ) = ∏ i ∈ Finset.range n, ((i : ℝ) + 1) := by
  exact_mod_cast Nat.factorial_eq_prod_range_add_one n

/-- Expresses the real binomial coefficient as a falling-factorial product divided by `s!`. -/
theorem choose_eq_falling (k s : ℕ) :
    (Nat.choose k s : ℝ) = (∏ u ∈ Finset.range s, ((k : ℝ) - u)) * (Nat.factorial s : ℝ)⁻¹ := by
  by_cases hs : s ≤ k
  · have hprod : (k.descFactorial s : ℝ) = ∏ u ∈ Finset.range s, ((k : ℝ) - u) := by
      have hh : (k.descFactorial s : ℝ) = ((∏ i ∈ Finset.range s, (k - i)) : ℕ) := by
        rw [Nat.descFactorial_eq_prod_range]
      rw [hh, Nat.cast_prod]
      refine Finset.prod_congr (s₂ := Finset.range s) rfl ?_
      intro u hu
      rw [Nat.cast_sub]
      have hlt : u < s := Finset.mem_range.mp hu
      omega
    have h1 : (Nat.choose k s : ℝ) * (Nat.factorial s : ℝ) * ((k - s).factorial : ℝ)
        = (Nat.factorial k : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hs
    have h2 : ((k - s).factorial : ℝ) * (k.descFactorial s : ℝ) = (Nat.factorial k : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hs
    have h12 : ((Nat.choose k s : ℝ) * (Nat.factorial s : ℝ)) * ((k - s).factorial : ℝ)
        = (k.descFactorial s : ℝ) * ((k - s).factorial : ℝ) := by
      calc (Nat.choose k s : ℝ) * (Nat.factorial s : ℝ) * ((k - s).factorial : ℝ)
          = (Nat.factorial k : ℝ) := h1
        _ = (k.descFactorial s : ℝ) * ((k - s).factorial : ℝ) := by rw [← h2, mul_comm]
    rw [← hprod, ← mul_right_cancel₀ (by positivity) h12, mul_assoc,
      mul_inv_cancel₀ (by positivity), mul_one]
  · have hC0 : Nat.choose k s = 0 := by
      have hlt : k < s := by omega
      exact Nat.choose_eq_zero_of_lt hlt
    have hC : (Nat.choose k s : ℝ) = 0 := by
      rw [hC0]
      norm_num
    have hz : ∏ u ∈ Finset.range s, ((k : ℝ) - u) = 0 := by
      rw [Finset.prod_eq_zero (i := k) (Finset.mem_range.mpr (by omega))]
      norm_num
    rw [hC, hz, zero_mul]

/-- The degree of a finite product of real polynomials is at most the sum of their degrees. -/
private theorem natDegree_prod_le {ι : Type} (s : Finset ι) (f : ι → Polynomial ℝ) :
    (s.prod f).natDegree ≤ s.sum fun i => (f i).natDegree := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact le_trans Polynomial.natDegree_mul_le
        (Nat.add_le_add_left ih (f a).natDegree)

/-- A finite sum of real polynomials has degree at most a common bound on the summands' degrees. -/
private theorem natDegree_sum_le {ι : Type} {s : Finset ι} {f : ι → Polynomial ℝ} {M : ℕ}
    (hM : ∀ i ∈ s, (f i).natDegree ≤ M) : (s.sum f).natDegree ≤ M := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (Polynomial.natDegree_add_le _ _)
        (Nat.max_le.mpr ⟨hM a (Finset.mem_insert_self a s),
          ih fun i hi => hM i (Finset.mem_insert_of_mem hi)⟩)

/-- The real polynomial given by the falling factorial of length `s` divided by `s!`. -/
noncomputable def binomPoly (s : ℕ) : Polynomial ℝ :=
  Polynomial.C (Nat.factorial s : ℝ)⁻¹ *
    (∏ u ∈ Finset.range s, (Polynomial.X - Polynomial.C (u : ℝ)))

/-- The binomial polynomial of order zero is the constant polynomial one. -/
@[simp] theorem binomPoly_zero : binomPoly 0 = 1 := by
  simp [binomPoly]

/-- Evaluating the order-`s` binomial polynomial at a natural number `k` gives `Nat.choose k s`. -/
theorem binomPoly_eval (s k : ℕ) : (binomPoly s).eval (k : ℝ) = (Nat.choose k s : ℝ) := by
  rw [binomPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [mul_comm, ← choose_eq_falling k s]

/-- The order-`s` binomial polynomial has degree at most `s`. -/
theorem binomPoly_natDegree_le (s : ℕ) : (binomPoly s).natDegree ≤ s := by
  have h0 : ((Nat.factorial s : ℝ)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (by positivity)
  have hp := natDegree_prod_le (Finset.range s) (fun u => Polynomial.X - Polynomial.C (u : ℝ))
  have hsum : (∑ i ∈ Finset.range s, (Polynomial.X - Polynomial.C (i : ℝ)).natDegree)
      = ∑ _i ∈ Finset.range s, (1 : ℕ) := by
    exact Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_sub_C (i : ℝ)
  rw [hsum] at hp
  rw [binomPoly, Polynomial.natDegree_C_mul h0]
  simpa using hp

/-- Boolean inputs of weight `k` whose true support contains `S`. -/
abbrev WeightCont (S : Finset I) (k : ℕ) : Type :=
  {f : I → Bool // boolWeight f = k ∧ S ⊆ boolSupp f}

/-- Embeds a Boolean input into real coordinates by sending false to zero and true to one. -/
def boolPoint (f : I → Bool) : I → ℝ := fun i => if f i = true then 1 else 0

/-- An index belongs to the true support exactly when its input bit is true. -/
theorem boolSupp_mem_iff (f : I → Bool) (i : I) : i ∈ boolSupp f ↔ f i = true := by
  simp only [boolSupp, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A monomial evaluated on a Boolean point is one exactly when its exponent support is
contained in the true support, and zero otherwise. -/
theorem eval_monomial_indicator (m : I →₀ ℕ) (f : I → Bool) :
    (∏ i, (boolPoint f i) ^ m i) = if m.support ⊆ boolSupp f then 1 else 0 := by
  classical
  have h1 : (∏ i, (boolPoint f i) ^ m i) = ∏ i ∈ m.support, (boolPoint f i) ^ m i := by
    have hone : ∀ i ∈ (Finset.univ \ m.support : Finset I), (boolPoint f i) ^ m i = 1 := by
      intro i hi
      have hmi : m i = 0 := by
        by_contra hc
        exact (Finset.mem_sdiff.mp hi).2 (Finsupp.mem_support_iff.mpr hc)
      rw [hmi, pow_zero]
    show (∏ i ∈ (Finset.univ : Finset I),
        (boolPoint f i) ^ m i) = ∏ i ∈ m.support, (boolPoint f i) ^ m i
    rw [← Finset.prod_sdiff (M := ℝ) (f := fun i => (boolPoint f i) ^ m i)
      (Finset.subset_univ _), Finset.prod_eq_one hone, one_mul]
  have h2 : (∏ i ∈ m.support, (boolPoint f i) ^ m i)
      = if m.support ⊆ boolSupp f then 1 else 0 := by
    by_cases hsub : m.support ⊆ boolSupp f
    · rw [if_pos hsub]
      have hall : ∀ i ∈ m.support, (boolPoint f i) ^ m i = 1 := by
        intro i hi
        have hf : f i = true := (boolSupp_mem_iff f i).mp (hsub hi)
        rw [boolPoint, if_pos hf, one_pow]
      exact Finset.prod_eq_one hall
    · rw [if_neg hsub]
      obtain ⟨i, hiS, hiNS⟩ := Finset.not_subset.mp hsub
      have hf : f i ≠ true := fun h => hiNS ((boolSupp_mem_iff f i).mpr h)
      have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hiS
      have hz : (boolPoint f i) ^ m i = 0 := by
        simp only [boolPoint, if_neg hf]
        have hone : m i = (m i - 1) + 1 := by omega
        rw [hone, pow_succ, mul_zero]
      exact Finset.prod_eq_zero (f := fun i => (boolPoint f i) ^ m i) (s := m.support)
        (i := i) hiS hz
  rw [h1, h2]

/-- The true support of the membership indicator of a finite set is that set. -/
theorem boolSupp_decide (t : Finset I) : boolSupp (fun i => decide (i ∈ t)) = t := by
  ext i
  simp only [boolSupp, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- Converting a cardinality-`k` finite set back to a weight-`k` input preserves its support. -/
theorem boolSupp_invFun (k : ℕ) (t : {t : Finset I // t.card = k}) :
    boolSupp ((weightEquiv' k).invFun t).1 = t.1 := by
  show boolSupp (fun i => decide (i ∈ t.1)) = t.1
  exact boolSupp_decide t.1

/-- Counts weight-`k` Boolean inputs whose support contains `S` using the ratio of the
corresponding binomial coefficients, when `k` and `S.card` do not exceed the input size. -/
theorem card_containing_real (S : Finset I) (k : ℕ) (hk : k ≤ Fintype.card I)
    (hS : S.card ≤ Fintype.card I) :
    (Fintype.card {f : I → Bool // boolWeight f = k ∧ S ⊆ boolSupp f} : ℝ)
      = (Nat.choose (Fintype.card I) k : ℝ) * (Nat.choose k S.card : ℝ)
        * (Nat.choose (Fintype.card I) S.card : ℝ)⁻¹ := by
  classical
  by_cases hs : S.card ≤ k
  · have e : {f : I → Bool // boolWeight f = k ∧ S ⊆ boolSupp f} ≃
        {t : Finset I // t.card = k ∧ S ⊆ t} :=
      let map : {f : I → Bool // boolWeight f = k ∧ S ⊆ boolSupp f} →
          {t : Finset I // t.card = k ∧ S ⊆ t} :=
        fun f => Subtype.mk (boolSupp f.1) (And.intro f.2.1 f.2.2)
      Equiv.ofBijective map (And.intro
        (fun a₁ a₂ hEq => Subtype.ext (by
          have hv : boolSupp a₁.1 = boolSupp a₂.1 := Subtype.ext_iff.mp hEq
          have hv' : a₁.1 = a₂.1 := by
            funext i
            have hmem := Finset.ext_iff.mp hv i
            simp only [boolSupp_mem_iff] at hmem
            cases ha : a₁.1 i <;> cases hb : a₂.1 i <;> simp_all
          exact hv'))
        (fun t => Exists.intro
          (Subtype.mk ((weightEquiv' k).invFun ⟨t.1, t.2.1⟩).1
            (And.intro ((weightEquiv' k).invFun ⟨t.1, t.2.1⟩).2 (by
              show S ⊆ boolSupp ((weightEquiv' k).invFun ⟨t.1, t.2.1⟩).1
              rw [boolSupp_invFun k ⟨t.1, t.2.1⟩]
              exact t.2.2)))
          (Subtype.ext (boolSupp_invFun k ⟨t.1, t.2.1⟩))))
    have hcount : Fintype.card {f : I → Bool // boolWeight f = k ∧ S ⊆ boolSupp f}
        = Nat.choose (Fintype.card I - S.card) (k - S.card) := by
      rw [Fintype.card_congr e, card_level_containing k S hs]
    have hmul : (Nat.choose (Fintype.card I) k : ℝ) * (Nat.choose k S.card : ℝ)
        = (Nat.choose (Fintype.card I) S.card : ℝ)
          * (Nat.choose (Fintype.card I - S.card) (k - S.card) : ℝ) := by
      have hh := congrArg (fun m : ℕ => (m : ℝ))
        (Nat.choose_mul (n := Fintype.card I) (k := k) (s := S.card) hs)
      push_cast at hh
      exact hh
    have hpos0 : (0 : ℝ) < (Nat.choose (Fintype.card I) S.card : ℝ) := by
      exact_mod_cast Nat.choose_pos hS
    have hden : (Nat.choose (Fintype.card I) S.card : ℝ) ≠ 0 := ne_of_gt hpos0
    rw [hcount, hmul]
    field_simp [hden]
  · have hzero : Fintype.card {f : I → Bool // boolWeight f = k ∧ S ⊆ boolSupp f} = 0 := by
      refine Fintype.card_eq_zero_iff.mpr ⟨fun f => ?_⟩
      have hsub : S.card ≤ (boolSupp f.1).card := Finset.card_le_card f.2.2
      exact absurd (hsub.trans_eq f.2.1) hs
    have hcz : Nat.choose k S.card = 0 := by
      have hlt : k < S.card := by omega
      exact Nat.choose_eq_zero_of_lt hlt
    rw [hzero, Nat.cast_zero, hcz, Nat.cast_zero, mul_zero, zero_mul]

/-- A constant factor can be pulled out of a sum over a finite type. -/
private theorem fintype_mul_sum {X : Type} [Fintype X] (c : ℝ) (h : X → ℝ) :
    (∑ x : X, c * h x) = c * ∑ x : X, h x := by
  show (∑ x ∈ (Finset.univ : Finset X), c * h x) = c * ∑ x ∈ (Finset.univ : Finset X), h x
  exact (Finset.mul_sum (R := ℝ) _ _ _).symm

/-- The sum of monomial-support indicators on a Hamming layer equals the number of inputs in
that layer containing the support. -/
theorem layer_indicator_sum (m : I →₀ ℕ) (k : ℕ) :
    (∑ f : {f : I → Bool // boolWeight f = k}, (if m.support ⊆ boolSupp f then (1 : ℝ) else 0))
      = (Fintype.card {f : I → Bool // boolWeight f = k ∧ m.support ⊆ boolSupp f} : ℝ) := by
  classical
  have hmem : ∀ f : I → Bool,
      f ∈ (Finset.univ.filter fun f : I → Bool => boolWeight f = k ∧ m.support ⊆ boolSupp f)
        ↔ (boolWeight f = k ∧ m.support ⊆ boolSupp f) := by
    intro f
    simp
  have hmem0 : ∀ f : I → Bool,
      f ∈ (Finset.univ.filter fun f : I → Bool => boolWeight f = k) ↔ boolWeight f = k := by
    intro f
    simp
  have hfilter : ((Finset.univ.filter fun f : I → Bool => boolWeight f = k).filter
      fun f : I → Bool => m.support ⊆ boolSupp f)
      = (Finset.univ.filter fun f : I → Bool => boolWeight f = k ∧ m.support ⊆ boolSupp f) := by
    ext f
    simp
  have h0 := Finset.sum_subtype (F := inferInstance)
    (s := (Finset.univ.filter fun f : I → Bool => boolWeight f = k))
    hmem0 (fun f => (if m.support ⊆ boolSupp f then (1 : ℝ) else 0))
  have h1 := Finset.sum_subtype (F := inferInstance)
    (s := (Finset.univ.filter fun f : I → Bool => boolWeight f = k ∧ m.support ⊆ boolSupp f))
    hmem (fun _ => (1 : ℝ))
  have h2 := Finset.sum_boole (R := ℝ) (fun f : I → Bool => m.support ⊆ boolSupp f)
    ((Finset.univ.filter fun f : I → Bool => boolWeight f = k) : Finset (I → Bool))
  have hone : (∑ a : {f : I → Bool // boolWeight f = k ∧ m.support ⊆ boolSupp f}, (1 : ℝ))
      = (Fintype.card {f : I → Bool // boolWeight f = k ∧ m.support ⊆ boolSupp f} : ℝ) := by
    simp
  rw [← hone, ← h1, ← h0, h2, hfilter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_eq_sum_ones]

/-- The sum of a real polynomial's evaluations over the Boolean Hamming layer of weight `k`. -/
noncomputable def layerSum (p : MvPolynomial I ℝ) (k : ℕ) : ℝ :=
  ∑ f : {f : I → Bool // boolWeight f = k}, p.eval (boolPoint f.1)

/-- The Hamming-layer sum divided by the binomial coefficient counting that layer. -/
noncomputable def layerAverage (p : MvPolynomial I ℝ) (k : ℕ) : ℝ :=
  layerSum p k * (Nat.choose (Fintype.card I) k : ℝ)⁻¹

/-- The univariate polynomial formed by replacing each monomial with its normalized support-size
binomial polynomial. -/
noncomputable def avgPoly (p : MvPolynomial I ℝ) : Polynomial ℝ :=
  p.support.sum fun m : I →₀ ℕ =>
    Polynomial.C (p.coeff m)
      * Polynomial.C (Nat.choose (Fintype.card I) m.support.card : ℝ)⁻¹
      * binomPoly m.support.card

/-- On each layer with weight at most the input size, the layer average equals evaluation of
`avgPoly` at that weight. -/
theorem layerAverage_eq_avgPoly (p : MvPolynomial I ℝ) (k : ℕ) (hk : k ≤ Fintype.card I) :
    layerAverage p k = (avgPoly p).eval (k : ℝ) := by
  classical
  have h1 : ∀ f : I → Bool, p.eval (boolPoint f)
      = ∑ am ∈ p.support, (p.coeff am : ℝ)
          * (∏ i, (boolPoint f i) ^ am i) := by
    intro f
    exact MvPolynomial.eval_eq' _ _
  have hcard : ∀ am : I →₀ ℕ, am.support.card ≤ Fintype.card I :=
    fun am => Finset.card_le_univ _
  have hck : (Nat.choose (Fintype.card I) k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  calc layerAverage p k
      = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ * (∑ f : {f : I → Bool // boolWeight f = k}, ∑ am ∈ p.support,
          (p.coeff am : ℝ) * (∏ i, (boolPoint f.1 i) ^ am i)) := by
          rw [layerAverage, layerSum,
            Finset.sum_congr (M := ℝ) rfl fun f _ => h1 f.1]
          ring
    _ = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ * (∑ am ∈ p.support, ∑ f : {f : I → Bool // boolWeight f = k},
          (p.coeff am : ℝ) * (∏ i, (boolPoint f.1 i) ^ am i)) := by
          congr 1
          exact Finset.sum_comm
    _ = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ * (∑ am ∈ p.support, (p.coeff am : ℝ) *
          (∑ f : {f : I → Bool // boolWeight f = k}, (∏ i, (boolPoint f.1 i) ^ am i))) := by
          congr 1
          refine Finset.sum_congr rfl fun am _ => ?_
          exact fintype_mul_sum _ _
    _ = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ * (∑ am ∈ p.support, (p.coeff am : ℝ) *
          (Fintype.card {f : I → Bool // boolWeight f = k ∧ am.support ⊆ boolSupp f} : ℝ)) := by
          congr 1
          refine Finset.sum_congr rfl fun am _ => ?_
          have hkey : (∑ f : {f : I → Bool // boolWeight f = k},
                (∏ i, (boolPoint f.1 i) ^ am i))
              = (Fintype.card {f : I → Bool // boolWeight f = k ∧ am.support ⊆ boolSupp f} : ℝ) := by
            rw [← layer_indicator_sum]
            refine Finset.sum_congr (M := ℝ) rfl fun f _ => ?_
            exact eval_monomial_indicator am f.1
          rw [hkey]
    _ = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ * (∑ am ∈ p.support, (p.coeff am : ℝ) *
          (Nat.choose (Fintype.card I) k : ℝ) * (Nat.choose k am.support.card : ℝ)
            * (Nat.choose (Fintype.card I) am.support.card : ℝ)⁻¹) := by
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl fun am ham => ?_
          rw [card_containing_real am.support k hk (hcard am)]
          ring
    _ = ∑ am ∈ p.support, (p.coeff am : ℝ) *
          (Nat.choose (Fintype.card I) am.support.card : ℝ)⁻¹
            * (Nat.choose k am.support.card : ℝ) := by
          have hh := Finset.mul_sum (R := ℝ) (p.support)
            (fun am : I →₀ ℕ => (p.coeff am : ℝ) *
              (Nat.choose (Fintype.card I) k : ℝ) * (Nat.choose k am.support.card : ℝ)
                * (Nat.choose (Fintype.card I) am.support.card : ℝ)⁻¹)
            (Nat.choose (Fintype.card I) k : ℝ)⁻¹
          rw [hh]
          refine Finset.sum_congr rfl fun am _ => ?_
          have hCk : ((Nat.choose (Fintype.card I) k : ℝ)⁻¹ * (Nat.choose (Fintype.card I) k : ℝ)) = 1 :=
            inv_mul_cancel₀ hck
          calc (Nat.choose (Fintype.card I) k : ℝ)⁻¹ *
                (p.coeff am * (Nat.choose (Fintype.card I) k : ℝ) *
                  (Nat.choose k am.support.card : ℝ) *
                  (Nat.choose (Fintype.card I) am.support.card : ℝ)⁻¹)
              = ((Nat.choose (Fintype.card I) k : ℝ)⁻¹ * (Nat.choose (Fintype.card I) k : ℝ)) *
                  ((p.coeff am : ℝ) * (Nat.choose k am.support.card : ℝ) *
                    (Nat.choose (Fintype.card I) am.support.card : ℝ)⁻¹) := by ring
            _ = 1 * ((p.coeff am : ℝ) * (Nat.choose k am.support.card : ℝ) *
                (Nat.choose (Fintype.card I) am.support.card : ℝ)⁻¹) := by rw [hCk]
            _ = (p.coeff am : ℝ) * (Nat.choose (Fintype.card I) am.support.card : ℝ)⁻¹
                * (Nat.choose k am.support.card : ℝ) := by ring
    _ = (avgPoly p).eval (k : ℝ) := by
          rw [avgPoly, Polynomial.eval_finsetSum]
          refine Finset.sum_congr (M := ℝ) rfl fun am _ => ?_
          rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
            binomPoly_eval]

/-- The support size of an exponent occurring in a polynomial is bounded by the polynomial's
total degree. -/
private theorem support_card_le_totalDegree (p : MvPolynomial I ℝ) (m : I →₀ ℕ)
    (hm : m ∈ p.support) : m.support.card ≤ p.totalDegree := by
  refine le_trans ?_ (MvPolynomial.le_totalDegree hm)
  calc m.support.card = ∑ i ∈ m.support, (1 : ℕ) := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ m.support, m i := Finset.sum_le_sum fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ = m.sum fun _ e => e := rfl

/-- The degree of the univariate layer-average polynomial is at most the original polynomial's
total degree. -/
theorem avgPoly_natDegree_le (p : MvPolynomial I ℝ) : (avgPoly p).natDegree ≤ p.totalDegree := by
  refine natDegree_sum_le fun m hm => ?_
  have hne : (p.coeff m : ℝ) ≠ 0 := Finsupp.mem_support_iff.mp hm
  have hnd : (Polynomial.C (p.coeff m) * Polynomial.C
      (Nat.choose (Fintype.card I) m.support.card : ℝ)⁻¹
        * binomPoly m.support.card).natDegree ≤ m.support.card := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C_mul hne, Polynomial.natDegree_C, Nat.zero_add]
    exact binomPoly_natDegree_le _
  exact le_trans hnd (support_card_le_totalDegree p m hm)

/-- The absolute value of a finite real sum is at most the sum of the absolute values. -/
private theorem fintype_abs_sum_le {X : Type} [Fintype X] (h : X → ℝ) :
    |∑ x : X, h x| ≤ ∑ x : X, |h x| := by
  show |∑ x ∈ (Finset.univ : Finset X), h x| ≤ ∑ x ∈ (Finset.univ : Finset X), |h x|
  exact Finset.abs_sum_le_sum_abs _ _

/-- Pointwise comparison of real functions implies comparison of their sums over a finite type. -/
private theorem fintype_sum_le {X : Type} [Fintype X] {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    (∑ x : X, f x) ≤ ∑ x : X, g x := by
  show (∑ x ∈ (Finset.univ : Finset X), f x) ≤ ∑ x ∈ (Finset.univ : Finset X), g x
  exact Finset.sum_le_sum fun x _ => h x

/-- The real parity value of a layer, equal to one for odd weight and zero for even weight. -/
def layerParity (k : ℕ) : ℝ := if k % 2 = 1 then 1 else 0

/-- The real cardinality of the weight-`k` Boolean layer is the corresponding binomial
coefficient. -/
theorem card_level_real (k : ℕ) :
    (Fintype.card {f : I → Bool // boolWeight f = k} : ℝ) = Nat.choose (Fintype.card I) k := by
  exact_mod_cast (card_weight_eq_choose (Fintype.card I) rfl k)

/-- Uniform approximation of parity within `1 / 3` on the Boolean cube implies the same
approximation by each valid layer average. -/
theorem layerAverage_close (p : MvPolynomial I ℝ) (k : ℕ) (hk : k ≤ Fintype.card I)
    (hyp : ∀ f : I → Bool,
      |p.eval (boolPoint f) - (if boolWeight f % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3) :
    |layerAverage p k - layerParity k| ≤ 1 / 3 := by
  have hck : (Nat.choose (Fintype.card I) k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  have hckpos : (0 : ℝ) < (Nat.choose (Fintype.card I) k : ℝ) := lt_of_le_of_ne
    (le_of_lt (Nat.cast_pos.mpr (Nat.choose_pos hk))) (Ne.symm hck)
  have hA : layerAverage p k - layerParity k
      = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ *
        (∑ f : {f : I → Bool // boolWeight f = k},
          (p.eval (boolPoint f.1) - layerParity k)) := by
    have key : (∑ f : {f : I → Bool // boolWeight f = k},
        (p.eval (boolPoint f.1) - layerParity k))
        = (∑ f : {f : I → Bool // boolWeight f = k}, p.eval (boolPoint f.1))
          - (Nat.choose (Fintype.card I) k : ℝ) * layerParity k := by
      show (∑ f ∈ (Finset.univ : Finset {f : I → Bool // boolWeight f = k}),
          (p.eval (boolPoint f.1) - layerParity k)) = _
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_level_real k]
    rw [layerAverage, layerSum, key]
    field_simp [hck]
  have hterm : ∀ f : {f : I → Bool // boolWeight f = k},
      |p.eval (boolPoint f.1) - layerParity k| ≤ 1 / 3 := by
    intro f
    have h1 : boolWeight f.1 = k := f.2
    have h := hyp f.1
    rw [h1] at h
    exact h
  rw [hA]
  calc |(Nat.choose (Fintype.card I) k : ℝ)⁻¹ *
        (∑ f : {f : I → Bool // boolWeight f = k}, (p.eval (boolPoint f.1) - layerParity k))|
      = |(Nat.choose (Fintype.card I) k : ℝ)⁻¹| *
        |∑ f : {f : I → Bool // boolWeight f = k}, (p.eval (boolPoint f.1) - layerParity k)| := abs_mul _ _
    _ ≤ |(Nat.choose (Fintype.card I) k : ℝ)⁻¹| *
        ∑ f : {f : I → Bool // boolWeight f = k}, |p.eval (boolPoint f.1) - layerParity k| :=
      mul_le_mul_of_nonneg_left (fintype_abs_sum_le _) (abs_nonneg _)
    _ = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ *
        ∑ f : {f : I → Bool // boolWeight f = k}, |p.eval (boolPoint f.1) - layerParity k| := by
      rw [abs_of_pos (inv_pos.mpr hckpos)]
    _ ≤ (Nat.choose (Fintype.card I) k : ℝ)⁻¹ *
        ∑ _f : {f : I → Bool // boolWeight f = k}, (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left (fintype_sum_le hterm) (le_of_lt (inv_pos.mpr hckpos))
    _ = (Nat.choose (Fintype.card I) k : ℝ)⁻¹ *
        ((Fintype.card {f : I → Bool // boolWeight f = k} : ℝ) * (1 / 3 : ℝ)) := by
      congr 1
      show (∑ _f ∈ (Finset.univ : Finset {f : I → Bool // boolWeight f = k}), (1 / 3 : ℝ))
        = (Fintype.card {f : I → Bool // boolWeight f = k} : ℝ) * (1 / 3)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 / 3 := by rw [card_level_real k]; field_simp [hck]

/-- On a valid even-parity layer, the symmetrized approximation minus one half is strictly
negative. -/
theorem eval_sub_half_neg (p : MvPolynomial I ℝ) (k : ℕ) (hk : k ≤ Fintype.card I)
    (hyp : ∀ f : I → Bool,
      |p.eval (boolPoint f) - (if boolWeight f % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3)
    (hpar : layerParity k = 0) :
    (avgPoly p).eval (k : ℝ) - 1 / 2 < 0 := by
  have h1 := layerAverage_close p k hk hyp
  rw [layerAverage_eq_avgPoly p k hk, hpar, sub_zero] at h1
  have h2 := le_abs_self ((avgPoly p).eval (k : ℝ))
  linarith

/-- On a valid odd-parity layer, the symmetrized approximation minus one half is strictly
positive. -/
theorem eval_sub_half_pos (p : MvPolynomial I ℝ) (k : ℕ) (hk : k ≤ Fintype.card I)
    (hyp : ∀ f : I → Bool,
      |p.eval (boolPoint f) - (if boolWeight f % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3)
    (hpar : layerParity k = 1) :
    (avgPoly p).eval (k : ℝ) - 1 / 2 > 0 := by
  have h1 := layerAverage_close p k hk hyp
  rw [layerAverage_eq_avgPoly p k hk, hpar] at h1
  have h2 := neg_le_abs ((avgPoly p).eval (k : ℝ) - 1)
  linarith

/-- A polynomial approximating parity within `1 / 3` has a root of its centered layer average
strictly between each pair of consecutive valid integer weights. -/
theorem root_between (p : MvPolynomial I ℝ) (k : ℕ) (hk : k < Fintype.card I)
    (hyp : ∀ f : I → Bool,
      |p.eval (boolPoint f) - (if boolWeight f % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3) :
    ∃ c : ℝ, c ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) ∧
      (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).eval c = 0 := by
  have hk' : k ≤ Fintype.card I := le_of_lt hk
  have hk1 : k + 1 ≤ Fintype.card I := by omega
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by rw [Nat.cast_succ]; linarith
  have hcont : ContinuousOn (fun t : ℝ => (avgPoly p).eval t)
      (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := (Polynomial.continuous _).continuousOn
  have hsign : (1 / 2 < (avgPoly p).eval (k : ℝ) ∧
        (avgPoly p).eval ((k + 1 : ℕ) : ℝ) < 1 / 2) ∨
      ((avgPoly p).eval (k : ℝ) < 1 / 2 ∧ 1 / 2 < (avgPoly p).eval ((k + 1 : ℕ) : ℝ)) := by
    by_cases hk2 : k % 2 = 1
    · have hA0 : layerParity k = 1 := by simp [layerParity, hk2]
      have hA1 : layerParity (k + 1) = 0 := by
        have hk3 : (k + 1) % 2 = 0 := by omega
        simp [layerParity, hk3]
      have hLo := eval_sub_half_pos p k hk' hyp hA0
      have hHi := eval_sub_half_neg p (k + 1) hk1 hyp hA1
      exact Or.inl ⟨by linarith, by linarith⟩
    · have hA0 : layerParity k = 0 := by
        have hk3 : k % 2 = 0 := by omega
        simp [layerParity, hk3]
      have hA1 : layerParity (k + 1) = 1 := by
        have hk3 : (k + 1) % 2 = 1 := by omega
        simp [layerParity, hk3]
      have hLo := eval_sub_half_neg p k hk' hyp hA0
      have hHi := eval_sub_half_pos p (k + 1) hk1 hyp hA1
      exact Or.inr ⟨by linarith, by linarith⟩
  have himg : (1 / 2 : ℝ) ∈ (fun t : ℝ => (avgPoly p).eval t) ''
      Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    rcases hsign with ⟨hfk, hfk1⟩ | ⟨hfk, hfk1⟩
    · exact (intermediate_value_Icc' hle hcont) (show (1 / 2 : ℝ) ∈
        Set.Icc ((avgPoly p).eval ((k + 1 : ℕ) : ℝ)) ((avgPoly p).eval (k : ℝ)) from
          Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    · exact (intermediate_value_Icc hle hcont) (show (1 / 2 : ℝ) ∈
        Set.Icc ((avgPoly p).eval (k : ℝ)) ((avgPoly p).eval ((k + 1 : ℕ) : ℝ)) from
          Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨c, hc, hcv⟩ := himg
  dsimp only at hcv
  rcases hsign with ⟨hfk, hfk1⟩ | ⟨hfk, hfk1⟩
  · refine ⟨c, ?_, ?_⟩
    · rw [Set.mem_Ioo]
      have hc' : (k : ℝ) ≤ c ∧ c ≤ ((k + 1 : ℕ) : ℝ) := hc
      have hne1 : c ≠ (k : ℝ) := by
        intro h
        rw [h] at hcv
        linarith
      have hne2 : c ≠ ((k + 1 : ℕ) : ℝ) := by
        intro h
        rw [h] at hcv
        linarith
      exact ⟨hc'.1.lt_of_ne hne1.symm, hc'.2.lt_of_ne hne2⟩
    · rw [Polynomial.eval_sub, hcv, Polynomial.eval_C, sub_self]
  · refine ⟨c, ?_, ?_⟩
    · rw [Set.mem_Ioo]
      have hc' : (k : ℝ) ≤ c ∧ c ≤ ((k + 1 : ℕ) : ℝ) := hc
      have hne1 : c ≠ (k : ℝ) := by
        intro h
        rw [h] at hcv
        linarith
      have hne2 : c ≠ ((k + 1 : ℕ) : ℝ) := by
        intro h
        rw [h] at hcv
        linarith
      exact ⟨hc'.1.lt_of_ne hne1.symm, hc'.2.lt_of_ne hne2⟩
    · rw [Polynomial.eval_sub, hcv, Polynomial.eval_C, sub_self]

/-- Subtracting one half from the layer-average polynomial leaves its degree bounded by the
original total degree. -/
theorem sub_half_natDegree_le (p : MvPolynomial I ℝ) :
    (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).natDegree ≤ p.totalDegree := by
  have h2 : (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).natDegree
      = (avgPoly p + -Polynomial.C ((1 : ℝ) / 2)).natDegree := by
    rw [sub_eq_add_neg]
  have h1 := Polynomial.natDegree_add_le (avgPoly p) (-Polynomial.C ((1 : ℝ) / 2))
  rw [← h2] at h1
  have hneg : (-Polynomial.C ((1 : ℝ) / 2)).natDegree = 0 := by
    rw [show -Polynomial.C ((1 : ℝ) / 2) = Polynomial.C (-(1 : ℝ) / 2) by
      rw [← Polynomial.C_neg]; ring]
    exact Polynomial.natDegree_C _
  rw [hneg] at h1
  exact le_trans h1 (Nat.max_le.mpr ⟨avgPoly_natDegree_le p, Nat.zero_le _⟩)

/-- The centered layer-average polynomial of a parity approximation has at least as many roots,
counted with multiplicity, as there are input indices. -/
theorem card_roots_ge (p : MvPolynomial I ℝ)
    (hyp : ∀ f : I → Bool,
      |p.eval (boolPoint f) - (if boolWeight f % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3) :
    Fintype.card I ≤ (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).roots.card := by
  classical
  set g : ℕ → ℝ := fun k =>
    if hk : k < Fintype.card I then Classical.choose (root_between p k hk hyp)
    else -(k : ℝ) with hg
  have hgmem : ∀ k : ℕ, k < Fintype.card I →
      g k ∈ ((avgPoly p - Polynomial.C ((1 : ℝ) / 2)).roots.toFinset : Set ℝ) := by
    intro k hk
    have hspec := (Classical.choose_spec (root_between p k hk hyp))
    have hg' : g k = (Classical.choose (root_between p k hk hyp)) := by
      rw [hg]
      simp only [dif_pos hk]
    rw [hg']
    have hne0 : (avgPoly p - Polynomial.C ((1 : ℝ) / 2)) ≠ 0 := by
      intro hQ
      have h1 := layerAverage_close p 0 (Nat.zero_le _) hyp
      rw [layerAverage_eq_avgPoly p 0 (Nat.zero_le _)] at h1
      have h1' : |(avgPoly p).eval (0 : ℝ)| ≤ 1 / 3 := by simpa [layerParity] using h1
      have hle : (avgPoly p).eval (0 : ℝ) ≤ 1 / 3 := le_trans (le_abs_self _) h1'
      have hz : Polynomial.eval (0 : ℝ) (avgPoly p - Polynomial.C ((1 : ℝ) / 2)) = 0 := by
        rw [hQ, Polynomial.eval_zero]
      rw [Polynomial.eval_sub, Polynomial.eval_C] at hz
      linarith
    refine Multiset.mem_toFinset.mpr ?_
    have hroot : Polynomial.IsRoot (avgPoly p - Polynomial.C ((1 : ℝ) / 2))
        (Classical.choose (root_between p k hk hyp)) := by
      unfold Polynomial.IsRoot
      exact hspec.2
    exact (Polynomial.mem_roots hne0).mpr hroot
  have hgIoo : ∀ k : ℕ, (hk : k < Fintype.card I) →
      g k ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    have hg' : g k = (Classical.choose (root_between p k hk hyp)) := by
      rw [hg]
      simp only [dif_pos hk]
    rw [hg']
    exact (Classical.choose_spec (root_between p k hk hyp)).1
  have hgval : ∀ k : ℕ, (hk : k < Fintype.card I) →
      g k = (Classical.choose (root_between p k hk hyp)) := by
    intro k hk
    rw [hg]
    simp only [dif_pos hk]
  have hgneg : ∀ k : ℕ, ¬(k < Fintype.card I) → g k = -(k : ℝ) := by
    intro k hk
    rw [hg]
    simp only [dif_neg hk]
  have hginj : Function.Injective g := by
    intro a b hab
    by_cases ha : a < Fintype.card I
    · by_cases hb : b < Fintype.card I
      · by_cases hne : a = b
        · exact hne
        · exfalso
          have h1 : g a ∈ Set.Ioo (a : ℝ) ((a + 1 : ℕ) : ℝ) := hgIoo a ha
          have h2 : g b ∈ Set.Ioo (b : ℝ) ((b + 1 : ℕ) : ℝ) := hgIoo b hb
          rw [Set.mem_Ioo] at h1 h2
          have h1' : (a : ℝ) < g b ∧ g b < ((a + 1 : ℕ) : ℝ) := by simpa only [hab] using h1
          rw [hgval b hb] at h1'
          rw [hgval b hb] at h2
          have hable : a ≤ b := by
            have hlt : (a : ℝ) < ((b + 1 : ℕ) : ℝ) := lt_of_lt_of_le h1'.1 (le_of_lt h2.2)
            have hltN : a < b + 1 := Nat.cast_lt.mp hlt
            omega
          have hble : b ≤ a := by
            have hlt : (b : ℝ) < ((a + 1 : ℕ) : ℝ) := lt_of_lt_of_le h2.1 (le_of_lt h1'.2)
            have hltN : b < a + 1 := Nat.cast_lt.mp hlt
            omega
          omega
      · exfalso
        have h1 : g a ∈ Set.Ioo (a : ℝ) ((a + 1 : ℕ) : ℝ) := hgIoo a ha
        rw [Set.mem_Ioo] at h1
        have h1' : (a : ℝ) < g b ∧ g b < ((a + 1 : ℕ) : ℝ) := by simpa only [hab] using h1
        rw [hgneg b hb] at h1'
        have hpos : (0 : ℝ) < -((b : ℕ) : ℝ) := by
          have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
          linarith
        have hb0' : ((b : ℕ) : ℝ) < ((0 : ℕ) : ℝ) := by linarith
        have hb0 : b < 0 := Nat.cast_lt.mp hb0'
        omega
    · by_cases hb : b < Fintype.card I
      · exfalso
        have h2 : g b ∈ Set.Ioo (b : ℝ) ((b + 1 : ℕ) : ℝ) := hgIoo b hb
        rw [Set.mem_Ioo] at h2
        have h2' : (b : ℝ) < g a ∧ g a < ((b + 1 : ℕ) : ℝ) := by simpa only [hab] using h2
        rw [hgneg a ha] at h2'
        have hpos : (0 : ℝ) < -((a : ℕ) : ℝ) := by
          have h0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
          linarith
        have ha0' : ((a : ℕ) : ℝ) < ((0 : ℕ) : ℝ) := by linarith
        have ha0 : a < 0 := Nat.cast_lt.mp ha0'
        omega
      · rw [hgneg a ha, hgneg b hb] at hab
        have hab' : ((a : ℕ) : ℝ) = (b : ℕ) := by linarith
        exact_mod_cast hab'
  have himg : (Finset.range (Fintype.card I)).image g
      ⊆ (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).roots.toFinset := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    exact hgmem k (Finset.mem_range.mp hk)
  calc Fintype.card I = (Finset.range (Fintype.card I)).card := (Finset.card_range _).symm
    _ = ((Finset.range (Fintype.card I)).image g).card :=
      (Finset.card_image_of_injective _ hginj).symm
    _ ≤ (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).roots.toFinset.card := Finset.card_le_card himg
    _ ≤ (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).roots.card :=
      Multiset.toFinset_card_le _

/-- Every real polynomial uniformly approximating Boolean parity within `1 / 3` has total degree
at least the number of input variables [BealsEtAl2001]. -/
theorem parity_boolean_approximation_degree (p : MvPolynomial I ℝ)
    (hyp : ∀ f : I → Bool,
      |MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) p
        - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3) :
    Fintype.card I ≤ p.totalDegree := by
  have hyp' : ∀ f : I → Bool,
      |p.eval (boolPoint f) - (if boolWeight f % 2 = 1 then (1 : ℝ) else 0)| ≤ 1 / 3 := by
    intro f
    have := hyp f
    simpa only [boolWeight, boolSupp, boolPoint] using! this
  have hcard := card_roots_ge p hyp'
  exact le_trans hcard (le_trans (Polynomial.card_roots'
    (avgPoly p - Polynomial.C ((1 : ℝ) / 2))) (sub_half_natDegree_le p))

/-- A unitary query circuit on a normalized state whose acceptance probability approximates
parity within `1 / 3` satisfies `Fintype.card I ≤ 2 * QueryCount C` [BealsEtAl2001]. -/
theorem parity_actual_bounded_error_query_lower_bound
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (_hU : IsUnitaryCircuit C) (_hN : Normalized ψ)
    (hyp : ∀ f : I → Bool,
      |MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E
        - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0)|
        ≤ 1 / 3) :
    Fintype.card I ≤ 2 * QueryCount C := by
  have h5 := acceptance_boolean_multilinearization_preserves_run C ψ E
  have h6 := parity_boolean_approximation_degree (booleanAcceptancePolynomial C ψ E)
    (fun f => by
      have h := hyp f
      rw [← h5.2.2 f] at h
      simpa only [boolWeight, boolSupp, boolPoint] using h)
  exact le_trans h6 h5.1

end Qatlib.Concepts.QueryComplexity.DegreeMethod
