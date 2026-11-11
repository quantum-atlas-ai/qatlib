/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.BooleanCubeFourier
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductPoincare
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeMvPolynomial
import Qatlib.Concepts.ProbabilityCore.DistributionAA.DegreeInfluenceBounds
import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.BooleanPolynomial
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Polynomial degree and variable dependence

This module bounds the number of relevant variables of a Boolean function in terms of its exact
multilinear polynomial degree. It develops support bounds for nonzero multilinear polynomials,
relates formal partial derivatives to coordinate flips, and proves Fourier inversion, Parseval's
identity, and influence formulas on the uniform Boolean cube. The Fourier calculations include
the identity used in [AticiServedio2007].

Combining the support and total-influence estimates, `card_le_exactDegree_mul_two_pow` proves `n
≤ d * 2 ^ (d - 1)` for functions depending on all `n` variables, where `d = exactDegree f`. The
logarithmic consequences culminate in `exactMinimum_logb_lower_bound`, an explicit exact-query
lower bound corresponding to [BealsEtAl2001].

## Main statements

* `pow_two_sub_le_card_support`: a nonzero multilinear polynomial of degree at most `d` is
  nonzero at at least `2 ^ (n - d)` Boolean inputs.
* `uniform_fourier_inversion`: expansion in the uniform Boolean characters.
* `sum_sq_eq_mul_sum_uniformFourierCoeff_sq`: Parseval's identity with the unnormalized sum over
  inputs.
* `cubeTotalInf_le_exactDegree`: total influence of a Boolean indicator is at most its exact
  degree.
* `card_le_exactDegree_mul_two_pow`: a degree bound on the number of relevant variables.
* `exactMinimum_logb_lower_bound`: a logarithmic lower bound on the exact query minimum.

## References

* [Beals et al., 2001][BealsEtAl2001]
* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ProbabilityCore.DistributionAA

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence

open Qatlib
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- A real multilinear polynomial that evaluates to zero at every Boolean input is the zero
polynomial. -/
theorem multilinear_eq_zero_of_bool_eval_zero {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1)
    (he : ∀ x : Fin n → Bool, MvPolynomial.eval (booleanPoint x) P = 0) : P = 0 := by
  classical
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _ => {0, 1})
  · intro i
    simpa using! Nat.lt_succ_of_le (hP i)
  · intro x hx
    let y : Fin n → Bool := fun i => decide (x i = 1)
    have hy : booleanPoint y = x := by
      funext i
      have hi := hx i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi <;> simp [booleanPoint, y, hi]
    rw [← hy]
    exact he y

/-- Evaluating a multilinear polynomial with its first coordinate set to `false` evaluates the
constant coefficient of its `finSuccEquiv` expansion at the remaining Boolean coordinates. -/
theorem bool_eval_cons_false {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (y : Fin n → Bool) :
    MvPolynomial.eval (booleanPoint (Fin.cons false y)) P =
      MvPolynomial.eval (booleanPoint y) ((MvPolynomial.finSuccEquiv ℝ n P).coeff 0) := by
  have hpoint : booleanPoint (Fin.cons false y) =
      Fin.cons (0 : ℝ) (booleanPoint y) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [booleanPoint]
  have hdeg : (MvPolynomial.finSuccEquiv ℝ n P).natDegree < 2 := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact Nat.lt_succ_of_le (hP 0)
  have hdegMap : (Polynomial.map (MvPolynomial.eval (booleanPoint y))
      (MvPolynomial.finSuccEquiv ℝ n P)).natDegree < 2 :=
    Polynomial.natDegree_map_le.trans_lt hdeg
  rw [hpoint, MvPolynomial.eval_eq_eval_mv_eval']
  rw [Polynomial.eval_eq_sum_range' hdegMap]
  simp [Finset.sum_range_succ]

/-- Evaluating a multilinear polynomial with its first coordinate set to `true` gives the sum of
the evaluations of the constant and linear coefficients of its `finSuccEquiv` expansion. -/
theorem bool_eval_cons_true {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (y : Fin n → Bool) :
    MvPolynomial.eval (booleanPoint (Fin.cons true y)) P =
      MvPolynomial.eval (booleanPoint y) ((MvPolynomial.finSuccEquiv ℝ n P).coeff 0) +
        MvPolynomial.eval (booleanPoint y) ((MvPolynomial.finSuccEquiv ℝ n P).coeff 1) := by
  have hpoint : booleanPoint (Fin.cons true y) =
      Fin.cons (1 : ℝ) (booleanPoint y) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [booleanPoint]
  have hdeg : (MvPolynomial.finSuccEquiv ℝ n P).natDegree < 2 := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact Nat.lt_succ_of_le (hP 0)
  have hdegMap : (Polynomial.map (MvPolynomial.eval (booleanPoint y))
      (MvPolynomial.finSuccEquiv ℝ n P)).natDegree < 2 :=
    Polynomial.natDegree_map_le.trans_lt hdeg
  rw [hpoint, MvPolynomial.eval_eq_eval_mv_eval']
  rw [Polynomial.eval_eq_sum_range' hdegMap]
  simp [Finset.sum_range_succ]

/-- The equivalence splitting the nonzero support of a function on the Boolean cube into its
slices with first coordinate `false` and `true`. -/
noncomputable def supportSuccEquiv {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    {x : Fin (n + 1) → Bool // f x ≠ 0} ≃
      {y : Fin n → Bool // f (Fin.cons false y) ≠ 0} ⊕
        {y : Fin n → Bool // f (Fin.cons true y) ≠ 0} where
  toFun x :=
    if hx : x.1 0 then
      Sum.inr ⟨Fin.tail x.1, by
        have hcons : Fin.cons true (Fin.tail x.1) = x.1 := by
          rw [← hx]
          exact Fin.cons_self_tail x.1
        simpa only [hcons] using! x.2⟩
    else
      Sum.inl ⟨Fin.tail x.1, by
        have hx0 : x.1 0 = false := Bool.eq_false_of_not_eq_true hx
        have hcons : Fin.cons false (Fin.tail x.1) = x.1 := by
          rw [← hx0]
          exact Fin.cons_self_tail x.1
        simpa only [hcons] using! x.2⟩
  invFun s :=
    match s with
    | Sum.inl y => ⟨Fin.cons false y.1, y.2⟩
    | Sum.inr y => ⟨Fin.cons true y.1, y.2⟩
  left_inv x := by
    by_cases hx : x.1 0
    · simp only [hx]
      apply Subtype.ext
      simpa [hx] using! Fin.cons_self_tail x.1
    · simp only [hx]
      apply Subtype.ext
      have hx0 : x.1 0 = false := Bool.eq_false_of_not_eq_true hx
      simpa [hx0] using! Fin.cons_self_tail x.1
  right_inv s := by
    cases s with
    | inl y => simp
    | inr y => simp

/-- The number of Boolean inputs where `f` is nonzero is the sum of the corresponding counts in
its two first-coordinate slices. -/
theorem card_support_succ {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    Fintype.card {x : Fin (n + 1) → Bool // f x ≠ 0} =
      Fintype.card {y : Fin n → Bool // f (Fin.cons false y) ≠ 0} +
        Fintype.card {y : Fin n → Bool // f (Fin.cons true y) ≠ 0} := by
  rw [Fintype.card_congr (supportSuccEquiv f), Fintype.card_sum]

/-- Maps a tail input with nonzero first-coordinate difference to a nonzero value of `f` in one
of the two slices above that tail. -/
noncomputable def derivativeSupportEmbedding {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ)
    (y : {y : Fin n → Bool // f (Fin.cons true y) - f (Fin.cons false y) ≠ 0}) :
    {x : Fin (n + 1) → Bool // f x ≠ 0} :=
  if hy : f (Fin.cons false y.1) = 0 then
    ⟨Fin.cons true y.1, by
      intro hzero
      apply y.2
      rw [hzero, hy, sub_zero]⟩
  else
    ⟨Fin.cons false y.1, hy⟩

/-- The map from the support of the first-coordinate difference to the nonzero support of `f` is
injective. -/
theorem derivativeSupportEmbedding_injective {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    Function.Injective (derivativeSupportEmbedding f) := by
  intro y z hyz
  unfold derivativeSupportEmbedding at hyz
  by_cases hy : f (Fin.cons false y.1) = 0
  · by_cases hz : f (Fin.cons false z.1) = 0
    · simp only [hy, hz, dif_pos] at hyz
      apply Subtype.ext
      have hcons : (Fin.cons true y.1 : Fin (n + 1) → Bool) = Fin.cons true z.1 :=
        congrArg Subtype.val hyz
      exact Fin.cons_right_injective (α := fun _ : Fin (n + 1) => Bool) true hcons
    · simp only [hy, hz, dif_pos] at hyz
      have h := congrArg (fun x : {x : Fin (n + 1) → Bool // f x ≠ 0} => x.1 0) hyz
      simp at h
  · by_cases hz : f (Fin.cons false z.1) = 0
    · simp only [hy, hz, dif_pos] at hyz
      have h := congrArg (fun x : {x : Fin (n + 1) → Bool // f x ≠ 0} => x.1 0) hyz
      simp at h
    · simp only [hy, hz] at hyz
      apply Subtype.ext
      have hcons : (Fin.cons false y.1 : Fin (n + 1) → Bool) = Fin.cons false z.1 :=
        congrArg Subtype.val hyz
      exact Fin.cons_right_injective (α := fun _ : Fin (n + 1) => Bool) false hcons

/-- A nonzero function represented on the Boolean cube by a multilinear polynomial of total
degree at most `d` is nonzero at at least `2 ^ (n - d)` inputs, with subtraction in the
natural numbers. -/
theorem pow_two_sub_le_card_support {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (P : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : P.totalDegree ≤ d)
    (hm : ∀ i, P.degreeOf i ≤ 1)
    (he : ∀ x, MvPolynomial.eval (booleanPoint x) P = f x)
    (hn : ∃ x, f x ≠ 0) : 2 ^ (n - d) ≤ Fintype.card {x // f x ≠ 0} := by
  classical
  induction n generalizing d with
  | zero =>
      obtain ⟨x, hx⟩ := hn
      have hpos : 0 < Fintype.card {x : Fin 0 → Bool // f x ≠ 0} :=
        Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
      rw [Nat.zero_sub, pow_zero]
      exact hpos
  | succ n ih =>
      let Q := MvPolynomial.finSuccEquiv ℝ n P
      let A := Q.coeff 0
      let R := Q.coeff 1
      let f0 : (Fin n → Bool) → ℝ := fun y => f (Fin.cons false y)
      let f1 : (Fin n → Bool) → ℝ := fun y => f (Fin.cons true y)
      have he0 (y : Fin n → Bool) : MvPolynomial.eval (booleanPoint y) A = f0 y := by
        dsimp only [A, Q, f0]
        rw [← bool_eval_cons_false P hm y, he]
      have he1 (y : Fin n → Bool) : MvPolynomial.eval (booleanPoint y) (A + R) = f1 y := by
        rw [MvPolynomial.eval_add]
        dsimp only [A, R, Q, f1]
        rw [← bool_eval_cons_true P hm y, he]
      have hAdeg : A.totalDegree ≤ d := by
        by_cases hA : A = 0
        · simp [hA]
        · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P 0 hA
          have hle' : A.totalDegree ≤ P.totalDegree := by simpa [A, Q] using! hle
          exact hle'.trans hd
      have hAm (j : Fin n) : A.degreeOf j ≤ 1 :=
        (MvPolynomial.degreeOf_coeff_finSuccEquiv P j 0).trans (hm j.succ)
      by_cases hR : R = 0
      · have hf01 : f0 = f1 := by
          funext y
          have hy := he1 y
          rw [hR, add_zero, he0] at hy
          exact hy
        have hn0 : ∃ y, f0 y ≠ 0 := by
          obtain ⟨x, hx⟩ := hn
          cases hx0 : x 0 with
          | false =>
              refine ⟨Fin.tail x, ?_⟩
              have hcons : Fin.cons false (Fin.tail x) = x := by
                rw [← hx0]
                exact Fin.cons_self_tail x
              simpa only [f0, hcons] using! hx
          | true =>
              refine ⟨Fin.tail x, ?_⟩
              rw [hf01]
              have hcons : Fin.cons true (Fin.tail x) = x := by
                rw [← hx0]
                exact Fin.cons_self_tail x
              simpa only [f1, hcons] using! hx
        have hih := ih f0 A d hAdeg hAm he0 hn0
        rw [card_support_succ]
        change 2 ^ (n + 1 - d) ≤
          Fintype.card {y // f0 y ≠ 0} + Fintype.card {y // f1 y ≠ 0}
        rw [← hf01]
        by_cases hdn : d ≤ n
        · have hsub : n + 1 - d = (n - d) + 1 := by omega
          rw [hsub, pow_succ]
          omega
        · have hsub : n + 1 - d = 0 := by omega
          rw [hsub, pow_zero]
          obtain ⟨y, hy⟩ := hn0
          have hpos : 0 < Fintype.card {y // f0 y ≠ 0} :=
            Fintype.card_pos_iff.mpr ⟨⟨y, hy⟩⟩
          omega
      · have hRdeg : R.totalDegree + 1 ≤ d :=
          (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P 1 hR).trans hd
        have hRm (j : Fin n) : R.degreeOf j ≤ 1 :=
          (MvPolynomial.degreeOf_coeff_finSuccEquiv P j 1).trans (hm j.succ)
        let D : (Fin n → Bool) → ℝ := fun y => f1 y - f0 y
        have heD (y : Fin n → Bool) : MvPolynomial.eval (booleanPoint y) R = D y := by
          have hy := he1 y
          rw [MvPolynomial.eval_add, he0] at hy
          dsimp only [D]
          linarith
        have hnD : ∃ y, D y ≠ 0 := by
          by_contra h
          push Not at h
          exact hR (multilinear_eq_zero_of_bool_eval_zero R hRm (fun y => by rw [heD]; exact h y))
        have hih := ih D R (d - 1) (by omega) hRm heD hnD
        have hsub : n + 1 - d = n - (d - 1) := by omega
        rw [hsub]
        exact hih.trans (Fintype.card_le_of_injective _ (derivativeSupportEmbedding_injective f))

/-- The coefficient at exponent vector `m` in the partial derivative with respect to `i` is `m i
+ 1` times the coefficient of `P` at `m + Finsupp.single i 1`. -/
theorem coeff_pderiv {n : ℕ} (m : Fin n →₀ ℕ) (i : Fin n) (P : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.pderiv i P).coeff m =
      (m i + 1 : ℕ) * P.coeff (m + Finsupp.single i 1) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.coeff_add, hP, hQ]
      ring
  | monomial s a =>
      rw [MvPolynomial.pderiv_monomial]
      by_cases hs : s = m + Finsupp.single i 1
      · subst s
        simp [MvPolynomial.coeff_monomial, Finsupp.add_apply]; ring
      · rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial, if_neg hs, mul_zero]
        by_cases hsi : s i = 0
        · simp [hsi]
        · have hms : s - Finsupp.single i 1 ≠ m := by
            intro hms
            apply hs
            rw [← hms]
            exact (Finsupp.sub_add_single_one_cancel hsi).symm
          simp [hms]

/-- Every exponent vector in the support of a partial derivative comes from a supported exponent
vector of `P` by decreasing the differentiated coordinate by one. -/
theorem mem_support_add_single_of_mem_pderiv {n : ℕ} {m : Fin n →₀ ℕ} {i : Fin n}
    {P : MvPolynomial (Fin n) ℝ} (hm : m ∈ (MvPolynomial.pderiv i P).support) :
    m + Finsupp.single i 1 ∈ P.support := by
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro hz
  have hc := coeff_pderiv m i P
  rw [hz, mul_zero] at hc
  exact hm hc

/-- Taking a nonzero partial derivative lowers total degree by at least one: its total degree
plus one is at most `P.totalDegree`. -/
theorem totalDegree_pderiv_add_one_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (i : Fin n)
    (h : MvPolynomial.pderiv i P ≠ 0) :
    (MvPolynomial.pderiv i P).totalDegree + 1 ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, add_comm,
    Finset.add_sup (by simpa only [MvPolynomial.support_nonempty] using! h), Finset.sup_le_iff]
  intro m hm
  have hp := MvPolynomial.le_totalDegree (mem_support_add_single_of_mem_pderiv hm)
  simpa [Finsupp.sum_add_index, add_comm] using! hp

/-- Taking a partial derivative with respect to `i` does not increase the degree in any variable
`j`. -/
theorem degreeOf_pderiv_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (i j : Fin n) :
    (MvPolynomial.pderiv i P).degreeOf j ≤ P.degreeOf j := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup, Finset.sup_le_iff]
  intro m hm
  calc
    m j ≤ ((m + Finsupp.single i 1 : Fin n →₀ ℕ) j) := by simp
    _ ≤ _ := Finset.le_sup (f := fun m : Fin n →₀ ℕ => m j)
      (mem_support_add_single_of_mem_pderiv hm)

/-- If `m i` is nonzero, the monomial product with exponent vector `m` factors as the product
with exponent vector `m - Finsupp.single i 1` multiplied by `z i`. -/
theorem prod_pow_eq_sub_single_mul {n : ℕ} (m : Fin n →₀ ℕ) (i : Fin n)
    (hmi : m i ≠ 0) (z : Fin n → ℝ) :
    m.prod (fun j e => z j ^ e) =
      (m - Finsupp.single i 1).prod (fun j e => z j ^ e) * z i := by
  conv_lhs => rw [← Finsupp.sub_add_single_one_cancel hmi]
  rw [Finsupp.prod_add_index' (fun j => pow_zero (z j))
    (fun j e₁ e₂ => pow_add (z j) e₁ e₂), Finsupp.prod_single_index (by simp)]
  simp

/-- For a monomial of degree at most one in coordinate `i`, its value at `x` minus its value
after flipping `i` equals its partial derivative at `x`, multiplied by `1` when `x i` is
true and by `-1` otherwise. -/
theorem bool_eval_sub_flip_monomial {n : ℕ} (m : Fin n →₀ ℕ) (a : ℝ) (i : Fin n)
    (hmi : m i ≤ 1) (x : Fin n → Bool) :
    MvPolynomial.eval (booleanPoint x) (MvPolynomial.monomial m a) -
        MvPolynomial.eval (booleanPoint (cubeFlip x i)) (MvPolynomial.monomial m a) =
      (if x i then 1 else -1) *
        MvPolynomial.eval (booleanPoint x) (MvPolynomial.pderiv i (MvPolynomial.monomial m a)) := by
  classical
  by_cases hzero : m i = 0
  · have hprod : m.prod (fun j e => (booleanPoint (cubeFlip x i) : Fin n → ℝ) j ^ e) =
        m.prod (fun j e => (booleanPoint x : Fin n → ℝ) j ^ e) := by
      apply Finsupp.prod_congr
      intro j hj
      by_cases hji : j = i
      · subst j
        simp [hzero]
      · simp [booleanPoint, cubeFlip, hji]
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
      MvPolynomial.pderiv_monomial, hprod]
    simp [hzero]
  · have hone : m i = 1 := by omega
    have hB : (m - Finsupp.single i 1).prod
        (fun j e => (booleanPoint (cubeFlip x i) : Fin n → ℝ) j ^ e) =
        (m - Finsupp.single i 1).prod (fun j e => (booleanPoint x : Fin n → ℝ) j ^ e) := by
      apply Finsupp.prod_congr
      intro j hj
      by_cases hji : j = i
      · subst j
        simp [hone]
      · simp [booleanPoint, cubeFlip, hji]
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
      MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial,
      prod_pow_eq_sub_single_mul m i hzero (booleanPoint x),
      prod_pow_eq_sub_single_mul m i hzero (booleanPoint (cubeFlip x i)), hB]
    cases hx : x i <;> simp [hx, hone, booleanPoint, cubeFlip]

/-- For a multilinear polynomial, the difference between its Boolean evaluations at `x` and
`cubeFlip x i` is its partial derivative at `x`, multiplied by `1` when `x i` is true and by
`-1` otherwise. -/
theorem bool_eval_sub_flip {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (x : Fin n → Bool) (i : Fin n) :
    MvPolynomial.eval (booleanPoint x) P - MvPolynomial.eval (booleanPoint (cubeFlip x i)) P =
      (if x i then 1 else -1) * MvPolynomial.eval (booleanPoint x) (MvPolynomial.pderiv i P) := by
  classical
  rw [MvPolynomial.as_sum P]
  simp only [map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact bool_eval_sub_flip_monomial m (P.coeff m) i
    (MvPolynomial.degreeOf_le_iff.mp (hP i) m hm) x

/-- Under the uniform Boolean-cube weights, the influence of coordinate `i` is `2 ^ n` inverse
times the sum of squared coordinate-flip differences of `F`. -/
theorem cubeInf_uniform {n : ℕ} (F : (Fin n → Bool) → ℝ) (i : Fin n) :
    cubeInf n (muWeight (1 / 2) n) F i =
      ((2 : ℝ) ^ n)⁻¹ * ∑ x, (F x - F (cubeFlip x i)) ^ 2 := by
  unfold cubeInf cubeExpect
  simp only [muWeight, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ite_self,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum]
  simp [one_div, inv_pow]

/-- If `f` depends on coordinate `i`, then `2 ^ n` times the uniform influence of `i` on its
indicator is at least `2 ^ (n - (exactDegree f - 1))`, with both subtractions in the natural
numbers. -/
theorem pow_two_sub_le_mul_cubeInf {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : ∃ x, f x ≠ f (cubeFlip x i)) :
    (2 : ℝ) ^ (n - (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f - 1)) ≤
      (2 : ℝ) ^ n * cubeInf n (muWeight (1 / 2) n)
        (fun x => if f x then (1 : ℝ) else 0) i := by
  classical
  let P := MvPolynomial.map (Int.castRingHom ℝ)
    (integerBooleanRepresentative f)
  let R := MvPolynomial.pderiv i P
  let F : (Fin n → Bool) → ℝ := fun x => if f x then 1 else 0
  have hPm : ∀ j, P.degreeOf j ≤ 1 := integerBooleanRepresentative_real_degreeOf f
  have hPdeg : P.totalDegree = Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f :=
    integerBooleanRepresentative_real_degree_eq f
  have he (x : Fin n → Bool) : MvPolynomial.eval (booleanPoint x) P = F x :=
    integerBooleanRepresentative_map_eval f x
  have hdiff (x : Fin n → Bool) : F x - F (cubeFlip x i) =
      (if x i then 1 else -1) * MvPolynomial.eval (booleanPoint x) R := by
    have h := bool_eval_sub_flip P hPm x i
    rw [he x, he (cubeFlip x i)] at h
    exact h
  have hn : ∃ x, MvPolynomial.eval (booleanPoint x) R ≠ 0 := by
    obtain ⟨x, hx⟩ := hdep
    refine ⟨x, ?_⟩
    intro hz
    have hzero : F x - F (cubeFlip x i) = 0 := by rw [hdiff, hz, mul_zero]
    cases hf : f x <;> cases hg : f (cubeFlip x i) <;> simp_all [F]
  have hRne : R ≠ 0 := by
    intro hR
    obtain ⟨x, hx⟩ := hn
    rw [hR] at hx
    simp at hx
  have hRdeg : R.totalDegree + 1 ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f := by
    rw [← hPdeg]
    exact totalDegree_pderiv_add_one_le P i hRne
  have hRm : ∀ j, R.degreeOf j ≤ 1 := fun j =>
    (degreeOf_pderiv_le P i j).trans (hPm j)
  have hsupport := pow_two_sub_le_card_support
    (fun x => MvPolynomial.eval (booleanPoint x) R) R
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f - 1) (by omega) hRm (fun _ => rfl) hn
  have hpoint (x : Fin n → Bool) :
      (if MvPolynomial.eval (booleanPoint x) R ≠ 0 then (1 : ℝ) else 0) ≤
        (F x - F (cubeFlip x i)) ^ 2 := by
    by_cases hx : MvPolynomial.eval (booleanPoint x) R ≠ 0
    · rw [if_pos hx]
      have hs : (if x i then (1 : ℝ) else -1) ≠ 0 := by
        cases hxi : x i <;> simp
      have hDne : F x - F (cubeFlip x i) ≠ 0 := by
        intro hzero
        have hz : (if x i then (1 : ℝ) else -1) * MvPolynomial.eval (booleanPoint x) R = 0 := by
          rw [← hdiff, hzero]
        exact hx ((mul_eq_zero.mp hz).resolve_left hs)
      have hfne : f x ≠ f (cubeFlip x i) := by
        intro heq
        apply hDne
        simp [F, heq]
      cases hf : f x <;> cases hg : f (cubeFlip x i) <;> simp_all [F]
    · rw [if_neg hx]
      positivity
  have hcard : (Fintype.card {x // MvPolynomial.eval (booleanPoint x) R ≠ 0} : ℝ) =
      ∑ x, if MvPolynomial.eval (booleanPoint x) R ≠ 0 then (1 : ℝ) else 0 := by
    have hnat : Fintype.card {x // MvPolynomial.eval (booleanPoint x) R ≠ 0} =
        ∑ x, if MvPolynomial.eval (booleanPoint x) R ≠ 0 then (1 : ℕ) else 0 := by
      simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact_mod_cast hnat
  have hsum : (Fintype.card {x // MvPolynomial.eval (booleanPoint x) R ≠ 0} : ℝ) ≤
      ∑ x, (F x - F (cubeFlip x i)) ^ 2 := by
    rw [hcard]
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hpow : (2 : ℝ) ^ (n - (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f - 1)) ≤
      ∑ x, (F x - F (cubeFlip x i)) ^ 2 := by
    have hsupport' : (2 : ℝ) ^ (n - (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f - 1)) ≤
        (Fintype.card {x // MvPolynomial.eval (booleanPoint x) R ≠ 0} : ℝ) := by
      exact_mod_cast hsupport
    exact hsupport'.trans hsum
  rw [cubeInf_uniform, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0), one_mul]
  exact hpow
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier
open scoped symmDiff

/-- The uniform Fourier coefficient of `F` at `S`, defined as the average of `cubeChar S x * F
x` over the Boolean cube. -/
def uniformFourierCoeff {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x, cubeChar S x * F x

/-- The sum of a Boolean character over the cube is `2 ^ n` for the empty index set and zero
otherwise. -/
theorem sum_cubeChar {n : ℕ} (S : Finset (Fin n)) :
    ∑ x, cubeChar S x = if S = ∅ then (2 : ℝ) ^ n else 0 := by
  classical
  have hfull (x : Fin n → Bool) : cubeChar S x =
      ∏ i, if i ∈ S then (if x i then (1 : ℝ) else -1) else 1 := by
    unfold cubeChar
    exact (Finset.prod_ite_mem_eq S (fun i => if x i then (1 : ℝ) else -1)).symm
  calc
    _ = ∑ x : Fin n → Bool, ∏ i, if i ∈ S then (if x i then (1 : ℝ) else -1) else 1 := by
      apply Finset.sum_congr rfl
      intro x _
      exact hfull x
    _ = ∏ i, ∑ b : Bool, if i ∈ S then (if b then (1 : ℝ) else -1) else 1 := by
      simpa using! (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
        (fun i b => if i ∈ S then (if b then (1 : ℝ) else -1) else 1)).symm
    _ = if S = ∅ then (2 : ℝ) ^ n else 0 := by
      by_cases hS : S = ∅
      · subst S
        simp
      · rw [if_neg hS]
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]

/-- The sum of the product of two Boolean characters over the cube is `2 ^ n` when their index
sets agree and zero otherwise. -/
theorem sum_cubeChar_mul {n : ℕ} (S T : Finset (Fin n)) :
    ∑ x, cubeChar S x * cubeChar T x = if S = T then (2 : ℝ) ^ n else 0 := by
  classical
  simp_rw [cubeChar_mul]
  rw [sum_cubeChar]
  by_cases hST : S = T
  · subst T
    simp
  · rw [if_neg hST, if_neg (fun h => hST (Finset.symmDiff_eq_empty.mp h))]

/-- The equivalence between Boolean assignments on `Fin n` and finite subsets of `Fin n`,
sending an assignment to the set of coordinates where it is true. -/
def cubeSubsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun x := Finset.univ.filter (fun i => x i)
  invFun S := fun i => decide (i ∈ S)
  left_inv x := by
    funext i
    simp
  right_inv S := by
    ext i
    simp

/-- Summing `cubeChar S x * cubeChar S y` over all index sets gives `2 ^ n` when `x = y` and
zero otherwise. -/
theorem sum_cubeChar_points {n : ℕ} (x y : Fin n → Bool) :
    ∑ S : Finset (Fin n), cubeChar S x * cubeChar S y =
      if x = y then (2 : ℝ) ^ n else 0 := by
  classical
  calc
    _ = ∑ u : Fin n → Bool, cubeChar (cubeSubsetEquiv n u) x * cubeChar (cubeSubsetEquiv n u) y := by
      exact ((cubeSubsetEquiv n).sum_comp
        (fun S => cubeChar S x * cubeChar S y)).symm
    _ = ∑ u : Fin n → Bool, ∏ i,
        if u i then ((if x i then (1 : ℝ) else -1) * (if y i then (1 : ℝ) else -1)) else 1 := by
      apply Finset.sum_congr rfl
      intro u _
      have hchar (z : Fin n → Bool) : cubeChar (cubeSubsetEquiv n u) z =
          ∏ i, if u i then (if z i then (1 : ℝ) else -1) else 1 := by
        unfold cubeChar
        simpa [cubeSubsetEquiv] using! (Finset.prod_ite_mem_eq (cubeSubsetEquiv n u)
          (fun i => if z i then (1 : ℝ) else -1)).symm
      rw [hchar x, hchar y, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hu : u i <;> simp [hu]
    _ = ∏ i, ∑ b : Bool,
        if b then ((if x i then (1 : ℝ) else -1) * (if y i then (1 : ℝ) else -1)) else 1 := by
      simpa using! (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
        (fun i b => if b then
          ((if x i then (1 : ℝ) else -1) * (if y i then (1 : ℝ) else -1)) else 1)).symm
    _ = if x = y then (2 : ℝ) ^ n else 0 := by
      have hfactor (i : Fin n) :
          (∑ b : Bool, if b then
            ((if x i then (1 : ℝ) else -1) * (if y i then (1 : ℝ) else -1)) else 1) =
            if x i = y i then 2 else 0 := by
        cases hx : x i <;> cases hy : y i <;> simp
      simp_rw [hfactor]
      by_cases hxy : x = y
      · subst y
        simp
      · rw [if_neg hxy]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Every real function on the Boolean cube equals the sum of its uniform Fourier coefficients
multiplied by the corresponding Boolean characters. -/
theorem uniform_fourier_inversion {n : ℕ} (F : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    F x = ∑ S, uniformFourierCoeff S F * cubeChar S x := by
  classical
  let a := (2 : ℝ) ^ n
  symm
  calc
    ∑ S, uniformFourierCoeff S F * cubeChar S x =
        a⁻¹ * ∑ S, (∑ y, cubeChar S y * F y) * cubeChar S x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      dsimp only [uniformFourierCoeff, a]
      ring
    _ = a⁻¹ * ∑ y, (∑ S, cubeChar S y * cubeChar S x) * F y := by
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = F x := by
      simp_rw [sum_cubeChar_points]
      rw [Finset.sum_eq_single x]
      · dsimp only [a]
        rw [if_pos rfl, ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0), one_mul]
      · intro y _ hy
        simp [hy]
      · simp

/-- Parseval's identity on the uniform Boolean cube: the sum of squared function values is `2 ^
n` times the sum of squared Fourier coefficients. See [Atici and Servedio, Lemma
II.1][AticiServedio2007]. -/
theorem sum_sq_eq_mul_sum_uniformFourierCoeff_sq {n : ℕ} (F : (Fin n → Bool) → ℝ) :
    ∑ x, F x ^ 2 = (2 : ℝ) ^ n * ∑ S, uniformFourierCoeff S F ^ 2 := by
  classical
  calc
    ∑ x, F x ^ 2 = ∑ x, (∑ S, uniformFourierCoeff S F * cubeChar S x) *
        (∑ T, uniformFourierCoeff T F * cubeChar T x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← uniform_fourier_inversion F x]
      ring
    _ = ∑ S, ∑ T, uniformFourierCoeff S F * uniformFourierCoeff T F *
        (∑ x, cubeChar S x * cubeChar T x) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ S, ∑ T, uniformFourierCoeff S F * uniformFourierCoeff T F *
        (if S = T then (2 : ℝ) ^ n else 0) := by
      simp_rw [sum_cubeChar_mul]
    _ = (2 : ℝ) ^ n * ∑ S, uniformFourierCoeff S F ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_eq_single S]
      · simp
        ring
      · intro T _ hTS
        simp [Ne.symm hTS]
      · simp

/-- For any expansion of `F` in Boolean characters with coefficients `a`, the sum of squared
values of `F` is `2 ^ n` times the sum of squared coefficients. -/
theorem sum_sq_eq_mul_sum_sq_of_expansion {n : ℕ} (a : Finset (Fin n) → ℝ)
    (F : (Fin n → Bool) → ℝ) (hF : ∀ x, F x = ∑ S, a S * cubeChar S x) :
    ∑ x, F x ^ 2 = (2 : ℝ) ^ n * ∑ S, a S ^ 2 := by
  classical
  calc
    ∑ x, F x ^ 2 = ∑ x, (∑ S, a S * cubeChar S x) * (∑ T, a T * cubeChar T x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hF]
      ring
    _ = ∑ S, ∑ T, a S * a T * (∑ x, cubeChar S x * cubeChar T x) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ S, ∑ T, a S * a T * (if S = T then (2 : ℝ) ^ n else 0) := by
      simp_rw [sum_cubeChar_mul]
    _ = (2 : ℝ) ^ n * ∑ S, a S ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_eq_single S]
      · simp
        ring
      · intro T _ hTS
        simp [Ne.symm hTS]
      · simp

/-- Flipping coordinate `i` negates the character indexed by `S` exactly when `i ∈ S`, and
otherwise leaves it unchanged. -/
theorem cubeChar_flip {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :
    cubeChar S (cubeFlip x i) = if i ∈ S then -cubeChar S x else cubeChar S x := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hsplit (z : Fin n → Bool) : cubeChar S z =
        (if z i then (1 : ℝ) else -1) * ∏ j ∈ S.erase i, (if z j then (1 : ℝ) else -1) := by
      exact (Finset.mul_prod_erase S (fun j => if z j then (1 : ℝ) else -1) hi).symm
    rw [hsplit (cubeFlip x i), hsplit x]
    have herase : (∏ j ∈ S.erase i, (if cubeFlip x i j then (1 : ℝ) else -1)) =
        ∏ j ∈ S.erase i, (if x j then (1 : ℝ) else -1) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [cubeFlip, hji]
    rw [herase]
    cases hx : x i <;> simp [cubeFlip, hx]
  · rw [if_neg hi]
    unfold cubeChar
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hi hj
    simp [cubeFlip, hji]

/-- The coordinate-flip difference of `F` has Fourier coefficient `2 * uniformFourierCoeff S F`
on sets containing `i` and zero on the other sets. -/
theorem flip_sub_fourier_expansion {n : ℕ} (F : (Fin n → Bool) → ℝ) (x : Fin n → Bool) (i : Fin n) :
    F x - F (cubeFlip x i) =
      ∑ S, (if i ∈ S then 2 * uniformFourierCoeff S F else 0) * cubeChar S x := by
  classical
  rw [uniform_fourier_inversion F x, uniform_fourier_inversion F (cubeFlip x i)]
  simp_rw [cubeChar_flip]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hi : i ∈ S <;> simp [hi]; ring

/-- The uniform influence of coordinate `i` is four times the sum of squared Fourier
coefficients indexed by sets containing `i`. -/
theorem cubeInf_fourier {n : ℕ} (F : (Fin n → Bool) → ℝ) (i : Fin n) :
    cubeInf n (muWeight (1 / 2) n) F i =
      4 * ∑ S, if i ∈ S then uniformFourierCoeff S F ^ 2 else 0 := by
  classical
  let a : Finset (Fin n) → ℝ := fun S =>
    if i ∈ S then 2 * uniformFourierCoeff S F else 0
  have hsum := sum_sq_eq_mul_sum_sq_of_expansion a
    (fun x => F x - F (cubeFlip x i)) (fun x => flip_sub_fourier_expansion F x i)
  rw [cubeInf_uniform, hsum, ← mul_assoc,
    inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0), one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hi : i ∈ S <;> simp [a, hi]; ring

/-- Uniform total influence is four times the sum of squared Fourier coefficients weighted by
the cardinalities of their index sets. -/
theorem cubeTotalInf_fourier {n : ℕ} (F : (Fin n → Bool) → ℝ) :
    cubeTotalInf n (muWeight (1 / 2) n) F =
      4 * ∑ S, (S.card : ℝ) * uniformFourierCoeff S F ^ 2 := by
  classical
  calc
    cubeTotalInf n (muWeight (1 / 2) n) F =
        ∑ i, 4 * ∑ S, if i ∈ S then uniformFourierCoeff S F ^ 2 else 0 := by
      simp_rw [cubeTotalInf, cubeInf_fourier]
    _ = 4 * ∑ i, ∑ S, if i ∈ S then uniformFourierCoeff S F ^ 2 else 0 := by
      rw [Finset.mul_sum]
    _ = 4 * ∑ S, ∑ i, if i ∈ S then uniformFourierCoeff S F ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = 4 * ∑ S, (S.card : ℝ) * uniformFourierCoeff S F ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro S _
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Encodes a Boolean assignment as a real sign vector, mapping `true` to `1` and `false` to
`-1` in each coordinate. -/
def signPoint {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ := fun i => if x i then 1 else -1

/-- The affine polynomial `(1 + X j) / 2` converting a sign coordinate into a zero-or-one
coordinate. -/
def booleanToSignSubst {n : ℕ} (j : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 / 2) * (1 + MvPolynomial.X j)

/-- Transforms a real multivariate polynomial by replacing every variable `X j` with
`booleanToSignSubst j`. -/
def booleanToSignPolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  P.eval₂ MvPolynomial.C booleanToSignSubst

/-- The real polynomial obtained from the integer Boolean representative of `f` by the affine
sign-coordinate substitution, representing the zero-or-one indicator of `f` on sign vectors. -/
def booleanSignRepresentative {n : ℕ} (f : (Fin n → Bool) → Bool) : MvPolynomial (Fin n) ℝ :=
  booleanToSignPolynomial (MvPolynomial.map (Int.castRingHom ℝ) (integerBooleanRepresentative f))

/-- Each affine sign-coordinate substitution polynomial has total degree at most one. -/
theorem totalDegree_booleanToSignSubst {n : ℕ} (j : Fin n) :
    (booleanToSignSubst j).totalDegree ≤ 1 := by
  unfold booleanToSignSubst
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hadd : (1 + MvPolynomial.X j : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_add (1 : MvPolynomial (Fin n) ℝ)
      (MvPolynomial.X j)).trans (by simp)
  simpa using! Nat.add_le_add
    (show (MvPolynomial.C (1 / 2) : MvPolynomial (Fin n) ℝ).totalDegree ≤ 0 by simp) hadd

/-- The degree of `booleanToSignSubst j` in any variable `i` is at most one. -/
theorem degreeOf_booleanToSignSubst {n : ℕ} (i j : Fin n) :
    (booleanToSignSubst j).degreeOf i ≤ 1 := by
  have hadd : (1 + MvPolynomial.X j : MvPolynomial (Fin n) ℝ).degreeOf i ≤ 1 :=
    (MvPolynomial.degreeOf_add_le i (1 : MvPolynomial (Fin n) ℝ)
      (MvPolynomial.X j)).trans (by
        simp only [MvPolynomial.degreeOf_one, MvPolynomial.degreeOf_X]
        split_ifs <;> norm_num)
  unfold booleanToSignSubst
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simpa using! hadd)

/-- The substitution polynomial for coordinate `j` has degree zero in every distinct coordinate
`i`. -/
theorem degreeOf_booleanToSignSubst_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (booleanToSignSubst j).degreeOf i = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hmul := MvPolynomial.degreeOf_mul_le i
    (MvPolynomial.C (1 / 2) : MvPolynomial (Fin n) ℝ) (1 + MvPolynomial.X j)
  have hadd := MvPolynomial.degreeOf_add_le i (1 : MvPolynomial (Fin n) ℝ) (MvPolynomial.X j)
  exact hmul.trans (by simpa [booleanToSignSubst, MvPolynomial.degreeOf_X, hij] using! hadd)

/-- The affine sign-coordinate substitution preserves any upper bound `d` on the total degree of
`P`. -/
theorem booleanToSignPolynomial_totalDegree {n : ℕ} (P : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hP : P.totalDegree ≤ d) : (booleanToSignPolynomial P).totalDegree ≤ d := by
  exact (cube_mv_substitution_degree P booleanToSignSubst
    (fun j => totalDegree_booleanToSignSubst j)).trans (by simpa using! hP)

/-- Applying the affine sign-coordinate substitution to a multilinear polynomial preserves
multilinearity. -/
theorem degreeOf_booleanToSignPolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (i : Fin n) :
    (booleanToSignPolynomial P).degreeOf i ≤ 1 := by
  classical
  rw [booleanToSignPolynomial, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans ?_
  apply Finset.sup_le
  intro m hm
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  simp only [MvPolynomial.degreeOf_C, zero_add]
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  calc
    (∑ j ∈ m.support, ((booleanToSignSubst j) ^ m j).degreeOf i) ≤
        ∑ j ∈ m.support, if j = i then m j else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · subst j
        simpa using! (MvPolynomial.degreeOf_pow_le i (booleanToSignSubst i) (m i)).trans
          (Nat.mul_le_mul_left (m i) (degreeOf_booleanToSignSubst i i))
      · have hz := degreeOf_booleanToSignSubst_of_ne (Ne.symm hji)
        have hp := MvPolynomial.degreeOf_pow_le i (booleanToSignSubst j) (m j)
        rw [hz, mul_zero] at hp
        simpa [hji] using! hp
    _ = m i := by
      by_cases hi : i ∈ m.support
      · simp [hi]
      · have hmi : m i = 0 := Finsupp.notMem_support_iff.mp hi
        simp [hi, hmi]
    _ ≤ 1 := MvPolynomial.degreeOf_le_iff.mp (hP i) m hm

/-- The sign-coordinate representative of `f` has total degree at most `exactDegree f`. -/
theorem booleanSignRepresentative_totalDegree {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (booleanSignRepresentative f).totalDegree ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f := by
  exact booleanToSignPolynomial_totalDegree _ (integerBooleanRepresentative_real_degree_eq f).le

/-- The sign-coordinate representative of a Boolean function has degree at most one in each
variable. -/
theorem booleanSignRepresentative_degreeOf {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    (booleanSignRepresentative f).degreeOf i ≤ 1 := by
  exact degreeOf_booleanToSignPolynomial _ (integerBooleanRepresentative_real_degreeOf f) i

/-- Evaluating the sign-coordinate representative at `signPoint x` gives `1` when `f x` is true
and `0` otherwise. -/
theorem eval_booleanSignRepresentative {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    MvPolynomial.eval (signPoint x) (booleanSignRepresentative f) = if f x then 1 else 0 := by
  rw [booleanSignRepresentative, booleanToSignPolynomial, ← MvPolynomial.eval_assoc]
  have hvars : (MvPolynomial.eval (signPoint x) ∘ booleanToSignSubst) = booleanPoint x := by
    funext j
    simp only [Function.comp_apply, booleanToSignSubst, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_add, map_one, MvPolynomial.eval_X,
      signPoint, booleanPoint]
    cases hx : x j <;> norm_num [hx]
  change MvPolynomial.eval (MvPolynomial.eval (signPoint x) ∘ booleanToSignSubst) _ = _
  rw [hvars]
  exact integerBooleanRepresentative_map_eval f x

/-- Evaluation of a multilinear polynomial at `signPoint x` is the sum over its supported
monomials of each coefficient multiplied by the Boolean character indexed by that monomial's
support. -/
theorem eval_signPoint {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (hQ : ∀ i, Q.degreeOf i ≤ 1) (x : Fin n → Bool) :
    MvPolynomial.eval (signPoint x) Q =
      ∑ m ∈ Q.support, Q.coeff m * cubeChar m.support x := by
  classical
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  have hprod : m.prod (fun i e => signPoint x i ^ e) = cubeChar m.support x := by
    change (∏ i ∈ m.support, signPoint x i ^ m i) = _
    unfold cubeChar
    apply Finset.prod_congr rfl
    intro i hi
    have hle := MvPolynomial.degreeOf_le_iff.mp (hQ i) m hm
    have hne : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hone : m i = 1 := by omega
    simp [signPoint, hone]
  change Q.coeff m * m.prod (fun i e => signPoint x i ^ e) = _
  rw [hprod]

/-- The uniform Fourier coefficient at `T` of a multilinear polynomial evaluated on sign vectors
is the sum of its coefficients at supported exponent vectors whose support is `T`. -/
theorem uniformFourierCoeff_eq_sum_coeff {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (hQ : ∀ i, Q.degreeOf i ≤ 1) (T : Finset (Fin n)) :
    uniformFourierCoeff T (fun x => MvPolynomial.eval (signPoint x) Q) =
      ∑ m ∈ Q.support, if m.support = T then Q.coeff m else 0 := by
  classical
  let a := (2 : ℝ) ^ n
  have ha : a ≠ 0 := by positivity
  calc
    uniformFourierCoeff T (fun x => MvPolynomial.eval (signPoint x) Q) =
        a⁻¹ * ∑ x, cubeChar T x *
          (∑ m ∈ Q.support, Q.coeff m * cubeChar m.support x) := by
      simp_rw [eval_signPoint Q hQ]
      rfl
    _ = a⁻¹ * ∑ m ∈ Q.support, Q.coeff m *
        (∑ x, cubeChar T x * cubeChar m.support x) := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ m ∈ Q.support, if m.support = T then Q.coeff m else 0 := by
      simp_rw [sum_cubeChar_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m.support = T
      · subst T
        simp only [if_true]
        change a⁻¹ * (Q.coeff m * a) = Q.coeff m
        rw [← mul_assoc, mul_comm a⁻¹ (Q.coeff m), mul_assoc, inv_mul_cancel₀ ha, mul_one]
      · have hTm : T ≠ m.support := Ne.symm hm
        simp [hm, hTm]

/-- The uniform Fourier coefficient at `T` of the indicator of `f` is the sum of the
coefficients in `booleanSignRepresentative f` at supported exponent vectors with support
`T`. -/
theorem uniformFourierCoeff_boolean_eq_sum_coeff {n : ℕ} (f : (Fin n → Bool) → Bool)
    (T : Finset (Fin n)) :
    uniformFourierCoeff T (fun x => if f x then (1 : ℝ) else 0) =
      ∑ m ∈ (booleanSignRepresentative f).support,
        if m.support = T then (booleanSignRepresentative f).coeff m else 0 := by
  simpa only [eval_booleanSignRepresentative] using!
    uniformFourierCoeff_eq_sum_coeff (booleanSignRepresentative f)
      (booleanSignRepresentative_degreeOf f) T

/-- The uniform Fourier coefficient of the indicator of `f` vanishes whenever its index set has
cardinality greater than `exactDegree f`. -/
theorem uniformFourierCoeff_eq_zero_of_card_gt_exactDegree {n : ℕ}
    (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hT : Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f < T.card) :
    uniformFourierCoeff T (fun x => if f x then (1 : ℝ) else 0) = 0 := by
  classical
  rw [uniformFourierCoeff_boolean_eq_sum_coeff]
  apply Finset.sum_eq_zero
  intro m hm
  have hbound := (cube_finsupp_support_card_le_sum m).trans
    ((MvPolynomial.le_totalDegree hm).trans (booleanSignRepresentative_totalDegree f))
  have hne : m.support ≠ T := by
    intro h
    rw [h] at hbound
    omega
  simp [hne]

/-- For a Boolean indicator, the sum of squared uniform Fourier coefficients equals its
coefficient at the empty set, hence its uniform mean. -/
theorem sum_uniformFourierCoeff_sq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ S, uniformFourierCoeff S (fun x => if f x then (1 : ℝ) else 0) ^ 2 =
      uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) := by
  classical
  let F : (Fin n → Bool) → ℝ := fun x => if f x then 1 else 0
  let a := (2 : ℝ) ^ n
  have ha : a ≠ 0 := by positivity
  have hparseval := sum_sq_eq_mul_sum_uniformFourierCoeff_sq F
  have hempty : uniformFourierCoeff ∅ F = a⁻¹ * ∑ x, F x := by
    simp only [uniformFourierCoeff, cubeChar, Finset.prod_empty, one_mul]
    rfl
  have hmass : a * ∑ S, uniformFourierCoeff S F ^ 2 =
      a * uniformFourierCoeff ∅ F := by
    calc
      a * ∑ S, uniformFourierCoeff S F ^ 2 = ∑ x, F x ^ 2 := hparseval.symm
      _ = ∑ x, F x := by
        apply Finset.sum_congr rfl
        intro x _
        cases hf : f x <;> simp [F, hf]
      _ = a * uniformFourierCoeff ∅ F := by
        rw [hempty, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  exact mul_left_cancel₀ ha hmass

/-- For a Boolean indicator with uniform mean `μ`, the sum of squared Fourier coefficients over
nonempty index sets is `μ - μ ^ 2`. -/
theorem sum_erase_empty_uniformFourierCoeff_sq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ S ∈ Finset.univ.erase ∅,
        uniformFourierCoeff S (fun x => if f x then (1 : ℝ) else 0) ^ 2 =
      uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) -
        uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) ^ 2 := by
  classical
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin n))))
    (fun S => uniformFourierCoeff S (fun x => if f x then (1 : ℝ) else 0) ^ 2)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [sum_uniformFourierCoeff_sq f] at he
  linarith

/-- The total influence of the zero-or-one indicator of `f` under the uniform Boolean-cube
weights is at most `exactDegree f`. -/
theorem cubeTotalInf_le_exactDegree {n : ℕ} (f : (Fin n → Bool) → Bool) :
    cubeTotalInf n (muWeight (1 / 2) n) (fun x => if f x then (1 : ℝ) else 0) ≤
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) := by
  classical
  have hweighted :
      (∑ S, (S.card : ℝ) * uniformFourierCoeff S
          (fun x => if f x then (1 : ℝ) else 0) ^ 2) ≤
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) *
          (uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) -
            uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) ^ 2) := by
    rw [← sum_erase_empty_uniformFourierCoeff_sq f, Finset.mul_sum]
    calc
      (∑ S, (S.card : ℝ) * uniformFourierCoeff S
          (fun x => if f x then (1 : ℝ) else 0) ^ 2) =
          ∑ S ∈ Finset.univ.erase ∅, (S.card : ℝ) * uniformFourierCoeff S
            (fun x => if f x then (1 : ℝ) else 0) ^ 2 := by
        symm
        simp
      _ ≤ ∑ S ∈ Finset.univ.erase ∅,
          (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) *
            uniformFourierCoeff S (fun x => if f x then (1 : ℝ) else 0) ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        by_cases hcard : S.card ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
        · have hgt : Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f < S.card :=
            Nat.lt_of_not_ge hcard
          rw [uniformFourierCoeff_eq_zero_of_card_gt_exactDegree f S hgt]
          simp
  rw [cubeTotalInf_fourier]
  have hquad : 4 *
      (uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) -
        uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) ^ 2) ≤ 1 := by
    nlinarith [sq_nonneg (2 * uniformFourierCoeff ∅
      (fun x => if f x then (1 : ℝ) else 0) - 1)]
  calc
    4 * ∑ S, (S.card : ℝ) * uniformFourierCoeff S
        (fun x => if f x then (1 : ℝ) else 0) ^ 2 ≤
        4 * ((Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) *
          (uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) -
            uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) ^ 2)) :=
      mul_le_mul_of_nonneg_left hweighted (by norm_num)
    _ = (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) *
        (4 * (uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) -
          uniformFourierCoeff ∅ (fun x => if f x then (1 : ℝ) else 0) ^ 2)) := by ring
    _ ≤ (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hquad (Nat.cast_nonneg _)
    _ = (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) := mul_one _

/-- If `f` depends on every coordinate, then `n ≤ d * 2 ^ (d - 1)`, where `d = exactDegree f`
and subtraction is in the natural numbers. -/
theorem card_le_exactDegree_mul_two_pow {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i, ∃ x, f x ≠ f (cubeFlip x i)) :
    n ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f *
      2 ^ (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f - 1) := by
  classical
  let d := Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f
  let A := (2 : ℝ) ^ (n - (d - 1))
  have hsum : (n : ℝ) * A ≤
      (2 : ℝ) ^ n * cubeTotalInf n (muWeight (1 / 2) n)
        (fun x => if f x then (1 : ℝ) else 0) := by
    calc
      (n : ℝ) * A = ∑ _i : Fin n, A := by simp
      _ ≤ ∑ i : Fin n, (2 : ℝ) ^ n * cubeInf n (muWeight (1 / 2) n)
          (fun x => if f x then (1 : ℝ) else 0) i := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_two_sub_le_mul_cubeInf f i (hdep i)
      _ = (2 : ℝ) ^ n * cubeTotalInf n (muWeight (1 / 2) n)
          (fun x => if f x then (1 : ℝ) else 0) := by
        rw [cubeTotalInf, Finset.mul_sum]
  have htotal := cubeTotalInf_le_exactDegree f
  have hbound : (n : ℝ) * A ≤ (d : ℝ) * (2 : ℝ) ^ n := by
    calc
      (n : ℝ) * A ≤ (2 : ℝ) ^ n * cubeTotalInf n (muWeight (1 / 2) n)
          (fun x => if f x then (1 : ℝ) else 0) := hsum
      _ ≤ (2 : ℝ) ^ n * (d : ℝ) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = (d : ℝ) * (2 : ℝ) ^ n := by ring
  by_cases hd : d = 0
  · have hA : 0 < A := by positivity
    have hzero : (n : ℝ) * A ≤ 0 := by simpa [hd] using! hbound
    have hnR : (n : ℝ) = 0 := by nlinarith
    have hn : n = 0 := by exact_mod_cast hnR
    simp [hn, hd, d]
  · by_cases hkn : d - 1 ≤ n
    · have hpow : (2 : ℝ) ^ n = A * (2 : ℝ) ^ (d - 1) := by
        dsimp only [A]
        rw [← pow_add]
        congr 1
        omega
      have hreal : (n : ℝ) ≤ (d : ℝ) * (2 : ℝ) ^ (d - 1) := by
        apply le_of_mul_le_mul_right _ (show 0 < A by positivity)
        calc
          (n : ℝ) * A ≤ (d : ℝ) * (2 : ℝ) ^ n := hbound
          _ = (d : ℝ) * (2 : ℝ) ^ (d - 1) * A := by rw [hpow]; ring
      exact_mod_cast hreal
    · have hnd : n < d := by omega
      exact hnd.le.trans (Nat.le_mul_of_pos_right _ (by positivity))

/-- For a natural number `n ≥ 16`, its base-two logarithm is at least four. -/
theorem four_le_logb_two_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) :
    4 ≤ Real.logb 2 (n : ℝ) := by
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h16 : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [← h16]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hnR

/-- If `n ≥ 16` and `f` depends on every coordinate, then its exact degree is at least `log₂ n -
log₂ (log₂ n) - 1`. -/
theorem logb_sub_logb_le_exactDegree {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i, ∃ x, f x ≠ f (cubeFlip x i)) (hn : 16 ≤ n) :
    Real.logb 2 (n : ℝ) - Real.logb 2 (Real.logb 2 (n : ℝ)) - 1 ≤
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) := by
  let d := Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f
  let L := Real.logb 2 (n : ℝ)
  change L - Real.logb 2 L - 1 ≤ (d : ℝ)
  have hvar : n ≤ d * 2 ^ (d - 1) := card_le_exactDegree_mul_two_pow f hdep
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [hd0] at hvar
    simp at hvar
    omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hvarR : (n : ℝ) ≤ (d : ℝ) * (2 : ℝ) ^ (d - 1) := by exact_mod_cast hvar
  have hlog : L ≤ Real.logb 2 ((d : ℝ) * (2 : ℝ) ^ (d - 1)) :=
    Real.logb_le_logb_of_le (by norm_num) hnR hvarR
  have hlog_bound : L ≤ (d : ℝ) - 1 + Real.logb 2 (d : ℝ) := by
    calc
      L ≤ Real.logb 2 ((d : ℝ) * (2 : ℝ) ^ (d - 1)) := hlog
      _ = Real.logb 2 (d : ℝ) + Real.logb 2 ((2 : ℝ) ^ (d - 1)) := by
        rw [Real.logb_mul (ne_of_gt hdR) (pow_ne_zero _ (by norm_num))]
      _ = Real.logb 2 (d : ℝ) + ((d - 1 : ℕ) : ℝ) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        ring
      _ = (d : ℝ) - 1 + Real.logb 2 (d : ℝ) := by
        rw [Nat.cast_sub hd, Nat.cast_one]
        ring
  have hL4 : 4 ≤ L := four_le_logb_two_of_sixteen_le hn
  have hlogL : 0 ≤ Real.logb 2 L := Real.logb_nonneg (by norm_num) (by linarith)
  by_cases hdL : (d : ℝ) ≤ L
  · have hlogd : Real.logb 2 (d : ℝ) ≤ Real.logb 2 L :=
      Real.logb_le_logb_of_le (by norm_num) hdR hdL
    linarith
  · have hLd : L < (d : ℝ) := lt_of_not_ge hdL
    linarith

/-- If `n ≥ 16` and `f` depends on every coordinate, then `exactMinimum f` is at least `(log₂ n)
/ 2 - 2 * log₂ (log₂ n) - 2`. This is an explicit logarithmic exact-query lower bound as in
[Beals et al., Corollary 4.4][BealsEtAl2001]. -/
theorem exactMinimum_logb_lower_bound {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i, ∃ x, f x ≠ f (cubeFlip x i)) (hn : 16 ≤ n) :
    Real.logb 2 (n : ℝ) / 2 - 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) - 2 ≤
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.exactMinimum f : ℝ) := by
  have hinv := logb_sub_logb_le_exactDegree f hdep hn
  have hdeg :=
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.minimum_degree_bounds f).1
  have hdegR : (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ) ≤
      2 * (Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.exactMinimum f : ℝ) := by
    exact_mod_cast hdeg
  have hL4 := four_le_logb_two_of_sixteen_le hn
  have hlogL : 0 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  linarith

/-- For a Boolean function depending on all coordinates, combines the bound `n ≤ d * 2 ^ (d -
1)` for `d = exactDegree f` with the explicit logarithmic lower bound on `exactMinimum f`
when `n ≥ 16` and its nonnegativity when `n < 16`. -/
theorem frontier1 {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i, ∃ x, f x ≠ f (cubeFlip x i)) :
    n ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f *
        2 ^ (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f - 1) ∧
      (16 ≤ n → Real.logb 2 (n : ℝ) / 2 -
          2 * Real.logb 2 (Real.logb 2 (n : ℝ)) - 2 ≤
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.exactMinimum f : ℝ)) ∧
      (n < 16 →
        0 ≤ (Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.exactMinimum f : ℝ)) := by
  refine ⟨card_le_exactDegree_mul_two_pow f hdep, exactMinimum_logb_lower_bound f hdep, ?_⟩
  intro _
  exact Nat.cast_nonneg _

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
