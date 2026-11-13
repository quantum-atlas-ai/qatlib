/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs

/-!
# Degree lower bounds for symmetric Boolean functions

The predicates `Symmetric` and `Nonconstant` characterize nonconstant Boolean functions
depending only on Hamming weight. Layer averaging converts an exact representing polynomial into
a nonconstant univariate polynomial, giving `n + 1 ≤ 2 * exactDegree f` and the query
consequence `n + 1 ≤ 4 * exactMinimum f`. These constructions support the symmetric-function
analysis of [BealsEtAl2001].

## Main statements

* `symmetric_exactDegree_lower`: A nonconstant symmetric Boolean function on `n` bits satisfies
  `n + 1 ≤ 2 * exactDegree f`.
* `symmetric_exactMinimum_lower`: A nonconstant symmetric Boolean function on `n` bits satisfies
  `n + 1 ≤ 4 * exactMinimum f`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.SymDegree

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open scoped Classical BigOperators

/-- The condition that equal Hamming weights give equal values of the Boolean function. -/
def Symmetric {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, boolWeight x = boolWeight y → f x = f y

/-- The condition that the Boolean function takes distinct values on some pair of inputs. -/
def Nonconstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y : Fin n → Bool, f x ≠ f y

/-- The Boolean characteristic word of the finite set `T`. -/
def wordOn {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ T)

/-- Evaluation of a real multivariate polynomial at `boolPoint g` agrees with `boolEval p g`. -/
theorem eval_boolPoint_eq_boolEval {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (g : Fin n → Bool) : p.eval (boolPoint g) = boolEval p g := rfl

/-- The Hamming weight of the characteristic word of `T` is `T.card`. -/
theorem boolWeight_wordOn {n : ℕ} (T : Finset (Fin n)) :
    boolWeight (wordOn T) = T.card := by
  unfold boolWeight wordOn
  rw [boolSupp_decide]

/-- For every `k ≤ n`, there exists a Boolean word of length `n` and Hamming weight `k`. -/
theorem exists_word_weight {n k : ℕ} (hk : k ≤ n) :
    ∃ w : Fin n → Bool, boolWeight w = k := by
  obtain ⟨T, -, hcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := k)
      (by simpa using! hk)
  exact ⟨wordOn T, by rw [boolWeight_wordOn, hcard]⟩

/-- For a symmetric function exactly represented by `p`, its layer average at a valid weight
equals the Boolean indicator of the function's value on any word of that weight. -/
theorem layerAverage_of_represents_symmetric {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hsym : Symmetric f) {p : MvPolynomial (Fin n) ℝ}
    (hp : ∀ g : Fin n → Bool, boolEval p g = if f g then (1 : ℝ) else 0)
    {k : ℕ} (hk : k ≤ n) {w : Fin n → Bool} (hw : boolWeight w = k) :
    layerAverage p k = if f w then (1 : ℝ) else 0 := by
  classical
  have hterm : ∀ g : {g : Fin n → Bool // boolWeight g = k},
      p.eval (boolPoint g.1) = if f w then (1 : ℝ) else 0 := by
    intro g
    have hval : f g.1 = f w := hsym g.1 w (g.2.trans hw.symm)
    rw [eval_boolPoint_eq_boolEval, hp g.1, hval]
  have hsum : layerSum p k
      = (Fintype.card {g : Fin n → Bool // boolWeight g = k} : ℝ)
          * (if f w then (1 : ℝ) else 0) := by
    rw [layerSum, Finset.sum_congr rfl (fun g _ => hterm g)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card {g : Fin n → Bool // boolWeight g = k} : ℝ)
      = (Nat.choose n k : ℝ) := by
    exact_mod_cast card_weight_eq_choose (I := Fin n) n (by simp) k
  have hck : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  rw [layerAverage, hsum, hcard]
  have hfc : Fintype.card (Fin n) = n := by simp
  rw [hfc]
  field_simp [hck]

/-- The averaging polynomial of an exact representation of a nonconstant symmetric Boolean
function is unequal to every constant polynomial. -/
theorem avgPoly_ne_C {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hsym : Symmetric f) (hnc : Nonconstant f) {p : MvPolynomial (Fin n) ℝ}
    (hp : ∀ g : Fin n → Bool, boolEval p g = if f g then (1 : ℝ) else 0) :
    ∀ c : ℝ, avgPoly p ≠ Polynomial.C c := by
  classical
  intro c hconst
  obtain ⟨x, y, hxy⟩ := hnc
  have hxn : boolWeight x ≤ n := by
    have := Finset.card_le_univ (boolSupp x)
    simpa [boolWeight] using! this
  have hyn : boolWeight y ≤ n := by
    have := Finset.card_le_univ (boolSupp y)
    simpa [boolWeight] using! this
  have hxq : (avgPoly p).eval ((boolWeight x : ℕ) : ℝ)
      = if f x then (1 : ℝ) else 0 := by
    rw [← layerAverage_eq_avgPoly p (boolWeight x) (by simpa using! hxn)]
    exact layerAverage_of_represents_symmetric hsym hp hxn rfl
  have hyq : (avgPoly p).eval ((boolWeight y : ℕ) : ℝ)
      = if f y then (1 : ℝ) else 0 := by
    rw [← layerAverage_eq_avgPoly p (boolWeight y) (by simpa using! hyn)]
    exact layerAverage_of_represents_symmetric hsym hp hyn rfl
  have hvals : (if f x then (1 : ℝ) else 0) ≠ (if f y then (1 : ℝ) else 0) := by
    intro h
    apply hxy
    by_cases hx : f x <;> by_cases hy : f y <;> simp_all
  simp only [hconst, Polynomial.eval_C] at hxq hyq
  exact hvals (hxq.symm.trans hyq)

/-- If `p` exactly represents a nonconstant symmetric Boolean function on `n` bits, then `n + 1
≤ 2 * p.totalDegree`. -/
theorem symmetric_degree_lower {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hsym : Symmetric f) (hnc : Nonconstant f) {p : MvPolynomial (Fin n) ℝ}
    (hp : ∀ g : Fin n → Bool, boolEval p g = if f g then (1 : ℝ) else 0) :
    n + 1 ≤ 2 * p.totalDegree := by
  classical
  have hne : ∀ c : ℝ, avgPoly p ≠ Polynomial.C c := avgPoly_ne_C hsym hnc hp
  have hq0 : avgPoly p ≠ 0 := by
    intro h
    exact hne 0 (by simpa using! h)
  have hq1 : avgPoly p - 1 ≠ 0 := by
    intro h
    have hq : avgPoly p = Polynomial.C 1 := by
      rw [Polynomial.C_1]
      exact sub_eq_zero.mp h
    exact hne 1 hq
  have hrne : avgPoly p * (avgPoly p - 1) ≠ 0 := mul_ne_zero hq0 hq1

  have hroot : ∀ j ∈ (Finset.range (n + 1)),
      (j : ℝ) ∈ (avgPoly p * (avgPoly p - 1)).roots := by
    intro j hj
    rw [Polynomial.mem_roots hrne]
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨w, hw⟩ := exists_word_weight (n := n) hjn
    have hqj : (avgPoly p).eval (j : ℝ) = if f w then (1 : ℝ) else 0 := by
      rw [← layerAverage_eq_avgPoly p j (by simpa using! hjn)]
      exact layerAverage_of_represents_symmetric hsym hp hjn hw
    have hv : (avgPoly p).eval (j : ℝ) = 0 ∨ (avgPoly p).eval (j : ℝ) = 1 := by
      cases f w <;> simp [hqj]
    show (avgPoly p * (avgPoly p - 1)).eval (j : ℝ) = 0
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one]
    rcases hv with hv | hv <;> rw [hv] <;> ring
  have hcard : n + 1 ≤ (avgPoly p * (avgPoly p - 1)).natDegree := by
    have hZ : (((Finset.range (n + 1)).image (fun j : ℕ => (j : ℝ))).val)
        ⊆ (avgPoly p * (avgPoly p - 1)).roots := by
      intro a ha
      rw [Finset.mem_val] at ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      exact hroot j hj
    have h := Polynomial.card_le_degree_of_subset_roots hZ
    have hZcard : ((Finset.range (n + 1)).image (fun j : ℕ => (j : ℝ))).card = n + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => by exact_mod_cast hab),
        Finset.card_range]
    rw [hZcard] at h
    exact h
  have hdeg : (avgPoly p * (avgPoly p - 1)).natDegree ≤ 2 * p.totalDegree := by
    have h1 : (avgPoly p * (avgPoly p - 1)).natDegree
        ≤ (avgPoly p).natDegree + (avgPoly p - 1).natDegree :=
      Polynomial.natDegree_mul_le
    have h2 : (avgPoly p - 1).natDegree ≤ (avgPoly p).natDegree := by
      have hsub := Polynomial.natDegree_sub_le (avgPoly p) (1 : Polynomial ℝ)
      simp only [Polynomial.natDegree_one] at hsub
      exact hsub.trans_eq (max_eq_left (Nat.zero_le _))
    have h3 : (avgPoly p).natDegree ≤ p.totalDegree := avgPoly_natDegree_le p
    omega
  omega

/-- A nonconstant symmetric Boolean function on `n` bits satisfies `n + 1 ≤ 2 * exactDegree f`.
See [Beals et al., 2001][BealsEtAl2001]. -/
theorem symmetric_exactDegree_lower {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hsym : Symmetric f) (hnc : Nonconstant f) :
    n + 1 ≤ 2 * exactDegree f := by
  classical
  have hne : {p : MvPolynomial (Fin n) ℝ |
      ∀ g, boolEval p g = if f g then (1 : ℝ) else 0}.Nonempty :=
    ⟨canonPoly f, fun g => canonPoly_represents f g⟩
  have hfinal : ∀ d ∈ (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) ''
      {p | ∀ g, boolEval p g = if f g then (1 : ℝ) else 0}, n + 1 ≤ 2 * d := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := hd
    exact symmetric_degree_lower hsym hnc hp
  exact hfinal _ (Nat.sInf_mem (hne.image fun p => p.totalDegree))

/-- A nonconstant symmetric Boolean function on `n` bits satisfies `n + 1 ≤ 4 * exactMinimum f`.
See [Beals et al., 2001][BealsEtAl2001]. -/
theorem symmetric_exactMinimum_lower {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hsym : Symmetric f) (hnc : Nonconstant f) :
    n + 1 ≤ 4 * exactMinimum f := by
  have hdeg := symmetric_exactDegree_lower hsym hnc
  have hmin : exactDegree f ≤ 2 * exactMinimum f := (minimum_degree_bounds f).1
  omega

end Qatlib.Papers.PolyMethod01.SymDegree
