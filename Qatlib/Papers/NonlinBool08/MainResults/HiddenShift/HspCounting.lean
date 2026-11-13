/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.HiddenShift.HspReduction

/-!
# Counting informative hidden-shift samples

Counts binary vectors and sample tuples compatible with a hidden shift. A union bound over
nonzero common orthogonal vectors bounds `badTuples`, yielding a lower bound of one half on the
fraction of informative tuples under the stated sample-count inequality. See [Roetteler2008].

## Main statements

* `card_bad_le`: bad tuples are bounded by a union of hyperplane tuple sets.
* `theorem7_linear_queries`: at least half of tuples are good under the numerical hypothesis.
* `theorem7_two_n`: 2n samples satisfy the good-tuple bound for positive n.

## References

* [Roetteler, 2008][Roetteler2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.HiddenShift

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

/-- The binary dot product is symmetric. -/
lemma dot_swap {n : ℕ} (x y : BVec n) : dot x y = dot y x := by
  simp only [dot, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The sign character is one exactly at the zero binary value. -/
lemma eps_eq_one_iff (z : ZMod 2) : eps z = 1 ↔ z = 0 := by
  unfold eps
  by_cases h : z = 0
  · simp [h]
  · simp [h]

/-- The sign character is negative one exactly at nonzero binary values. -/
lemma eps_eq_neg_one_iff (z : ZMod 2) : eps z = -1 ↔ z ≠ 0 := by
  unfold eps
  by_cases h : z = 0
  · simp [h]
  · simp [h]

/-- A nonzero binary vector has exactly `2 ^ (n - 1)` orthogonal binary vectors. -/
theorem card_orth {n : ℕ} (v : BVec n) (hv : v ≠ 0) :
    (Finset.univ.filter (fun x : BVec n => dot x v = 0)).card = 2 ^ (n - 1) := by
  classical
  have hnv : n ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim v 0)
  set S : Finset (BVec n) := Finset.univ.filter (fun x => dot x v = 0) with hS
  set T : Finset (BVec n) := Finset.univ.filter (fun x => ¬ dot x v = 0) with hT
  have hST : S.card + T.card = 2 ^ n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (BVec n))) (p := fun x => dot x v = 0)
    rw [Finset.card_univ, BentCore.card_bvec_nat] at h
    simpa [hS, hT] using h
  have hSval : (∑ x ∈ S, eps (dot x v)) = (S.card : ℤ) := by
    have hterm : ∀ x ∈ S, eps (dot x v) = (1 : ℤ) := by
      intro x hx
      rw [hS, Finset.mem_filter] at hx
      exact (eps_eq_one_iff _).mpr hx.2
    have hsum : (∑ x ∈ S, eps (dot x v)) = ∑ _x ∈ S, (1 : ℤ) :=
      Finset.sum_congr rfl hterm
    rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hTval : (∑ x ∈ T, eps (dot x v)) = -(T.card : ℤ) := by
    have hterm : ∀ x ∈ T, eps (dot x v) = (-1 : ℤ) := by
      intro x hx
      rw [hT, Finset.mem_filter] at hx
      exact (eps_eq_neg_one_iff _).mpr hx.2
    have hsum : (∑ x ∈ T, eps (dot x v)) = ∑ _x ∈ T, (-1 : ℤ) :=
      Finset.sum_congr rfl hterm
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    ring
  have htotal : (∑ x : BVec n, eps (dot x v)) = 0 := by
    have h := sum_eps_dot v
    rw [if_neg hv] at h
    rw [show (∑ x : BVec n, eps (dot x v)) = ∑ x : BVec n, eps (dot v x) from
      Finset.sum_congr rfl (fun x _ => by rw [dot_swap])]
    exact h
  have hsplit : (∑ x ∈ S, eps (dot x v)) + (∑ x ∈ T, eps (dot x v)) = 0 := by
    have h := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (BVec n))) (p := fun x => dot x v = 0)
      (f := fun x => eps (dot x v))
    rw [htotal] at h
    simpa [hS, hT] using h
  rw [hSval, hTval] at hsplit

  have hSZ : (S.card : ℤ) = (2 : ℤ) ^ (n - 1) := by
    have heq : (S.card : ℤ) = (T.card : ℤ) := by linarith
    have h2 : (S.card : ℤ) + (T.card : ℤ) = (2 : ℤ) ^ n := by
      exact_mod_cast hST
    have hpow : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ']
    rw [hpow] at h2
    linarith
  exact_mod_cast hSZ

/-- The finite set of pairs `(x, b)` satisfying the hidden-shift constraint `dot x s + b = 0`. -/
def compat {n : ℕ} (s : BVec n) : Finset (BVec n × ZMod 2) :=
  Finset.univ.filter (fun a => dot a.1 s + a.2 = 0)

/-- Exactly `2 ^ n` binary vector-bit pairs satisfy the constraint for a fixed shift. -/
theorem card_compat {n : ℕ} (s : BVec n) : (compat s).card = 2 ^ n := by
  classical

  have hbij : (compat s) = (Finset.univ : Finset (BVec n)).image
      (fun x => (x, dot x s)) := by
    ext a
    simp only [compat, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ha

      have h2 : a.2 = dot a.1 s := by
        calc a.2 = a.2 + 0 := (add_zero _).symm
          _ = a.2 + (dot a.1 s + dot a.1 s) := by rw [BentCore.add_self_zmod2]
          _ = (dot a.1 s + a.2) + dot a.1 s := by abel
          _ = 0 + dot a.1 s := by rw [ha]
          _ = dot a.1 s := zero_add _
      exact ⟨a.1, Prod.ext rfl h2.symm⟩
    · rintro ⟨x, hx⟩
      have h1 : a.1 = x := by rw [← hx]
      have h2 : a.2 = dot x s := by rw [← hx]
      rw [h1, h2, BentCore.add_self_zmod2]
  rw [hbij, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h),
    Finset.card_univ, BentCore.card_bvec_nat]

/-- The condition that all vectors in a sample tuple share a nonzero orthogonal vector. -/
def isBadVec {n k : ℕ} (x : Fin k → BVec n) : Prop :=
  ∃ δ : BVec n, δ ≠ 0 ∧ ∀ i, dot (x i) δ = 0

/-- The finite set of binary vectors orthogonal to `δ`. -/
def hyper {n : ℕ} (δ : BVec n) : Finset (BVec n) :=
  Finset.univ.filter (fun x => dot x δ = 0)

/-- The hyperplane orthogonal to a nonzero vector has `2 ^ (n - 1)` elements. -/
lemma hyper_card {n : ℕ} {δ : BVec n} (hδ : δ ≠ 0) : (hyper δ).card = 2 ^ (n - 1) :=
  card_orth δ hδ

/-- The finite set of length-`k` tuples whose entries are all orthogonal to `δ`. -/
noncomputable def hyperTuples {n k : ℕ} (δ : BVec n) : Finset (Fin k → BVec n) :=
  Finset.univ.filter (fun x => ∀ i, dot (x i) δ = 0)

/-- The finite set of sample tuples possessing a common nonzero orthogonal vector. -/
noncomputable def badTuples {n k : ℕ} : Finset (Fin k → BVec n) := by
  classical
  exact Finset.univ.filter (fun x => isBadVec x)

/-- The finite set of sample tuples with no common nonzero orthogonal vector. -/
noncomputable def goodTuples {n k : ℕ} : Finset (Fin k → BVec n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ isBadVec x)

/-- The number of length-`k` tuples in a fixed orthogonal set is its cardinality raised to `k`. -/
lemma card_hyperTuples {n k : ℕ} (δ : BVec n) :
    (hyperTuples (k := k) δ).card = (hyper δ).card ^ k := by
  classical
  have hset : hyperTuples (k := k) δ = Fintype.piFinset (fun _ : Fin k => hyper δ) := by
    ext x
    simp [hyperTuples, hyper, Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The number of bad length-`k` tuples is at most `(2 ^ n - 1) * (2 ^ (n - 1)) ^ k`. -/
lemma card_bad_le {n k : ℕ} :
    (badTuples (n := n) (k := k)).card ≤ (2 ^ n - 1) * (2 ^ (n - 1)) ^ k := by
  classical
  have hsub : (badTuples (n := n) (k := k))
      ⊆ (Finset.univ \ {(0 : BVec n)}).biUnion (fun δ => hyperTuples (k := k) δ) := by
    intro x hx
    rw [badTuples, Finset.mem_filter] at hx
    obtain ⟨-, δ, hδ, horth⟩ := hx
    rw [Finset.mem_biUnion]
    refine ⟨δ, ?_, ?_⟩
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨Finset.mem_univ δ, hδ⟩
    · rw [hyperTuples, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, horth⟩
  calc (badTuples (n := n) (k := k)).card
      ≤ ((Finset.univ \ {(0 : BVec n)}).biUnion (fun δ => hyperTuples (k := k) δ)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ δ ∈ Finset.univ \ {(0 : BVec n)}, (hyperTuples (k := k) δ).card :=
        Finset.card_biUnion_le
    _ = ∑ _δ ∈ Finset.univ \ {(0 : BVec n)}, (2 ^ (n - 1)) ^ k := by
        apply Finset.sum_congr rfl
        intro δ hδ
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hδ
        rw [card_hyperTuples, hyper_card hδ.2]
    _ = (Finset.univ \ {(0 : BVec n)}).card * (2 ^ (n - 1)) ^ k := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (2 ^ n - 1) * (2 ^ (n - 1)) ^ k := by
        rw [Finset.card_sdiff_of_subset
          (Finset.singleton_subset_iff.mpr (Finset.mem_univ 0)),
          Finset.card_singleton, Finset.card_univ, BentCore.card_bvec_nat]

/-- If `2 ^ n - 1 < 2 ^ (k - 1)`, at least half of all length-`k` binary-vector tuples have no
common nonzero orthogonal vector. See [Roetteler, Theorem 7][Roetteler2008]. -/
theorem theorem7_linear_queries {n k : ℕ} (hk : 2 ^ n - 1 < 2 ^ (k - 1)) :
    2 * (goodTuples (n := n) (k := k)).card ≥ 2 ^ (n * k) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hgood : (goodTuples (n := 0) (k := k)) = Finset.univ := by
      ext x
      simp only [goodTuples, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _ hbad
        obtain ⟨δ, hδ, -⟩ := hbad
        exact hδ (Subsingleton.elim δ 0)
    rw [hgood, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, BentCore.card_bvec_nat,
      Nat.zero_mul, pow_zero]
    norm_num
  · have hsplit : (goodTuples (n := n) (k := k)).card + (badTuples (n := n) (k := k)).card
        = 2 ^ (n * k) := by
      have hunion : (goodTuples (n := n) (k := k)) ∪ (badTuples (n := n) (k := k))
          = Finset.univ := by
        ext x
        simp only [goodTuples, badTuples, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and]
        by_cases h : isBadVec x <;> simp [h]
      have hdisj : Disjoint (goodTuples (n := n) (k := k)) (badTuples (n := n) (k := k)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [goodTuples, badTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        exact hx1 hx2
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, BentCore.card_bvec_nat, ← pow_mul]
    have hbad := card_bad_le (n := n) (k := k)

    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [Nat.reduceSub, pow_zero] at hk
        have h2n : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hnpos
        omega
      · exact hkpos
    have hstep1 : 2 * (2 ^ n - 1) ≤ 2 ^ k := by
      have h1 : 2 * (2 ^ n - 1) ≤ 2 * 2 ^ (k - 1) :=
        Nat.mul_le_mul_left 2 (Nat.le_of_lt hk)
      have h2 : 2 * 2 ^ (k - 1) = 2 ^ k := by
        conv_rhs => rw [show k = (k - 1) + 1 from by omega]
        rw [pow_succ, mul_comm]
      omega
    have hn1 : 2 ^ (n - 1) * 2 = 2 ^ n := by
      conv_rhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ]
    have hpow : (2 ^ (n - 1)) ^ k * 2 ^ k = 2 ^ (n * k) := by
      rw [← mul_pow, hn1, ← pow_mul]
    have hbad2 : 2 * (badTuples (n := n) (k := k)).card ≤ 2 ^ (n * k) := by
      have h1 : 2 * (badTuples (n := n) (k := k)).card
          ≤ 2 * ((2 ^ n - 1) * (2 ^ (n - 1)) ^ k) :=
        Nat.mul_le_mul_left 2 hbad
      have h2 : 2 * ((2 ^ n - 1) * (2 ^ (n - 1)) ^ k)
          = (2 * (2 ^ n - 1)) * (2 ^ (n - 1)) ^ k := by ring
      have h3 : (2 * (2 ^ n - 1)) * (2 ^ (n - 1)) ^ k
          ≤ 2 ^ k * (2 ^ (n - 1)) ^ k := Nat.mul_le_mul_right _ hstep1
      have h4 : 2 ^ k * (2 ^ (n - 1)) ^ k = 2 ^ (n * k) := by
        rw [mul_comm]
        exact hpow
      omega
    omega

/-- For positive `n`, at least half of all length-`2 * n` tuples have no common nonzero
orthogonal vector. See [Roetteler, Theorem 7][Roetteler2008]. -/
theorem theorem7_two_n {n : ℕ} (hn : 1 ≤ n) :
    2 * (goodTuples (n := n) (k := 2 * n)).card ≥ 2 ^ (n * (2 * n)) := by
  refine theorem7_linear_queries (n := n) (k := 2 * n) ?_
  have h1 : n ≤ 2 * n - 1 := by omega
  have h2 : 2 ^ n ≤ 2 ^ (2 * n - 1) :=
    pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) h1
  have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

end Qatlib.Papers.NonlinBool08.MainResults.HiddenShift
