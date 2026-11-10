/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubePolynomial

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

theorem cube_bool_power {n : ℕ} (x : Fin n → Bool) (a : Fin n →₀ ℕ)
    (i : Fin n) (hi : i ∈ a.support) :
    (if x i then (1 : ℝ) else 0) ^ a i = if x i then (1 : ℝ) else 0 := by
  have hn : a i ≠ 0 := Finsupp.mem_support_iff.1 hi
  cases hx : x i <;> simp [hn]

theorem cube_mv_monomial_boolean_eval {n : ℕ} (x : Fin n → Bool) (a : Fin n →₀ ℕ) :
    a.prod (fun i k => (if x i then (1 : ℝ) else 0)^k) = cubeMonomial a.support x := by
  change (∏ i ∈ a.support, (if x i then (1 : ℝ) else 0)^a i) = _
  apply Finset.prod_congr rfl
  intro i hi
  exact cube_bool_power x a i hi

theorem cube_finsupp_support_card_le_sum {n : ℕ} (a : Fin n →₀ ℕ) :
    a.support.card ≤ a.sum (fun _ k => k) := by
  calc
    _ = ∑ _i ∈ a.support, 1 := by simp
    _ ≤ ∑ i ∈ a.support, a i := Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
    _ = _ := rfl

theorem cube_degree_of_mv_polynomial {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hd : P.totalDegree ≤ d) :
    CubeDegreeLE d (fun x => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) P) := by
  let c := fun S : Finset (Fin n) => ∑ a ∈ P.support, if a.support=S then P.coeff a else 0
  refine ⟨c, ?_, ?_⟩
  · intro S hS
    apply Finset.sum_eq_zero
    intro a ha
    have hbound :=
        (cube_finsupp_support_card_le_sum a).trans ((MvPolynomial.le_totalDegree ha).trans hd)
    have hne : a.support ≠ S := by intro he; rw [he] at hbound; omega
    simp [hne]
  · intro x
    change MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) P = ∑ S, c S*cubeMonomial S x
    rw [MvPolynomial.eval_eq]
    change (∑ a ∈ P.support, P.coeff a*a.prod (fun i k => (if x i then (1 : ℝ) else 0)^k)) = _
    simp only [cube_mv_monomial_boolean_eval]
    change (∑ a ∈ P.support, P.coeff a*cubeMonomial a.support x) = ∑ S, c S*cubeMonomial S x
    dsimp [c]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

def cubeMvPolynomial {n : ℕ} (c : Finset (Fin n) → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ S : Finset (Fin n), MvPolynomial.C (c S)*∏ i ∈ S, MvPolynomial.X i

theorem cube_degree_to_mv_polynomial {n d : ℕ} {f : (Fin n → Bool) → ℝ} (hd : CubeDegreeLE d f) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ d ∧
      ∀ x, MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) P = f x := by
  obtain ⟨c,hc,hf⟩ := hd
  refine ⟨cubeMvPolynomial c, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro S _
    by_cases hs : d < S.card
    · simp [hc S hs]
    · have hp : (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ S.card := by
        apply (MvPolynomial.totalDegree_finsetProd S _).trans
        simp
      have he := MvPolynomial.totalDegree_mul (MvPolynomial.C (c S)) (∏ i ∈ S, MvPolynomial.X i)
      simp only [MvPolynomial.totalDegree_C, zero_add] at he
      exact he.trans (hp.trans (Nat.le_of_not_gt hs))
  · intro x
    simp only [cubeMvPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_prod, MvPolynomial.eval_X]
    exact (hf x).symm

theorem cube_degree_mul {n d e : ℕ} {f g : (Fin n → Bool) → ℝ}
    (hf : CubeDegreeLE d f) (hg : CubeDegreeLE e g) : CubeDegreeLE (d+e) (fun x => f x*g x) := by
  obtain ⟨P,hP,hPe⟩ := cube_degree_to_mv_polynomial hf
  obtain ⟨Q,hQ,hQe⟩ := cube_degree_to_mv_polynomial hg
  have hdeg : (P*Q).totalDegree ≤ d+e :=
      (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hP hQ)
  have hc := cube_degree_of_mv_polynomial (P*Q) hdeg
  simpa only [MvPolynomial.eval_mul, hPe, hQe] using hc

theorem cube_degree_const (n d : ℕ) (c : ℝ) : CubeDegreeLE d (fun _ : Fin n → Bool => c) := by
  have h :=
      cube_degree_of_mv_polynomial (d := d) (MvPolynomial.C c : MvPolynomial (Fin n) ℝ) (by simp)
  simpa only [MvPolynomial.eval_C] using h

theorem cube_degree_add {n d : ℕ} {f g : (Fin n → Bool) → ℝ}
    (hf : CubeDegreeLE d f) (hg : CubeDegreeLE d g) : CubeDegreeLE d (fun x => f x+g x) := by
  obtain ⟨P,hP,hPe⟩ := cube_degree_to_mv_polynomial hf
  obtain ⟨Q,hQ,hQe⟩ := cube_degree_to_mv_polynomial hg
  have hdeg : (P+Q).totalDegree ≤ d := (MvPolynomial.totalDegree_add _ _).trans (max_le hP hQ)
  simpa only [MvPolynomial.eval_add, hPe, hQe] using cube_degree_of_mv_polynomial (P+Q) hdeg

theorem cube_degree_sub {n d : ℕ} {f g : (Fin n → Bool) → ℝ}
    (hf : CubeDegreeLE d f) (hg : CubeDegreeLE d g) : CubeDegreeLE d (fun x => f x-g x) := by
  obtain ⟨P,hP,hPe⟩ := cube_degree_to_mv_polynomial hf
  obtain ⟨Q,hQ,hQe⟩ := cube_degree_to_mv_polynomial hg
  have hdeg : (P-Q).totalDegree ≤ d := (MvPolynomial.totalDegree_sub _ _).trans (max_le hP hQ)
  simpa only [MvPolynomial.eval_sub, hPe, hQe] using cube_degree_of_mv_polynomial (P-Q) hdeg

theorem cube_mv_substitution_degree {n m k : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (Q : Fin n → MvPolynomial (Fin m) ℝ) (hQ : ∀ i, (Q i).totalDegree ≤ k) :
    (P.eval₂ MvPolynomial.C Q).totalDegree ≤ k*P.totalDegree := by
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  have hp : (a.prod (fun i e => Q i^e)).totalDegree ≤ k*a.sum (fun _ e => e) := by
    change (∏ i ∈ a.support, Q i^a i).totalDegree ≤ _
    apply (MvPolynomial.totalDegree_finsetProd a.support _).trans
    calc
      _ ≤ ∑ i ∈ a.support, k*a i := Finset.sum_le_sum fun i _ =>
        (MvPolynomial.totalDegree_pow _ _).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (a i) (hQ i))
      _ = k*a.sum (fun _ e => e) := by
        change (∑ i ∈ a.support, k*a i) = k*(∑ i ∈ a.support, a i)
        rw [Finset.mul_sum]
  have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.C (P.coeff a)) (a.prod fun i e => Q i^e)
  simp only [MvPolynomial.totalDegree_C, zero_add] at hmul
  exact hmul.trans (hp.trans (Nat.mul_le_mul_left k (MvPolynomial.le_totalDegree ha)))

theorem cube_degree_flip {n d : ℕ} {f : (Fin n → Bool) → ℝ} (hf : CubeDegreeLE d f) (i : Fin n) :
    CubeDegreeLE d (fun x => f (cubeFlip x i)) := by
  obtain ⟨P,hP,hPe⟩ := cube_degree_to_mv_polynomial hf
  let Q : Fin n → MvPolynomial (Fin n) ℝ :=
      fun j => if j=i then 1-MvPolynomial.X j else MvPolynomial.X j
  have hQ (j : Fin n) : (Q j).totalDegree ≤ 1 := by
    dsimp [Q]
    split_ifs
    · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    · simp
  have hd : (P.eval₂ MvPolynomial.C Q).totalDegree ≤ d :=
    (cube_mv_substitution_degree P Q hQ).trans (by simpa using hP)
  have he := cube_degree_of_mv_polynomial (P.eval₂ MvPolynomial.C Q) hd
  have hx (x : Fin n → Bool) :
      MvPolynomial.eval (fun j => if x j then (1 : ℝ) else 0) (P.eval₂ MvPolynomial.C Q) = f (cubeFlip x i) := by
    rw [← MvPolynomial.eval_assoc]
    have hvars : (fun j => MvPolynomial.eval (fun k => if x k then (1 : ℝ) else 0) (Q j)) =
        (fun j => if cubeFlip x i j then (1 : ℝ) else 0) := by
      ext j
      by_cases hj : j=i
      · subst j
        cases hb : x i <;> simp [Q,cubeFlip,hb]
      · simp [Q,cubeFlip,hj]
    change MvPolynomial.eval
        (fun j => MvPolynomial.eval (fun k => if x k then (1 : ℝ) else 0) (Q j)) P = _
    rw [hvars]
    exact hPe _
  simpa only [hx] using he

end Qatlib.Concepts.ProbabilityCore.DistributionAA
