/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.Closure
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Ring.Parity
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation

namespace Qatlib.Papers.FermLinOpt04.MainResults.Model

noncomputable def wordProd {n : ℕ} (l : List (Fin (2 * n))) : Fock n :=
  (l.map gen).prod

@[simp] theorem wordProd_nil {n : ℕ} : wordProd ([] : List (Fin (2 * n))) = 1 := rfl

@[simp] theorem wordProd_cons {n : ℕ} (a : Fin (2 * n)) (l : List (Fin (2 * n))) :
    wordProd (a :: l) = gen a * wordProd l := rfl

theorem wordProd_append {n : ℕ} (l₁ l₂ : List (Fin (2 * n))) :
    wordProd (l₁ ++ l₂) = wordProd l₁ * wordProd l₂ := by
  simp only [wordProd, List.map_append, List.prod_append]

theorem monomial_eq_wordProd {n : ℕ} (S : Finset (Fin (2 * n))) :
    monomial S = wordProd (S.sort (· ≤ ·)) := rfl

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, by ring⟩

theorem gen_mul_wordProd {n : ℕ} (a : Fin (2 * n)) (l : List (Fin (2 * n))) :
    gen a * wordProd l
      = ((-1 : ℂ) ^ (l.filter (fun b => b != a)).length) • (wordProd l * gen a) := by
  induction l with
  | nil => simp
  | cons x t ih =>
      have hsqa : gen a * gen a = (1 : Fock n) := by
        simp only [gen]; exact majorana_sq a
      by_cases hx : x = a
      · rw [hx]
        have hf : ((a :: t).filter (fun b => b != a)) = t.filter (fun b => b != a) := by
          simp
        have hL : gen a * (gen a * wordProd t) = wordProd t := by
          rw [← Matrix.mul_assoc, hsqa, Matrix.one_mul]
        have hR : ((-1 : ℂ) ^ (t.filter (fun b => b != a)).length) •
            ((gen a * wordProd t) * gen a) = wordProd t := by
          rw [ih, Matrix.smul_mul, Matrix.mul_assoc, hsqa, Matrix.mul_one, smul_smul,
            neg_one_pow_mul_self, one_smul]
        rw [wordProd_cons, hf]
        exact hL.trans hR.symm
      · have hf : ((x :: t).filter (fun b => b != a))
            = x :: t.filter (fun b => b != a) := by
          simp [show (x != a) = true from by simpa using! hx]
        have hanti : gen a * gen x = -(gen x * gen a) := by
          simp only [gen]; exact majorana_anticommute a x (Ne.symm hx)
        have hsign : -((((-1 : ℂ) ^ (t.filter (fun b => b != a)).length)) •
              (gen x * (wordProd t * gen a)))
            = ((-1 : ℂ) ^ ((t.filter (fun b => b != a)).length + 1)) •
              (gen x * (wordProd t * gen a)) := by
          rw [pow_succ, mul_smul, neg_one_smul, smul_neg]
        rw [wordProd_cons, hf, List.length_cons,
          ← Matrix.mul_assoc (gen a) (gen x) (wordProd t), hanti, neg_mul,
          Matrix.mul_assoc (gen x) (gen a) (wordProd t), ih, Matrix.mul_smul,
          Matrix.mul_assoc (gen x) (wordProd t) (gen a), hsign]

theorem wordProd_mul_gen {n : ℕ} (l : List (Fin (2 * n))) (a : Fin (2 * n)) (h : a ∉ l) :
    wordProd l * gen a = ((-1 : ℂ) ^ l.length) • (gen a * wordProd l) := by
  have hmain := gen_mul_wordProd a l
  rw [List.filter_bne_eq_self_of_not_mem h] at hmain
  calc wordProd l * gen a
      = (((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length)) • (wordProd l * gen a) := by
          rw [neg_one_pow_mul_self, one_smul]
    _ = ((-1 : ℂ) ^ l.length) • (((-1 : ℂ) ^ l.length) • (wordProd l * gen a)) := by
          rw [smul_smul]
    _ = ((-1 : ℂ) ^ l.length) • (gen a * wordProd l) := by rw [hmain]

theorem isOddOp_wordProd {n : ℕ} {l : List (Fin (2 * n))} (h : Odd l.length) :
    IsOddOp (wordProd l) :=
  (parity_prod (l.map gen) (fun X hX => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hX
    exact IsOddOp.gen a)).2 (by rwa [List.length_map])

theorem trace_eq_zero_of_isOddOp {n : ℕ} {X : Fock n} (h : IsOddOp X) :
    Matrix.trace X = 0 := by
  have hc : Matrix.trace (parityOp * X * parityOp) = Matrix.trace X := by
    rw [Matrix.trace_mul_comm (parityOp * X) parityOp, ← Matrix.mul_assoc, parityOp_sq,
      Matrix.one_mul]
  rw [h, Matrix.trace_neg] at hc
  have h2 : (2 : ℂ) * Matrix.trace X = 0 := by linear_combination -hc
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

theorem count_sort {n : ℕ} (S : Finset (Fin (2 * n))) (a : Fin (2 * n)) :
    (S.sort (· ≤ ·)).count a = if a ∈ S then 1 else 0 := by
  rw [List.Nodup.count (Finset.sort_nodup S (· ≤ ·))]
  simp

theorem exists_split_count_one {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : l.count a = 1) : ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ a ∉ l₁ ∧ a ∉ l₂ := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
      by_cases hx : x = a
      · rw [hx] at h ⊢
        rw [List.count_cons_self] at h
        have ht : t.count a = 0 := by omega
        exact ⟨[], t, rfl, by simp, List.count_eq_zero.mp ht⟩
      · rw [List.count_cons_of_ne hx] at h
        obtain ⟨l₁, l₂, hl, h1, h2⟩ := ih h
        refine ⟨x :: l₁, l₂, by rw [hl]; rfl, ?_, h2⟩
        intro hm
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact hx rfl
        · exact h1 hm'

theorem trace_wordProd_split {n : ℕ} (l₁ l₂ : List (Fin (2 * n))) (a : Fin (2 * n))
    (h₁ : a ∉ l₁) (h₂ : a ∉ l₂) (hlen : Even (l₁.length + l₂.length + 1)) :
    Matrix.trace (wordProd (l₁ ++ a :: l₂)) = 0 := by
  have h1 : wordProd l₁ * gen a
      = ((-1 : ℂ) ^ l₁.length) • (gen a * wordProd l₁) := wordProd_mul_gen l₁ a h₁
  have h2 : wordProd l₂ * gen a
      = ((-1 : ℂ) ^ l₂.length) • (gen a * wordProd l₂) := wordProd_mul_gen l₂ a h₂
  rw [wordProd_append, wordProd_cons]

  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (wordProd l₁ * gen a) (wordProd l₂),
    ← Matrix.mul_assoc]

  have hrot : (wordProd l₂ * wordProd l₁) * gen a
      = ((-1 : ℂ) ^ (l₁.length + l₂.length)) • (gen a * (wordProd l₂ * wordProd l₁)) := by
    calc (wordProd l₂ * wordProd l₁) * gen a
        = wordProd l₂ * (wordProd l₁ * gen a) := by rw [Matrix.mul_assoc]
      _ = wordProd l₂ * (((-1 : ℂ) ^ l₁.length) • (gen a * wordProd l₁)) := by rw [h1]
      _ = ((-1 : ℂ) ^ l₁.length) • (wordProd l₂ * (gen a * wordProd l₁)) := by
            rw [Matrix.mul_smul]
      _ = ((-1 : ℂ) ^ l₁.length) • ((wordProd l₂ * gen a) * wordProd l₁) := by
            rw [← Matrix.mul_assoc (wordProd l₂) (gen a) (wordProd l₁)]
      _ = ((-1 : ℂ) ^ l₁.length) •
            ((((-1 : ℂ) ^ l₂.length) • (gen a * wordProd l₂)) * wordProd l₁) := by rw [h2]
      _ = ((-1 : ℂ) ^ l₁.length) •
            (((-1 : ℂ) ^ l₂.length) • ((gen a * wordProd l₂) * wordProd l₁)) := by
            rw [Matrix.smul_mul]
      _ = (((-1 : ℂ) ^ l₁.length) * ((-1 : ℂ) ^ l₂.length)) •
            ((gen a * wordProd l₂) * wordProd l₁) := by rw [smul_smul]
      _ = ((-1 : ℂ) ^ (l₁.length + l₂.length)) • (gen a * (wordProd l₂ * wordProd l₁)) := by
            rw [pow_add, ← Matrix.mul_assoc (gen a) (wordProd l₂) (wordProd l₁)]
  have hc : ((-1 : ℂ) ^ (l₁.length + l₂.length)) = -1 := by
    have hodd : Odd (l₁.length + l₂.length) := by
      obtain ⟨k, hk⟩ := hlen
      exact ⟨k - 1, by omega⟩
    exact hodd.neg_one_pow
  have hcyc : Matrix.trace ((wordProd l₂ * wordProd l₁) * gen a)
      = Matrix.trace (gen a * (wordProd l₂ * wordProd l₁)) :=
    Matrix.trace_mul_comm (wordProd l₂ * wordProd l₁) (gen a)
  have hsc : Matrix.trace ((wordProd l₂ * wordProd l₁) * gen a)
      = (-1) * Matrix.trace (gen a * (wordProd l₂ * wordProd l₁)) := by
    rw [hrot, Matrix.trace_smul, hc, smul_eq_mul]
  rw [hcyc] at hsc ⊢
  have htwo : (2 : ℂ) * Matrix.trace (gen a * (wordProd l₂ * wordProd l₁)) = 0 := by
    linear_combination hsc
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem trace_monomial_mul_offdiag {n : ℕ} {S T : Finset (Fin (2 * n))} (hST : S ≠ T) :
    Matrix.trace (monomial S * monomial T) = 0 := by
  rw [monomial_eq_wordProd, monomial_eq_wordProd, ← wordProd_append]
  rcases Nat.even_or_odd ((S.sort (· ≤ ·) ++ T.sort (· ≤ ·)).length) with heven | hodd
  · have hex : ∃ a : Fin (2 * n), (a ∈ S ∧ a ∉ T) ∨ (a ∈ T ∧ a ∉ S) := by
      by_contra hcon
      apply hST
      ext a
      constructor
      · intro ha
        by_contra hna
        exact hcon ⟨a, Or.inl ⟨ha, hna⟩⟩
      · intro ha
        by_contra hna
        exact hcon ⟨a, Or.inr ⟨ha, hna⟩⟩
    obtain ⟨a, ha | ha⟩ := hex
    · have hcnt : (S.sort (· ≤ ·) ++ T.sort (· ≤ ·)).count a = 1 := by
        rw [List.count_append, count_sort, count_sort, if_pos ha.1, if_neg ha.2, add_zero]
      obtain ⟨l₁, l₂, hl, h1, h2⟩ := exists_split_count_one hcnt
      rw [hl]
      refine trace_wordProd_split l₁ l₂ a h1 h2 ?_
      have heven' : Even ((l₁ ++ a :: l₂).length) := by rw [← hl]; exact heven
      simpa [List.length_append, List.length_cons, Nat.add_assoc] using! heven'
    · have hcnt : (S.sort (· ≤ ·) ++ T.sort (· ≤ ·)).count a = 1 := by
        rw [List.count_append, count_sort, count_sort, if_neg ha.2, if_pos ha.1, zero_add]
      obtain ⟨l₁, l₂, hl, h1, h2⟩ := exists_split_count_one hcnt
      rw [hl]
      refine trace_wordProd_split l₁ l₂ a h1 h2 ?_
      have heven' : Even ((l₁ ++ a :: l₂).length) := by rw [← hl]; exact heven
      simpa [List.length_append, List.length_cons, Nat.add_assoc] using! heven'
  · exact trace_eq_zero_of_isOddOp (isOddOp_wordProd hodd)

theorem trace_one_fock {n : ℕ} : Matrix.trace (1 : Fock n) = ((2 : ℂ) ^ n) := by
  rw [Matrix.trace_one]
  have hcard : Fintype.card (Reg n) = 2 ^ n := card_reg n
  rw [hcard]
  push_cast
  ring

theorem wordProd_self {n : ℕ} (l : List (Fin (2 * n))) (h : l.Nodup) :
    wordProd (l ++ l) = ((-1 : ℂ) ^ Nat.choose l.length 2) • (1 : Fock n) := by
  induction l with
  | nil => simp
  | cons x t ih =>
      obtain ⟨hx, ht⟩ := List.nodup_cons.mp h
      have hcomm : wordProd t * gen x = ((-1 : ℂ) ^ t.length) • (gen x * wordProd t) :=
        wordProd_mul_gen t x hx
      obtain hε := ih ht
      have hsqa : gen x * gen x = (1 : Fock n) := by
        simp only [gen]; exact majorana_sq x
      have hkey : gen x * ((gen x * wordProd t) * wordProd t)
          = wordProd t * wordProd t := by
        rw [Matrix.mul_assoc (gen x) (wordProd t) (wordProd t),
          ← Matrix.mul_assoc (gen x) (gen x) (wordProd t * wordProd t), hsqa,
          Matrix.one_mul]
      have hchoose : Nat.choose (x :: t).length 2
          = t.length + Nat.choose t.length 2 := by
        rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]
      rw [hchoose, pow_add]
      have hstep : wordProd (x :: t) * wordProd (x :: t)
          = gen x * ((wordProd t * gen x) * wordProd t) := by
        rw [wordProd_cons,
          Matrix.mul_assoc (gen x) (wordProd t) (gen x * wordProd t)]
        congr 1
        rw [Matrix.mul_assoc]
      rw [wordProd_append, hstep, hcomm, Matrix.smul_mul, Matrix.mul_smul, hkey,
        ← wordProd_append, hε, smul_smul]

theorem monomial_mul_self {n : ℕ} (S : Finset (Fin (2 * n))) :
    monomial S * monomial S
      = ((-1 : ℂ) ^ Nat.choose S.card 2) • (1 : Fock n) := by
  have h := wordProd_self (S.sort (· ≤ ·)) (Finset.sort_nodup S (· ≤ ·))
  rw [monomial_eq_wordProd, ← wordProd_append]
  simpa [Finset.length_sort] using! h

theorem trace_monomial_mul_self {n : ℕ} (S : Finset (Fin (2 * n))) :
    Matrix.trace (monomial S * monomial S)
      = ((-1 : ℂ) ^ Nat.choose S.card 2) * ((2 : ℂ) ^ n) := by
  rw [monomial_mul_self, Matrix.trace_smul, trace_one_fock, smul_eq_mul]

theorem i_pow_choose (p : ℕ) :
    Complex.I ^ p * ((-1 : ℂ) ^ Nat.choose (2 * p) 2) = (-Complex.I) ^ p := by
  have hcho : Nat.choose (2 * p) 2 = p * (2 * p - 1) := by
    rw [Nat.choose_two_right]
    have h2 : (2 * p) * (2 * p - 1) = 2 * (p * (2 * p - 1)) := by ring
    rw [h2, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  have hsign : ((-1 : ℂ) ^ (p * (2 * p - 1))) = (-1 : ℂ) ^ p := by
    rcases p with _ | q
    · simp
    · have h2p : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
      have hexp : (q + 1) * (2 * (q + 1) - 1) = (q + 1) + 2 * ((q + 1) * q) := by
        rw [h2p]; ring
      rw [hexp, pow_add, pow_mul, show ((-1 : ℂ) ^ 2) = 1 by norm_num, one_pow, mul_one]
  rw [hcho, hsign, ← mul_pow, show Complex.I * (-1 : ℂ) = -Complex.I by ring]

theorem trace_gaussianOp_mul_monomial_odd {n : ℕ}
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ) {T : Finset (Fin (2 * n))}
    (hT : Odd T.card) : Matrix.trace (gaussianOp M C * monomial T) = 0 := by
  rw [gaussianOp, Matrix.smul_mul, Finset.sum_mul, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_sum, Finset.mul_sum, Finset.sum_eq_zero]
  intro S hS
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hne : S ≠ T := by
    intro h
    rw [← h] at hT
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hS).2
    obtain ⟨j, hj⟩ := hT
    omega
  rw [trace_monomial_mul_offdiag hne, mul_zero, mul_zero]

theorem trace_gaussianOp_mul_monomial_even {n : ℕ}
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (C : ℂ) {T : Finset (Fin (2 * n))}
    (hT : Even T.card) :
    Matrix.trace (gaussianOp M C * monomial T)
      = C * ((2 : ℂ) ^ n) * (-Complex.I) ^ (T.card / 2) * pfaffianSub M T := by
  rw [gaussianOp, Matrix.smul_mul, Finset.sum_mul, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_sum, Finset.mul_sum,
    Finset.sum_eq_single T
      (fun S _ hST => by
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_monomial_mul_offdiag hST,
          mul_zero, mul_zero])
      (fun hTnot => by
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩) hTnot)]
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_monomial_mul_self]
  obtain ⟨p, hp⟩ := hT
  have hp2 : T.card / 2 = p := by omega
  have hpos : T.card = 2 * p := by omega
  rw [hp2, hpos]
  have hI := i_pow_choose p
  linear_combination (C * (2:ℂ)^n * pfaffianSub M T) * hI

end Qatlib.Papers.FermLinOpt04.MainResults.Model
