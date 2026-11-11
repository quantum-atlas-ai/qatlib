/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# VarTimeSearch23 — Lemma 3 (arithmetic core)

Source: Ambainis, Kokainis, Vihrovs, *Improved Algorithm and Lower Bound for
Variable Time Quantum Search*, fixed arXiv:2302.06749v3 (2023-08-02).

Lemma 3 (p.5; proof in Appendix A, p.14–15) has three arithmetic parts about
the product in Eq. (3.3):

* C-1: if `9^j s_j / n ≤ 9/4` then `1 − 4 s_j 9^j / (27 n) ≥ 2/3`;
* C-2: `∏_{j=1}^{ℓ−1} (1 − 4 s_j 9^j / (27 n)) ≥ 2/3`;
* C-3: `9^ℓ s_ℓ ≥ 9^ℓ s_d ≥ n`.

The source proves C-1 and C-2 from inequality (A.2)
`∑_{j=1}^{ℓ−1} 9^j s_j < 9n/4` (via the generalized Bernoulli inequality), and
C-3 from `s_ℓ ≥ s_d = m` and the choice of `ℓ`, which gives `9^ℓ ≥ n/m`.
This module states C-1 pointwise, C-2 under the source's (A.2), and C-3 under
`s_d = m`, `s_d ≤ s_ℓ` and `n ≤ 9^ℓ m`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.VarTimeSearch23.MainResults

/-- Generalized Bernoulli inequality, used in the source's proof of C-2:
for `0 ≤ x_j ≤ 1`, `∏_{j∈t} (1 − x_j) ≥ 1 − ∑_{j∈t} x_j`. -/
private lemma prod_one_sub_ge_one_sub_sum {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (x : ι → ℝ) (hx0 : ∀ i ∈ t, 0 ≤ x i)
    (hx1 : ∀ i ∈ t, x i ≤ 1) :
    1 - ∑ i ∈ t, x i ≤ ∏ i ∈ t, (1 - x i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have ha0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a t)
      have ha1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a t)
      have ht0 : ∀ i ∈ t, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
      have ht1 : ∀ i ∈ t, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
      have ih' := ih ht0 ht1
      have hsum0 : 0 ≤ ∑ i ∈ t, x i := Finset.sum_nonneg ht0
      have hfaca : 0 ≤ 1 - x a := by linarith
      calc 1 - (x a + ∑ i ∈ t, x i)
          = (1 - ∑ i ∈ t, x i) - x a := by ring
        _ ≤ (1 - ∑ i ∈ t, x i) * (1 - x a) := by
              nlinarith [mul_nonneg ha0 hsum0]
        _ ≤ (∏ i ∈ t, (1 - x i)) * (1 - x a) :=
              mul_le_mul_of_nonneg_right ih' hfaca
        _ = (1 - x a) * ∏ i ∈ t, (1 - x i) := by ring

/-- Source Lemma 3, C-1 (p.5): `9^j s_j / n ≤ 9/4` implies
`1 − 4 s_j 9^j / (27 n) ≥ 2/3`, i.e. every factor on the RHS of (3.3) is at
least `2/3` (hence positive). -/
theorem lemma3_C1 (n s j : ℕ) (hn : 0 < n)
    (h : (9 : ℝ) ^ j * (s : ℝ) / (n : ℝ) ≤ 9 / 4) :
    1 - 4 * (s : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j ≥ 2 / 3 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : 4 * (s : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j
      = (4 / 27) * ((9 : ℝ) ^ j * (s : ℝ) / (n : ℝ)) := by
    field_simp [ne_of_gt hn'] <;> ring
  rw [heq]
  nlinarith

/-- Source Lemma 3, C-2 (p.5; Appendix A p.14), under the source's inequality
(A.2): if `∑_{j=1}^{ℓ−1} 9^j s_j ≤ 9n/4` (and each factor is on the RHS of
(3.3)), then `∏_{j=1}^{ℓ−1} (1 − 4 s_j 9^j / (27 n)) ≥ 2/3`. -/
theorem lemma3_C2 (n ell : ℕ) (s : ℕ → ℕ) (hn : 0 < n)
    (hC1 : ∀ j ∈ Finset.Icc 1 (ell - 1),
      (9 : ℝ) ^ j * (s j : ℝ) / (n : ℝ) ≤ 9 / 4)
    (hA2 : ∑ j ∈ Finset.Icc 1 (ell - 1), (s j : ℝ) * (9 : ℝ) ^ j
      ≤ 9 * (n : ℝ) / 4) :
    (2 : ℝ) / 3 ≤
      ∏ j ∈ Finset.Icc 1 (ell - 1),
        (1 - 4 * (s j : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set t : Finset ℕ := Finset.Icc 1 (ell - 1) with ht
  set x : ℕ → ℝ := fun j => 4 * (s j : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j with hx
  have hx0 : ∀ j ∈ t, 0 ≤ x j := by
    intro j hj
    have h9 : (0 : ℝ) ≤ (9 : ℝ) ^ j := by positivity
    have hs : (0 : ℝ) ≤ (s j : ℝ) := by positivity
    have hn0 : (0 : ℝ) ≤ 27 * (n : ℝ) := by positivity
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs) hn0
    exact mul_nonneg this h9
  have hx1 : ∀ j ∈ t, x j ≤ 1 := by
    intro j hj
    have hj' : j ∈ Finset.Icc 1 (ell - 1) := hj
    have hb := hC1 j hj'
    have heq : x j = (4 / 27) * ((9 : ℝ) ^ j * (s j : ℝ) / (n : ℝ)) := by
      simp only [hx]
      field_simp [ne_of_gt hn'] <;> ring
    rw [heq]
    nlinarith
  have hbern := prod_one_sub_ge_one_sub_sum t x hx0 hx1
  have hsum_eq : ∑ j ∈ t, x j
      = (4 / (27 * (n : ℝ))) * ∑ j ∈ t, (s j : ℝ) * (9 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hx]
    field_simp [ne_of_gt hn'] <;> ring
  have hsum_le : (4 / (27 * (n : ℝ)))
      * ∑ j ∈ t, (s j : ℝ) * (9 : ℝ) ^ j ≤ (4 / (27 * (n : ℝ))) * (9 * (n : ℝ) / 4) := by
    apply mul_le_mul_of_nonneg_left hA2
    positivity
  have hconst : (4 / (27 * (n : ℝ))) * (9 * (n : ℝ) / 4) = 1 / 3 := by
    field_simp [ne_of_gt hn'] <;> ring
  calc (2 : ℝ) / 3 = 1 - 1 / 3 := by norm_num
    _ = 1 - (4 / (27 * (n : ℝ))) * (9 * (n : ℝ) / 4) := by rw [hconst]
    _ ≤ 1 - ∑ j ∈ t, x j := by
          rw [hsum_eq]
          linarith [hsum_le, hconst]
    _ ≤ ∏ j ∈ t, (1 - x j) := hbern

/-- Source Lemma 3, C-3 (p.5; Appendix A p.15): `9^ℓ s_ℓ ≥ 9^ℓ s_d ≥ n`,
given `s_d = m`, `s_d ≤ s_ℓ` and the choice of `ℓ`, `n ≤ 9^ℓ m`. -/
theorem lemma3_C3 (n ell sd sl m : ℕ)
    (hsd : sd = m) (hsl : sd ≤ sl) (hchoice : n ≤ 9 ^ ell * m) :
    (9 : ℝ) ^ ell * (sl : ℝ) ≥ (9 : ℝ) ^ ell * (sd : ℝ) ∧
      (9 : ℝ) ^ ell * (sl : ℝ) ≥ (n : ℝ) := by
  have h1 : sd ≤ sl := hsl
  have hmul : 9 ^ ell * sd ≤ 9 ^ ell * sl := Nat.mul_le_mul_left _ h1
  have hn1 : n ≤ 9 ^ ell * sd := by
    rw [hsd]
    exact hchoice
  constructor
  · exact_mod_cast hmul
  · have : n ≤ 9 ^ ell * sl := le_trans hn1 hmul
    exact_mod_cast this

/-- Source Lemma 3 as one conjunction: the three parts C-1, C-2, C-3 used in
the proof of Lemma 1 (Eq. (3.4), p.6). -/
theorem lemma3_statement (n ell : ℕ) (s : ℕ → ℕ) (sd sl m : ℕ) (hn : 0 < n)
    (hsd : sd = m) (hsl : sd ≤ sl) (hchoice : n ≤ 9 ^ ell * m)
    (hC1 : ∀ j ∈ Finset.Icc 1 (ell - 1),
      (9 : ℝ) ^ j * (s j : ℝ) / (n : ℝ) ≤ 9 / 4)
    (hA2 : ∑ j ∈ Finset.Icc 1 (ell - 1), (s j : ℝ) * (9 : ℝ) ^ j
      ≤ 9 * (n : ℝ) / 4) :
    (∀ j ∈ Finset.Icc 1 (ell - 1),
      1 - 4 * (s j : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j ≥ 2 / 3) ∧
    (2 : ℝ) / 3 ≤
      ∏ j ∈ Finset.Icc 1 (ell - 1),
        (1 - 4 * (s j : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j) ∧
    ((9 : ℝ) ^ ell * (sl : ℝ) ≥ (9 : ℝ) ^ ell * (sd : ℝ) ∧
      (9 : ℝ) ^ ell * (sl : ℝ) ≥ (n : ℝ)) :=
  ⟨fun j hj => lemma3_C1 n (s j) j hn (hC1 j hj),
   lemma3_C2 n ell s hn hC1 hA2,
   lemma3_C3 n ell sd sl m hsd hsl hchoice⟩

end Qatlib.Papers.VarTimeSearch23.MainResults
