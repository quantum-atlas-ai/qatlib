/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Existence of Phase-Cancellation Coefficients

This module encodes the linear and quadratic equations from [IvanyosSanselmeSantha2007a] as the
polynomial family `systemPoly`. Degree bounds allow the Chevalley-Warning theorem to establish a
nonzero common solution when the number of variables exceeds `3 * d`.

The result `exists_solution_paper_n` specializes this existence statement to the paper's number
of variables, `(d + 1) ^ 2 * (d + 2) / 2`, for positive `d`.

## Main statements

* `totalDegree_system_le` bounds the sum of the polynomial degrees by `3 * d`.
* `exists_nontrivial_solution` supplies a nonzero solution to both equation families when `3 * d
  < n`.
* `three_d_lt_paper_n` and `exists_solution_paper_n` verify the paper's variable count and
  obtain a solution at that count.

## References

* [Ivanyos et al., 2007][IvanyosSanselmeSantha2007a]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NilpotentHSP07.MainResults

open MvPolynomial

variable {p d n : ℕ} [Fact p.Prime]

/-- The diagonal quadratic polynomial whose coefficient of `(X i) ^ 2` is `u i k`. -/
def quadPoly (u : Fin n → Fin d → ZMod p) (k : Fin d) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ i, C (u i k) * (X i) ^ 2

/-- The linear polynomial whose coefficient of `X i` is `u i k`. -/
def linPoly (u : Fin n → Fin d → ZMod p) (k : Fin d) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ i, C (u i k) * X i

/-- The polynomial family combining the quadratic equations in the left summand with the linear
equations in the right summand. -/
def systemPoly (u : Fin n → Fin d → ZMod p) : Fin d ⊕ Fin d → MvPolynomial (Fin n) (ZMod p)
  | Sum.inl k => quadPoly u k
  | Sum.inr k => linPoly u k

/-- Each polynomial `quadPoly u k` has total degree at most two. -/
theorem totalDegree_quadPoly_le (u : Fin n → Fin d → ZMod p) (k : Fin d) :
    (quadPoly u k).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    (C (u i k) * (X i) ^ 2 : MvPolynomial (Fin n) (ZMod p)).totalDegree
        ≤ (C (u i k)).totalDegree + ((X i) ^ 2).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = 2 := by simp

/-- Each polynomial `linPoly u k` has total degree at most one. -/
theorem totalDegree_linPoly_le (u : Fin n → Fin d → ZMod p) (k : Fin d) :
    (linPoly u k).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    (C (u i k) * X i : MvPolynomial (Fin n) (ZMod p)).totalDegree
        ≤ (C (u i k)).totalDegree + (X i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp

/-- The sum of the total degrees of all polynomials in `systemPoly u` is at most `3 * d`. This
provides the degree bound for a Chevalley-Warning existence argument for the system
considered in [IvanyosSanselmeSantha2007a]. -/
theorem totalDegree_system_le (u : Fin n → Fin d → ZMod p) :
    (∑ i : Fin d ⊕ Fin d, (systemPoly u i).totalDegree) ≤ 3 * d := by
  rw [Fintype.sum_sum_type]
  simp only [systemPoly]
  have h1 : (∑ k : Fin d, (quadPoly u k).totalDegree) ≤ ∑ _k : Fin d, 2 :=
    Finset.sum_le_sum (fun k _ => totalDegree_quadPoly_le u k)
  have h2 : (∑ k : Fin d, (linPoly u k).totalDegree) ≤ ∑ _k : Fin d, 1 :=
    Finset.sum_le_sum (fun k _ => totalDegree_linPoly_le u k)
  calc
    (∑ k : Fin d, (quadPoly u k).totalDegree) + (∑ k : Fin d, (linPoly u k).totalDegree)
        ≤ (∑ _k : Fin d, 2) + (∑ _k : Fin d, 1) := add_le_add h1 h2
    _ = 3 * d := by simp [Finset.sum_const]; ring

/-- If `3 * d < n`, there is a nonzero vector whose weighted coordinatewise quadratic and linear
sums both vanish. This is an existence result for the equation system considered in
[IvanyosSanselmeSantha2007a]. -/
theorem exists_nontrivial_solution (u : Fin n → Fin d → ZMod p) (hn : 3 * d < n) :
    ∃ j : Fin n → ZMod p, j ≠ 0 ∧
      (∀ k : Fin d, ∑ i, u i k * (j i * j i) = 0) ∧
      (∀ k : Fin d, ∑ i, u i k * j i = 0) := by
  classical
  let f : Fin d ⊕ Fin d → MvPolynomial (Fin n) (ZMod p) := systemPoly u
  have hdeg : (∑ i : Fin d ⊕ Fin d, (f i).totalDegree) < Fintype.card (Fin n) := by
    have hle := totalDegree_system_le (p := p) u
    simp only [f]
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt hle hn
  let P : (Fin n → ZMod p) → Prop :=
    fun x => ∀ i ∈ (Finset.univ : Finset (Fin d ⊕ Fin d)), MvPolynomial.eval x (f i) = 0
  have hdvd : p ∣ Nat.card { x // P x } := by
    have h := char_dvd_card_solutions_of_sum_lt (K := ZMod p) (σ := Fin n)
      (ι := Fin d ⊕ Fin d) p (s := Finset.univ) (f := f) hdeg
    simpa only [← Nat.card_eq_fintype_card] using h
  have hzero : P 0 := by
    intro i _
    rcases i with k | k
    · simp [f, systemPoly, quadPoly]
    · simp [f, systemPoly, linPoly]
  have hpos : 0 < Nat.card { x // P x } := by
    haveI : Nonempty { x // P x } := ⟨⟨(0 : Fin n → ZMod p), hzero⟩⟩
    haveI : Finite { x // P x } := Finite.of_injective Subtype.val Subtype.val_injective
    exact Nat.card_pos
  have hne1 : Nat.card { x // P x } ≠ 1 := by
    intro h1
    have hp1 : p ∣ 1 := h1 ▸ hdvd
    exact (Fact.out : p.Prime).not_dvd_one hp1
  have hgt_nat : 1 < Nat.card { x // P x } := by omega
  have hgt : 1 < Fintype.card { x // P x } := by
    rw [← Nat.card_eq_fintype_card]
    exact hgt_nat
  obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hgt
  have key : ∀ z : Fin n → ZMod p,
      (∀ i ∈ (Finset.univ : Finset (Fin d ⊕ Fin d)), MvPolynomial.eval z (f i) = 0) →
      (∀ k : Fin d, ∑ i, u i k * (z i * z i) = 0) ∧
      (∀ k : Fin d, ∑ i, u i k * z i = 0) := by
    intro z hz
    constructor
    · intro k
      have h := hz (Sum.inl k) (Finset.mem_univ _)
      simpa [f, systemPoly, quadPoly, pow_two] using h
    · intro k
      have h := hz (Sum.inr k) (Finset.mem_univ _)
      simpa [f, systemPoly, linPoly] using h
  have hdistinct : x.1 ≠ 0 ∨ y.1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hxy (Subtype.ext (by rw [h.1, h.2]))
  rcases hdistinct with hx0 | hy0
  · obtain ⟨hq, hl⟩ := key x.1 x.2
    exact ⟨x.1, hx0, hq, hl⟩
  · obtain ⟨hq, hl⟩ := key y.1 y.2
    exact ⟨y.1, hy0, hq, hl⟩

/-- For positive `d`, the number `(d + 1) ^ 2 * (d + 2) / 2` is strictly greater than `3 * d`.
This verifies the variable count in [Ivanyos et al., Theorem 5][IvanyosSanselmeSantha2007a]. -/
theorem three_d_lt_paper_n (d : ℕ) (hd : 1 ≤ d) :
    3 * d < (d + 1) ^ 2 * (d + 2) / 2 := by
  have h6 : 6 * d < (d + 1) ^ 2 * (d + 2) := by nlinarith
  have hev : Even ((d + 1) ^ 2 * (d + 2)) := by
    have h : Even ((d + 1) * (d + 2)) := Nat.even_mul_succ_self (d + 1)
    have h2 : (d + 1) ^ 2 * (d + 2) = (d + 1) * ((d + 1) * (d + 2)) := by ring
    rw [h2]
    exact h.mul_left (d + 1)
  obtain ⟨m, hm⟩ := hev
  omega

/-- For positive `d`, the linear and quadratic system has a nonzero solution with `(d + 1) ^ 2 *
(d + 2) / 2` variables. This gives the existence conclusion at the variable count of
[Ivanyos et al., Theorem 5][IvanyosSanselmeSantha2007a]. -/
theorem exists_solution_paper_n (d : ℕ) (hd : 1 ≤ d)
    (u : Fin ((d + 1) ^ 2 * (d + 2) / 2) → Fin d → ZMod p) :
    ∃ j : Fin ((d + 1) ^ 2 * (d + 2) / 2) → ZMod p, j ≠ 0 ∧
      (∀ k : Fin d, ∑ i, u i k * (j i * j i) = 0) ∧
      (∀ k : Fin d, ∑ i, u i k * j i = 0) :=
  exists_nontrivial_solution u (three_d_lt_paper_n d hd)

end Qatlib.Papers.NilpotentHSP07.MainResults
