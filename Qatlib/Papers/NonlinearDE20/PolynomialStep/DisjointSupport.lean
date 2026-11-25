/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NonlinearDE20.PolynomialStep.InteractionIncidence
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

@[expose] public section

/-!
# Disjoint support fraction

For `n` copies and interaction supports of size `m` with `2 * m ≤ n`, this module counts the
`m`-subsets disjoint from a fixed support and bounds their fraction by `(1 - m / n)^m`, the upper
bound used in the overlap analysis of [LloydEtAl2020]. The sharper printed approximation
`1 - m^2 / n` is not claimed: it fails for small parameters.

## Main statements

* `disjoint_support_fraction`: the fraction of `m`-subsets disjoint from a fixed `m`-subset equals
  `C(n - m, m) / C(n, m)` and is at most `(1 - m / n)^m`.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Disjoint

/-- Products of pointwise smaller nonnegative factors are smaller. -/
private lemma prod_le_prod_of_nonneg {α : Type*} {s : Finset α} {f g : α → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hga : 0 ≤ g a := le_trans hfa (h a (Finset.mem_insert_self a s))
    have hP : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hB : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
    calc f a * ∏ i ∈ s, f i ≤ g a * ∏ i ∈ s, f i :=
          mul_le_mul_of_nonneg_right (h a (Finset.mem_insert_self a s)) hP
      _ ≤ g a * ∏ i ∈ s, g i := mul_le_mul_of_nonneg_left hB hga

/-- For `2 * m ≤ n`, the fraction of size-`m` subsets disjoint from a fixed size-`m` subset is
`C(n - m, m) / C(n, m)`, and it is at most `(1 - m / n)^m` [LloydEtAl2020]. -/
theorem disjoint_support_fraction (n m : ℕ) (s : Finset (Fin n))
    (hmn : 2 * m ≤ n) (hs : s.card = m) :
    ((Finset.univ.filter (fun t : Finset (Fin n) => t.card = m ∧ Disjoint t s)).card : ℝ) /
        (Nat.choose n m : ℝ) = (Nat.choose (n - m) m : ℝ) / (Nat.choose n m : ℝ) ∧
      (Nat.choose (n - m) m : ℝ) / (Nat.choose n m : ℝ) ≤ (1 - (m : ℝ) / n) ^ m := by
  have hmle : m ≤ n := le_trans (by omega : m ≤ 2 * m) hmn
  have hset : (Finset.univ.filter (fun t : Finset (Fin n) => t.card = m ∧ Disjoint t s))
      = (Finset.univ \ s).powersetCard m := by
    ext t
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨-, hc, hd⟩
      refine ⟨fun x hx => ?_, hc⟩
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, fun hxs => Finset.disjoint_left.mp hd hx hxs⟩
    · rintro ⟨hsub, hc⟩
      refine ⟨Finset.mem_univ t, hc, Finset.disjoint_left.mpr fun x hx hxs => ?_⟩
      have hx' : x ∈ Finset.univ \ s := hsub hx
      rw [Finset.mem_sdiff] at hx'
      exact hx'.2 hxs
  have hcard : (Finset.univ \ s).card = n - m := by
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hs]
  have hP1 : (∏ i ∈ Finset.range m, (((n - i : ℕ) : ℝ)))
      = (Nat.factorial m : ℝ) * (Nat.choose n m : ℝ) := by
    have h : (∏ i ∈ Finset.range m, (n - i)) = Nat.factorial m * Nat.choose n m := by
      rw [← Nat.descFactorial_eq_prod_range n m, Nat.descFactorial_eq_factorial_mul_choose]
    have := congrArg (Nat.cast : ℕ → ℝ) h
    simpa using this
  have hP2 : (∏ i ∈ Finset.range m, (((n - m - i : ℕ) : ℝ)))
      = (Nat.factorial m : ℝ) * (Nat.choose (n - m) m : ℝ) := by
    have h : (∏ i ∈ Finset.range m, (n - m - i)) =
        Nat.factorial m * Nat.choose (n - m) m := by
      rw [← Nat.descFactorial_eq_prod_range (n - m) m, Nat.descFactorial_eq_factorial_mul_choose]
    have := congrArg (Nat.cast : ℕ → ℝ) h
    simpa using this
  have hmf : (Nat.factorial m : ℝ) ≠ 0 := by
    have := Nat.factorial_pos m
    exact_mod_cast this.ne'
  have hC1 : (Nat.choose n m : ℝ) ≠ 0 := by
    have := Nat.choose_pos hmle
    exact_mod_cast this.ne'
  have hratio : (Nat.choose (n - m) m : ℝ) / (Nat.choose n m : ℝ)
      = (∏ i ∈ Finset.range m, (((n - m - i : ℕ) : ℝ))) /
        (∏ i ∈ Finset.range m, (((n - i : ℕ) : ℝ))) := by
    rw [hP1, hP2]
    field_simp
  have hprod : (∏ i ∈ Finset.range m, (((n - m - i : ℕ) : ℝ))) /
        (∏ i ∈ Finset.range m, (((n - i : ℕ) : ℝ)))
      = ∏ i ∈ Finset.range m, ((((n - m - i : ℕ) : ℝ)) / (((n - i : ℕ) : ℝ))) := by
    rw [Finset.prod_div_distrib]
  have hterm : ∀ i ∈ Finset.range m,
      ((((n - m - i : ℕ) : ℝ)) / (((n - i : ℕ) : ℝ))) ≤ 1 - (m : ℝ) / n := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hin : i < n := lt_of_lt_of_le hi' hmle
    have hn : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hni : (0 : ℝ) < ((n - i : ℕ) : ℝ) := by
      have : 0 < n - i := by omega
      exact_mod_cast this
    have hsub : (1 : ℝ) - (m : ℝ) / n = ((n - m : ℕ) : ℝ) / (n : ℝ) := by
      rw [Nat.cast_sub hmle]
      field_simp
    rw [hsub, div_le_div_iff₀ hni hn]
    have e1 : (((n - m - i : ℕ) : ℝ)) = (n : ℝ) - (m : ℝ) - (i : ℝ) := by
      rw [show n - m - i = n - (m + i) from by omega, Nat.cast_sub (by omega : m + i ≤ n)]
      push_cast
      ring
    have e2 : (((n - i : ℕ) : ℝ)) = (n : ℝ) - (i : ℝ) :=
      Nat.cast_sub (le_of_lt hin)
    have hnm : (((n - m : ℕ) : ℝ)) = (n : ℝ) - (m : ℝ) := Nat.cast_sub hmle
    rw [e1, e2, hnm]
    have hiR : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hm2 : (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    nlinarith [mul_nonneg hiR hmR]
  have hnonneg : ∀ i ∈ Finset.range m,
      (0 : ℝ) ≤ (((n - m - i : ℕ) : ℝ)) / (((n - i : ℕ) : ℝ)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hin : i < n := lt_of_lt_of_le hi' hmle
    have hni : (0 : ℝ) < ((n - i : ℕ) : ℝ) := by
      have : 0 < n - i := by omega
      exact_mod_cast this
    exact div_nonneg (Nat.cast_nonneg _) hni.le
  have hle : (∏ i ∈ Finset.range m, ((((n - m - i : ℕ) : ℝ)) / (((n - i : ℕ) : ℝ))))
      ≤ (1 - (m : ℝ) / n) ^ m := by
    calc ∏ i ∈ Finset.range m, ((((n - m - i : ℕ) : ℝ)) / (((n - i : ℕ) : ℝ)))
        ≤ ∏ _i ∈ Finset.range m, (1 - (m : ℝ) / n) := prod_le_prod_of_nonneg hnonneg hterm
      _ = (1 - (m : ℝ) / n) ^ m := by
          rw [Finset.prod_const, Finset.card_range]
  refine ⟨?_, ?_⟩
  · rw [hset, Finset.card_powersetCard, hcard]
  · calc (Nat.choose (n - m) m : ℝ) / (Nat.choose n m : ℝ)
        = (∏ i ∈ Finset.range m, (((n - m - i : ℕ) : ℝ))) /
          (∏ i ∈ Finset.range m, (((n - i : ℕ) : ℝ))) := hratio
      _ = ∏ i ∈ Finset.range m, ((((n - m - i : ℕ) : ℝ)) / (((n - i : ℕ) : ℝ))) := hprod
      _ ≤ (1 - (m : ℝ) / n) ^ m := hle

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Disjoint
