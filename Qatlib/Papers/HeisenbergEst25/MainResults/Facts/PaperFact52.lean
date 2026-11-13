/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeisenbergEst25.MainResults.Model.ProtocolModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Weyl Dimension Ratios for Gamma-Shaped Young Diagrams

This module proves Fact 5.2, evaluating the Clebsch-Gordan square-root Weyl dimension
ratios `α_i √(dim Q^d_{γ_i} / dim Q^d_{γ_i^+})` and
`β_{i-1} √(dim Q^d_{γ_{i-1}} / dim Q^d_{γ_i^+})` for the Γ-shaped Young diagrams of
the Heisenberg-scaling state estimation protocol and identifying them with `xCoeff`
and `yCoeff`.

## Main statements

* `fact52_alpha_dim_ratio`: `α_i √(gammaDimRatio d L N i) = xCoeff d L N i` for `i ≤ L`.
* `fact52_beta_dim_ratio`: `β_{i-1} √(gammaDimRatioPrev d L N i) = yCoeff d L N i` for `1 ≤ i ≤ L`.

## References

* [Chen, 2025][Chen2025HeisenbergEst], Fact 5.2, Section 5, p. 11.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HeisenbergEst25.MainResults.Facts

open Qatlib.Papers.HeisenbergEst25.MainResults.Model

open scoped BigOperators

private def weylPairs (d : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 d).product (Finset.Icc 1 d)).filter (fun p => p.1 < p.2)

private def rowGap (shape : ℕ → ℤ) (p : ℕ × ℕ) : ℝ :=
  (shape p.1 : ℝ) - (p.1 : ℝ) - (shape p.2 : ℝ) + (p.2 : ℝ)

private lemma weyl_ratio (d : ℕ) (s t : ℕ → ℤ) :
    weylDim d s / weylDim d t =
      ∏ p ∈ weylPairs d, rowGap s p / rowGap t p := by
  unfold weylDim
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hab : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hden : (p.2 : ℝ) - (p.1 : ℝ) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hab))
  simpa only [rowGap, Int.cast_add, Int.cast_sub, Int.cast_natCast] using
    div_div_div_cancel_right₀ hden
      (((s p.1 - (p.1 : ℤ) - s p.2 + (p.2 : ℤ) : ℤ) : ℝ))
      (((t p.1 - (p.1 : ℤ) - t p.2 + (p.2 : ℤ) : ℤ) : ℝ))

private lemma plus_gap_pos (d L N i a b : ℕ) (hN : L ≤ N) (hi : i ≤ L)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ d) :
    0 < rowGap (gammaPlusRow d L N i) (a, b) := by
  have hb1 : b ≠ 1 := by omega
  have had : a ≠ d := by omega
  have hd1 : d ≠ 1 := by omega
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hiR : (i : ℝ) ≤ (L : ℝ) := by exact_mod_cast hi
  have hNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hshape : (gammaPlusRow d L N i b : ℝ) ≤ (gammaPlusRow d L N i a : ℝ) := by
    by_cases ha1 : a = 1 <;> by_cases hbd : b = d <;>
      simp [gammaPlusRow, ha1, hb1, had, hbd, hd1] <;> linarith
  dsimp [rowGap]
  linarith

private lemma prod_first_row (d : ℕ) (f : ℕ × ℕ → ℝ)
    (h : ∀ a b, 1 ≤ a → a < b → b ≤ d → a ≠ 1 → f (a, b) = 1) :
    (∏ p ∈ weylPairs d, f p) = ∏ b ∈ Finset.Icc 2 d, f (1, b) := by
  symm
  apply Finset.prod_bij_ne_one (fun b _ _ => (1, b))
  · intro b hb _
    simp only [Finset.mem_Icc] at hb
    simp only [weylPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc]
    omega
  · intro a _ _ b _ _ hab
    exact congrArg Prod.snd hab
  · rintro ⟨a, b⟩ hp hf
    simp only [weylPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc] at hp
    have ha1 : a = 1 := by
      by_contra ha1
      exact hf (h a b hp.1.1.1 hp.2 hp.1.2.2 ha1)
    subst a
    exact ⟨b, Finset.mem_Icc.mpr ⟨by omega, hp.1.2.2⟩, hf, rfl⟩
  · intros
    rfl

private lemma prod_last_row (d : ℕ) (hd : 2 ≤ d) (f : ℕ × ℕ → ℝ)
    (h : ∀ a b, 1 ≤ a → a < b → b ≤ d → b ≠ d → f (a, b) = 1) :
    (∏ p ∈ weylPairs d, f p) = ∏ a ∈ Finset.Icc 1 (d - 1), f (a, d) := by
  symm
  apply Finset.prod_bij_ne_one (fun a _ _ => (a, d))
  · intro a ha _
    simp only [Finset.mem_Icc] at ha
    simp only [weylPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc]
    omega
  · intro a _ _ b _ _ hab
    exact congrArg Prod.fst hab
  · rintro ⟨a, b⟩ hp hf
    simp only [weylPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc] at hp
    have hbd : b = d := by
      by_contra hbd
      exact hf (h a b hp.1.1.1 hp.2 hp.1.2.2 hbd)
    subst b
    exact ⟨a, Finset.mem_Icc.mpr ⟨hp.1.1.1, by omega⟩, hf, rfl⟩
  · intros
    rfl

/-- Adjacent quotients telescope even when the interval is empty at `m = 1`. -/
private lemma telescope (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℝ)
    (hf : ∀ j ∈ Finset.Icc 1 m, f j ≠ 0) :
    (∏ j ∈ Finset.Icc 2 m, f (j - 1) / f j) = f 1 / f m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst m
      simp [hf 1 (by simp)]
    · have hm1 : 1 ≤ m := by omega
      rw [Finset.prod_Icc_succ_top (by omega)]
      rw [ih hm1 (fun j hj => hf j (by
        simp only [Finset.mem_Icc] at hj ⊢
        omega))]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      exact div_mul_div_cancel₀ (hf m (by simp only [Finset.mem_Icc]; omega))

private lemma telescope_linear (m : ℕ) (hm : 1 ≤ m) (A B : ℝ)
    (hf : ∀ j ∈ Finset.Icc 1 m, A + B * (j : ℝ) ≠ 0) :
    (∏ j ∈ Finset.Icc 2 m, (A + B * ((j : ℝ) - 1)) / (A + B * (j : ℝ))) =
      (A + B) / (A + B * (m : ℝ)) := by
  calc
    _ = ∏ j ∈ Finset.Icc 2 m,
        (A + B * ((j - 1 : ℕ) : ℝ)) / (A + B * (j : ℝ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Nat.cast_sub (by have := (Finset.mem_Icc.mp hj).1; omega), Nat.cast_one]
    _ = _ := by simpa using telescope m hm (fun j => A + B * (j : ℝ)) hf

private lemma gamma_ratio (d L N i : ℕ) (hd : 2 ≤ d) (hN : L ≤ N) (hi : i ≤ L) :
    gammaDimRatio d L N i =
      (((L : ℝ) + N + d - 2 * i - 1) * ((N : ℝ) - i + 1)) /
        (((L : ℝ) + N + d - 2 * i) * ((N : ℝ) + d - i - 1)) := by
  have hd1 : d ≠ 1 := by omega
  have hiR : (i : ℝ) ≤ (L : ℝ) := by exact_mod_cast hi
  have hNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  let f := fun p => rowGap (gammaRow d L N i) p / rowGap (gammaPlusRow d L N i) p
  have hsupport : ∀ a b, 1 ≤ a → a < b → b ≤ d → a ≠ 1 → f (a, b) = 1 := by
    intro a b ha hab hb ha1
    have hb1 : b ≠ 1 := by omega
    have heq : rowGap (gammaRow d L N i) (a, b) =
        rowGap (gammaPlusRow d L N i) (a, b) := by
      simp [rowGap, gammaRow, gammaPlusRow, ha1, hb1]
    dsimp [f]
    rw [heq]
    exact div_self (ne_of_gt (plus_gap_pos d L N i a b hN hi ha hab hb))
  have hmid : ∀ b ∈ Finset.Icc 2 (d - 1),
      f (1, b) = ((N : ℝ) - i - 1 + b) / ((N : ℝ) - i + b) := by
    intro b hb
    have hb1 : b ≠ 1 := by have := Finset.mem_Icc.mp hb; omega
    have hbd : b ≠ d := by have := Finset.mem_Icc.mp hb; omega
    dsimp [f]
    simp [rowGap, gammaRow, gammaPlusRow, hb1, hbd]
    congr 1 <;> ring
  have htop : f (1, d) = ((L : ℝ) + N + d - 2 * i - 1) /
      ((L : ℝ) + N + d - 2 * i) := by
    dsimp [f]
    simp [rowGap, gammaRow, gammaPlusRow, hd1]
    congr 1 <;> ring
  have htel : (∏ b ∈ Finset.Icc 2 (d - 1),
      ((N : ℝ) - i - 1 + b) / ((N : ℝ) - i + b)) =
      ((N : ℝ) - i + 1) / ((N : ℝ) + d - i - 1) := by
    have ht := telescope_linear (d - 1) (by omega) ((N : ℝ) - i) 1 (by
      intro j hj
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      linarith)
    simp only [one_mul, hdsub] at ht
    convert ht using 1
    · apply Finset.prod_congr rfl
      intro b _
      congr 1
      ring
    · congr 1
      ring
  change weylDim d (gammaRow d L N i) / weylDim d (gammaPlusRow d L N i) = _
  rw [weyl_ratio, prod_first_row d f hsupport]
  have hsplit := Finset.prod_Icc_succ_top (a := 2) (b := d - 1) (by omega)
    (fun b => f (1, b))
  rw [Nat.sub_add_cancel (by omega : 1 ≤ d)] at hsplit
  rw [hsplit, htop, Finset.prod_congr rfl hmid, htel]
  rw [div_mul_div_comm]
  congr 1 <;> ring

private lemma gamma_ratio_prev (d L N i : ℕ) (hd : 2 ≤ d) (hN : L ≤ N)
    (hi1 : 1 ≤ i) (hi : i ≤ L) :
    gammaDimRatioPrev d L N i =
      (((L : ℝ) + N + d - 2 * i + 1) * ((L : ℝ) + d - i - 1)) /
        (((L : ℝ) + N + d - 2 * i) * ((L : ℝ) - i + 1)) := by
  have hd1 : d ≠ 1 := by omega
  have hiR : (i : ℝ) ≤ (L : ℝ) := by exact_mod_cast hi
  have hisub : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by
    rw [Nat.cast_sub hi1, Nat.cast_one]
  have hdsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  let f := fun p => rowGap (gammaRow d L N (i - 1)) p /
    rowGap (gammaPlusRow d L N i) p
  have hsupport : ∀ a b, 1 ≤ a → a < b → b ≤ d → b ≠ d → f (a, b) = 1 := by
    intro a b ha hab hb hbd
    have hb1 : b ≠ 1 := by omega
    have had : a ≠ d := by omega
    have heq : rowGap (gammaRow d L N (i - 1)) (a, b) =
        rowGap (gammaPlusRow d L N i) (a, b) := by
      by_cases ha1 : a = 1 <;>
        simp [rowGap, gammaRow, gammaPlusRow, ha1, hb1, had, hbd, hisub]
      ring
    dsimp [f]
    rw [heq]
    exact div_self (ne_of_gt (plus_gap_pos d L N i a b hN hi ha hab hb))
  have hmid : ∀ a ∈ Finset.Icc 2 (d - 1),
      f (a, d) = ((L : ℝ) + d - i + 1 - a) / ((L : ℝ) + d - i - a) := by
    intro a ha
    have ha1 : a ≠ 1 := by have := Finset.mem_Icc.mp ha; omega
    have had : a ≠ d := by have := Finset.mem_Icc.mp ha; omega
    dsimp [f]
    simp [rowGap, gammaRow, gammaPlusRow, ha1, had, hd1, hisub]
    congr 1 <;> ring
  have htop : f (1, d) = ((L : ℝ) + N + d - 2 * i + 1) /
      ((L : ℝ) + N + d - 2 * i) := by
    dsimp [f]
    simp [rowGap, gammaRow, gammaPlusRow, hd1, hisub]
    congr 1 <;> ring
  have htel : (∏ a ∈ Finset.Icc 2 (d - 1),
      ((L : ℝ) + d - i + 1 - a) / ((L : ℝ) + d - i - a)) =
      ((L : ℝ) + d - i - 1) / ((L : ℝ) - i + 1) := by
    have ht := telescope_linear (d - 1) (by omega) ((L : ℝ) + d - i) (-1) (by
      intro j hj
      have hjR : (j : ℝ) ≤ (d - 1 : ℕ) := by
        exact_mod_cast (Finset.mem_Icc.mp hj).2
      rw [hdsub] at hjR
      linarith)
    rw [hdsub] at ht
    convert ht using 1
    · apply Finset.prod_congr rfl
      intro a _
      congr 1 <;> ring
    · congr 1
      ring
  change weylDim d (gammaRow d L N (i - 1)) / weylDim d (gammaPlusRow d L N i) = _
  rw [weyl_ratio, prod_last_row d hd f hsupport]
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ d - 1),
    Finset.prod_insert (by simp), htop]
  change _ * (∏ a ∈ Finset.Icc 2 (d - 1), f (a, d)) = _
  rw [Finset.prod_congr rfl hmid, htel, div_mul_div_comm]

/-- **Fact 5.2 (first identity)**: the `α_i`-weighted square-root Weyl dimension ratio
equals `xCoeff d L N i`. -/
theorem fact52_alpha_dim_ratio (d L N i : ℕ)
    (hd : 2 ≤ d) (_hL : 0 < L) (hN : L ≤ N) (hi : i ≤ L) :
    alphaCoeff d L N i * Real.sqrt (gammaDimRatio d L N i) = xCoeff d L N i := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hiR : (i : ℝ) ≤ L := by exact_mod_cast hi
  have hNR : (L : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) + d - i - 1 := by linarith
  have hB : 0 < (L : ℝ) + N + d - 2 * i - 1 := by linarith
  have hC : 0 < (L : ℝ) + N + d - 2 * i := by linarith
  have ha : 0 ≤ alphaCoeff d L N i :=
    div_nonneg (le_of_lt hA) (le_of_lt hB)
  calc
    _ = Real.sqrt (alphaCoeff d L N i ^ 2) * Real.sqrt (gammaDimRatio d L N i) := by
      rw [Real.sqrt_sq ha]
    _ = Real.sqrt (alphaCoeff d L N i ^ 2 * gammaDimRatio d L N i) :=
      (Real.sqrt_mul (sq_nonneg _) _).symm
    _ = xCoeff d L N i := by
      unfold xCoeff
      congr 1
      rw [gamma_ratio d L N i hd hN hi]
      unfold alphaCoeff
      field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]

/-- **Fact 5.2 (second identity)**: the `β_{i - 1}`-weighted square-root Weyl dimension
ratio equals `yCoeff d L N i`. -/
theorem fact52_beta_dim_ratio (d L N i : ℕ)
    (hd : 2 ≤ d) (_hL : 0 < L) (hN : L ≤ N) (hi1 : 1 ≤ i) (hiL : i ≤ L) :
    betaCoeff d L N (i - 1) * Real.sqrt (gammaDimRatioPrev d L N i) = yCoeff d L N i := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hiR : (i : ℝ) ≤ L := by exact_mod_cast hiL
  have hNR : (L : ℝ) ≤ N := by exact_mod_cast hN
  have hisub : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub hi1, Nat.cast_one]
  have hA : 0 < (L : ℝ) - i + 1 := by linarith
  have hB : 0 < (L : ℝ) + N + d - 2 * i + 1 := by linarith
  have hC : 0 < (L : ℝ) + N + d - 2 * i := by linarith
  have hbeta : betaCoeff d L N (i - 1) =
      ((L : ℝ) - i + 1) / ((L : ℝ) + N + d - 2 * i + 1) := by
    unfold betaCoeff
    rw [hisub]
    congr 1 <;> ring
  have hb : 0 ≤ betaCoeff d L N (i - 1) := by
    rw [hbeta]
    exact div_nonneg (le_of_lt hA) (le_of_lt hB)
  calc
    _ = Real.sqrt (betaCoeff d L N (i - 1) ^ 2) *
        Real.sqrt (gammaDimRatioPrev d L N i) := by rw [Real.sqrt_sq hb]
    _ = Real.sqrt (betaCoeff d L N (i - 1) ^ 2 * gammaDimRatioPrev d L N i) :=
      (Real.sqrt_mul (sq_nonneg _) _).symm
    _ = yCoeff d L N i := by
      unfold yCoeff
      congr 1
      rw [gamma_ratio_prev d L N i hd hN hi1 hiL, hbeta]
      field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]

end Qatlib.Papers.HeisenbergEst25.MainResults.Facts
