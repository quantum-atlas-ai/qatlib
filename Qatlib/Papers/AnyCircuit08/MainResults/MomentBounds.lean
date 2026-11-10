/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AnyCircuit08.MainResults.Basic

namespace Qatlib.Papers.AnyCircuit08.MainResults

set_option autoImplicit false

open scoped BigOperators

theorem weighted_l1_ge_of_fourth_moment {X : Type} [Fintype X] (p Y : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hY : ∀ x, 0 ≤ Y x) :
    (∑ x, p x * Y x ^ 2) ^ 3
      ≤ (∑ x, p x * Y x) ^ 2 * (∑ x, p x * Y x ^ 4) := by
  set A : ℝ := ∑ x, p x * Y x ^ 2 with hAdef
  set B : ℝ := ∑ x, p x * Y x with hBdef
  set C : ℝ := ∑ x, p x * Y x ^ 3 with hCdef
  set D : ℝ := ∑ x, p x * Y x ^ 4 with hDdef
  have hAnn : 0 ≤ A := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (pow_nonneg (hY x) 2))
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hY x))
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (pow_nonneg (hY x) 3))
  have hDnn : 0 ≤ D := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (pow_nonneg (hY x) 4))

  have h1 : A ^ 2 ≤ B * C := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun x => Real.sqrt (p x) * Real.sqrt (Y x))
      (g := fun x => Real.sqrt (p x) * (Y x * Real.sqrt (Y x)))
    have hfg : ∀ x, Real.sqrt (p x) * Real.sqrt (Y x) *
        (Real.sqrt (p x) * (Y x * Real.sqrt (Y x))) = p x * Y x ^ 2 := by
      intro x
      have hp' : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp x)
      have hY' : Real.sqrt (Y x) * Real.sqrt (Y x) = Y x := Real.mul_self_sqrt (hY x)
      calc Real.sqrt (p x) * Real.sqrt (Y x) *
            (Real.sqrt (p x) * (Y x * Real.sqrt (Y x)))
          = (Real.sqrt (p x) * Real.sqrt (p x)) * Y x *
              (Real.sqrt (Y x) * Real.sqrt (Y x)) := by ring
        _ = p x * Y x * Y x := by rw [hp', hY']
        _ = p x * Y x ^ 2 := by ring
    have hf2 : ∀ x, (Real.sqrt (p x) * Real.sqrt (Y x)) ^ 2 = p x * Y x := by
      intro x
      have hp' : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp x)
      have hY' : Real.sqrt (Y x) * Real.sqrt (Y x) = Y x := Real.mul_self_sqrt (hY x)
      calc (Real.sqrt (p x) * Real.sqrt (Y x)) ^ 2
          = (Real.sqrt (p x) * Real.sqrt (p x)) *
              (Real.sqrt (Y x) * Real.sqrt (Y x)) := by ring
        _ = p x * Y x := by rw [hp', hY']
    have hg2 : ∀ x, (Real.sqrt (p x) * (Y x * Real.sqrt (Y x))) ^ 2
        = p x * Y x ^ 3 := by
      intro x
      have hp' : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp x)
      have hY' : Real.sqrt (Y x) * Real.sqrt (Y x) = Y x := Real.mul_self_sqrt (hY x)
      calc (Real.sqrt (p x) * (Y x * Real.sqrt (Y x))) ^ 2
          = (Real.sqrt (p x) * Real.sqrt (p x)) * Y x ^ 2 *
              (Real.sqrt (Y x) * Real.sqrt (Y x)) := by ring
        _ = p x * Y x ^ 2 * Y x := by rw [hp', hY']
        _ = p x * Y x ^ 3 := by ring
    rw [Finset.sum_congr rfl (fun x _ => hfg x),
      Finset.sum_congr rfl (fun x _ => hf2 x),
      Finset.sum_congr rfl (fun x _ => hg2 x)] at hcs
    simpa only [← hAdef, ← hBdef, ← hCdef] using hcs

  have h2 : C ^ 2 ≤ A * D := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun x => Real.sqrt (p x) * Y x)
      (g := fun x => Real.sqrt (p x) * Y x ^ 2)
    have hfg : ∀ x, Real.sqrt (p x) * Y x * (Real.sqrt (p x) * Y x ^ 2)
        = p x * Y x ^ 3 := by
      intro x
      have hp' : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp x)
      calc Real.sqrt (p x) * Y x * (Real.sqrt (p x) * Y x ^ 2)
          = (Real.sqrt (p x) * Real.sqrt (p x)) * Y x * Y x ^ 2 := by ring
        _ = p x * Y x * Y x ^ 2 := by rw [hp']
        _ = p x * Y x ^ 3 := by ring
    have hf2 : ∀ x, (Real.sqrt (p x) * Y x) ^ 2 = p x * Y x ^ 2 := by
      intro x
      have hp' : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp x)
      calc (Real.sqrt (p x) * Y x) ^ 2
          = (Real.sqrt (p x) * Real.sqrt (p x)) * Y x ^ 2 := by ring
        _ = p x * Y x ^ 2 := by rw [hp']
    have hg2 : ∀ x, (Real.sqrt (p x) * Y x ^ 2) ^ 2 = p x * Y x ^ 4 := by
      intro x
      have hp' : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp x)
      calc (Real.sqrt (p x) * Y x ^ 2) ^ 2
          = (Real.sqrt (p x) * Real.sqrt (p x)) * Y x ^ 4 := by ring
        _ = p x * Y x ^ 4 := by rw [hp']
    rw [Finset.sum_congr rfl (fun x _ => hfg x),
      Finset.sum_congr rfl (fun x _ => hf2 x),
      Finset.sum_congr rfl (fun x _ => hg2 x)] at hcs
    simpa only [← hAdef, ← hCdef, ← hDdef] using hcs

  have h4 : A ^ 4 ≤ B ^ 2 * (A * D) := by
    calc A ^ 4 = (A ^ 2) ^ 2 := by ring
      _ ≤ (B * C) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = B ^ 2 * C ^ 2 := by ring
      _ ≤ B ^ 2 * (A * D) := mul_le_mul_of_nonneg_left h2 (by positivity)
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · have hzero : ∀ x, p x * Y x ^ 2 = 0 := by
      intro x
      have hle : p x * Y x ^ 2 ≤ A := by
        rw [hAdef]
        exact Finset.single_le_sum
          (fun i _ => mul_nonneg (hp i) (pow_nonneg (hY i) 2)) (Finset.mem_univ x)
      rw [← hA0] at hle
      exact le_antisymm hle (mul_nonneg (hp x) (pow_nonneg (hY x) 2))
    have hB0 : B = 0 := by
      rw [hBdef]
      apply Finset.sum_eq_zero
      intro x _
      rcases mul_eq_zero.mp (hzero x) with hpz | hYz
      · rw [hpz]; ring
      · have hy : Y x = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hYz
        rw [hy]; ring
    have hD0 : D = 0 := by
      rw [hDdef]
      apply Finset.sum_eq_zero
      intro x _
      rcases mul_eq_zero.mp (hzero x) with hpz | hYz
      · rw [hpz]; ring
      · have hy : Y x = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hYz
        rw [hy]; ring
    have hfin : A ^ 3 ≤ B ^ 2 * D := by rw [← hA0, hB0, hD0]; simp
    simpa only [← hAdef, ← hBdef, ← hDdef] using hfin
  · have hkey : A * A ^ 3 ≤ A * (B ^ 2 * D) := by
      calc A * A ^ 3 = A ^ 4 := by ring
        _ ≤ B ^ 2 * (A * D) := h4
        _ = A * (B ^ 2 * D) := by ring
    have hfin : A ^ 3 ≤ B ^ 2 * D := le_of_mul_le_mul_left hkey hApos
    simpa only [← hAdef, ← hBdef, ← hDdef] using hfin

theorem weighted_l1_ge_sqrt {X : Type} [Fintype X] (p Y : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hY : ∀ x, 0 ≤ Y x) :
    (∑ x, p x * Y x ^ 2) * Real.sqrt (∑ x, p x * Y x ^ 2)
      ≤ (∑ x, p x * Y x) * Real.sqrt (∑ x, p x * Y x ^ 4) := by
  set A : ℝ := ∑ x, p x * Y x ^ 2 with hAdef
  set B : ℝ := ∑ x, p x * Y x with hBdef
  set D : ℝ := ∑ x, p x * Y x ^ 4 with hDdef
  have hAnn : 0 ≤ A := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (pow_nonneg (hY x) 2))
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hY x))
  have hDnn : 0 ≤ D := Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (pow_nonneg (hY x) 4))
  have h3 : A ^ 3 ≤ B ^ 2 * D := by
    have := weighted_l1_ge_of_fourth_moment p Y hp hY
    simpa only [← hAdef, ← hBdef, ← hDdef] using this
  have hsq : Real.sqrt (A ^ 3) ≤ Real.sqrt (B ^ 2 * D) := Real.sqrt_le_sqrt h3
  have hA3 : Real.sqrt (A ^ 3) = A * Real.sqrt A := by
    rw [show A ^ 3 = A ^ 2 * A by ring]
    rw [Real.sqrt_mul (sq_nonneg A) A, Real.sqrt_sq hAnn]
  have hBD : Real.sqrt (B ^ 2 * D) = B * Real.sqrt D := by
    rw [Real.sqrt_mul (sq_nonneg B) D, Real.sqrt_sq hBnn]
  rwa [hA3, hBD] at hsq

theorem exists_ge_of_average_ge {X : Type} [Fintype X] (hX : 0 < Fintype.card X)
    (f : X → ℝ) {c : ℝ}
    (h : c ≤ (∑ x, f x) / (Fintype.card X : ℝ)) : ∃ x, c ≤ f x := by
  by_contra hc
  have hc' : ∀ x, f x < c := fun x => not_le.mp (fun hle => hc ⟨x, hle⟩)
  haveI : Nonempty X := Fintype.card_pos_iff.mp hX
  have hlt : (∑ x, f x) < (Fintype.card X : ℝ) * c := by
    have hsum : (∑ x, f x) < ∑ _x : X, c :=
      Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
        (fun x _ => hc' x)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcardpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hX
  have hdiv : (∑ x, f x) / (Fintype.card X : ℝ) < c := by
    rw [div_lt_iff₀ hcardpos]
    linarith
  linarith

end Qatlib.Papers.AnyCircuit08.MainResults
