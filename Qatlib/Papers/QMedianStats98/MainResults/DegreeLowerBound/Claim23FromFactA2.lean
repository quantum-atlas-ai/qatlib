/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth.GridInterpolation
import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.DampingBound
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound

open Polynomial

theorem source_d1_choice {C : ℝ} (hC : 0 < C) (d : ℕ) :
    6 * (d : ℝ) ≤ C ^ 2 * ((Nat.ceil (6 / C ^ 2) * d : ℕ) : ℝ) := by
  have hC2 : (0 : ℝ) < C ^ 2 := by positivity
  have hceil : 6 / C ^ 2 ≤ (Nat.ceil (6 / C ^ 2) : ℝ) := Nat.le_ceil _
  have h6 : 6 ≤ C ^ 2 * (Nat.ceil (6 / C ^ 2) : ℝ) := by
    calc 6 = C ^ 2 * (6 / C ^ 2) := by field_simp
      _ ≤ C ^ 2 * (Nat.ceil (6 / C ^ 2) : ℝ) :=
          mul_le_mul_of_nonneg_left hceil (le_of_lt hC2)
  calc 6 * (d : ℝ) ≤ (C ^ 2 * (Nat.ceil (6 / C ^ 2) : ℝ)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right h6 (Nat.cast_nonneg d)
    _ = C ^ 2 * ((Nat.ceil (6 / C ^ 2) * d : ℕ) : ℝ) := by push_cast; ring

theorem source_claim_2_3_of_fact_A2 {q : Polynomial ℝ} {c C : ℝ} {d d1 n : ℕ}
    (hC : 0 < C) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hdeg : q.natDegree ≤ d)
    (hd1 : 6 * (d : ℝ) ≤ C ^ 2 * (d1 : ℝ))
    (hgrid : ∀ i : ℕ, i ≤ n → |q.eval ((i : ℕ) : ℝ)| ≤ (4 / 3 : ℝ))
    (x : ℝ) (hxC : C ≤ |x|) (hx1 : |x| ≤ 1)
    (hx0 : 0 ≤ x + c) (hxn : x + c ≤ (n : ℝ)) :
    |q.eval (x + c) * (1 - x ^ 2) ^ d1| ≤ 1 := by
  have hfact :=
    Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth.source_fact_A2
      (d := d) (n := n) hdn (p := q) (c := (4 / 3 : ℝ)) (x := x + c)
      hdeg (by norm_num) hgrid ⟨hx0, hxn⟩
  have hq : |q.eval (x + c)| ≤ (4 / 3 : ℝ) * (2 : ℝ) ^ d := by
    calc |q.eval (x + c)| ≤ (2 : ℝ) ^ d * (4 / 3 : ℝ) := hfact
      _ = (4 / 3 : ℝ) * (2 : ℝ) ^ d := by ring
  have hdamp := source_shifted_algebraic_bound (d := d) (d1 := d1) hC hxC hx1 hd1 hd
  have hnonneg : (0 : ℝ) ≤ (1 - x ^ 2) ^ d1 := by
    have hx2le : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, hx1]
    have : 0 ≤ 1 - x ^ 2 := by linarith
    positivity
  rw [abs_mul, abs_of_nonneg hnonneg]
  exact (mul_le_mul hq le_rfl hnonneg (by positivity)).trans hdamp

theorem source_claim_2_3_of_fact_A2_ceil {q : Polynomial ℝ} {c C : ℝ} {d n : ℕ}
    (hC : 0 < C) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hdeg : q.natDegree ≤ d)
    (hgrid : ∀ i : ℕ, i ≤ n → |q.eval ((i : ℕ) : ℝ)| ≤ (4 / 3 : ℝ))
    (x : ℝ) (hxC : C ≤ |x|) (hx1 : |x| ≤ 1)
    (hx0 : 0 ≤ x + c) (hxn : x + c ≤ (n : ℝ)) :
    |q.eval (x + c) * (1 - x ^ 2) ^ (Nat.ceil (6 / C ^ 2) * d)| ≤ 1 :=
  source_claim_2_3_of_fact_A2 (d1 := Nat.ceil (6 / C ^ 2) * d)
    hC hd hdn hdeg (source_d1_choice hC d) hgrid x hxC hx1 hx0 hxn

end Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
