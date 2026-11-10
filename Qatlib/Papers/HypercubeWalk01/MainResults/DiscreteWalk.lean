/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypercubeWalk01.MainResults.CubeFourier
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators symmDiff

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

namespace Qatlib.Papers.HypercubeWalk01.MainResults

noncomputable def discOmega (n k : ℕ) : ℝ :=
  Real.arccos (1 - 2 * (k : ℝ) / n)

noncomputable def discOverlapA (n k j l : ℕ) : ℝ :=
  (Real.cos (discOmega n k) -
      Real.cos (discOmega n (j + l)) * Real.cos (discOmega n (k - j + l))) /
    (Real.sin (discOmega n (j + l)) * Real.sin (discOmega n (k - j + l)))

noncomputable def discCoeff (n t k : ℕ) : ℝ :=
  (1 : ℝ) / 2 ^ n *
    ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (n - k + 1),
      (Nat.choose k j : ℝ) * (Nat.choose (n - k) l : ℝ) *
        ((1 - discOverlapA n k j l) / 2 *
            Real.cos ((discOmega n (j + l) + discOmega n (k - j + l)) * t) +
          (1 + discOverlapA n k j l) / 2 *
            Real.cos ((discOmega n (j + l) - discOmega n (k - j + l)) * t))

noncomputable def discDist (n t : ℕ) (x : Cube n) : ℝ :=
  uniformMass n * ∑ S : Finset (Fin n), discCoeff n t S.card * chi S x

noncomputable def parityParityMass (n t : ℕ) (x : Cube n) : ℝ :=
  if (∑ i, if x i then (1 : ℕ) else 0) % 2 = t % 2 then ((2 : ℝ) ^ (n - 1))⁻¹ else 0

noncomputable def tvDistParityAt (n t : ℕ) (P : Cube n → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |P x - parityParityMass n t x|

def IsInstantaneousMixingAt (n t : ℕ) (ε : ℝ) (P : Cube n → ℝ) : Prop :=
  tvDistParityAt n t P ≤ ε

lemma discOmega_zero {n : ℕ} (_hn : 0 < n) : discOmega n 0 = 0 := by
  have harg : 1 - 2 * (((0 : ℕ) : ℝ)) / (n : ℝ) = 1 := by simp
  rw [discOmega, harg, Real.arccos_one]

lemma discOmega_self {n : ℕ} (hn : 0 < n) : discOmega n n = Real.pi := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have harg : 1 - 2 * (n : ℝ) / n = -1 := by
    field_simp
    ring
  simp only [discOmega, harg]
  exact Real.arccos_neg_one

theorem cos_two_t_at_ceil_odd_multiple {n k : ℕ} (hn : 0 < n) (hk : Odd k) :
    |Real.cos (2 * ((⌈(k : ℝ) * (Real.pi / 4) * n⌉₊ : ℕ) : ℝ) / n)| ≤ 2 / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨m, hm⟩ := hk
  set x : ℝ := (k : ℝ) * (Real.pi / 4) * n with hxdef
  have hx0 : 0 ≤ x := by
    simp only [hxdef]
    positivity
  set t : ℕ := ⌈x⌉₊ with htdef
  have htge : x ≤ (t : ℝ) := Nat.le_ceil x
  have htlt : (t : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hcos0 : Real.cos (2 * x / (n : ℝ)) = 0 := by
    have harg : 2 * x / (n : ℝ) = (k : ℝ) * Real.pi / 2 := by
      simp only [hxdef]
      field_simp
      ring
    rw [harg]
    have hsplit : (k : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi + Real.pi / 2 := by
      rw [hm]
      push_cast
      ring
    rw [hsplit, Real.cos_add]
    simp [Real.sin_nat_mul_pi]
  have hδ : |2 * (t : ℝ) / (n : ℝ) - 2 * x / (n : ℝ)| ≤ 2 / (n : ℝ) := by
    have heq : 2 * (t : ℝ) / (n : ℝ) - 2 * x / (n : ℝ) = 2 * ((t : ℝ) - x) / (n : ℝ) := by
      ring
    rw [heq, abs_div, abs_of_pos hnR]
    have hnum : |2 * ((t : ℝ) - x)| = 2 * ((t : ℝ) - x) := by
      rw [abs_of_nonneg]
      linarith
    rw [hnum]
    exact div_le_div_of_nonneg_right (by linarith) hnR.le
  have hshift : Real.cos (2 * (t : ℝ) / (n : ℝ)) =
      Real.cos (2 * x / (n : ℝ) + (2 * (t : ℝ) / (n : ℝ) - 2 * x / (n : ℝ))) := by
    rw [add_sub_cancel]
  rw [hshift, Real.cos_add, hcos0, zero_mul, zero_sub, abs_neg, abs_mul]
  calc |Real.sin (2 * x / (n : ℝ))| *
        |Real.sin (2 * (t : ℝ) / (n : ℝ) - 2 * x / (n : ℝ))|
      ≤ 1 * |2 * (t : ℝ) / (n : ℝ) - 2 * x / (n : ℝ)| := by
        refine mul_le_mul (Real.abs_sin_le_one _) ?_ (abs_nonneg _) (by norm_num)
        exact Real.abs_sin_le_abs
    _ ≤ 1 * (2 / (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hδ (by norm_num)
    _ = 2 / (n : ℝ) := one_mul _

end Qatlib.Papers.HypercubeWalk01.MainResults
