/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SwitchAdiab12.MainResults.SourceLemmaV1

@[expose] public section


/-! # The shifted convolution inequality -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SwitchAdiab12.MainResults.ConvCor

/-- Adding indices on both sides can only increase a binomial coefficient. -/
theorem chooseGrow (a b u v : ℕ) :
    (a + b).choose a ≤ (a + u + (b + v)).choose (a + u) := by
  calc
    (a + b).choose a ≤ (a + b + v).choose a := Nat.choose_le_add _ _ _
    _ = (a + (b + v)).choose (b + v) := by
      rw [Nat.add_assoc, Nat.choose_symm_add]
    _ ≤ (a + (b + v) + u).choose (b + v) := Nat.choose_le_add _ _ _
    _ = (a + u + (b + v)).choose (a + u) := by
      have he : a + (b + v) + u = a + u + (b + v) := by omega
      rw [he, Nat.choose_symm_add]

/-- Corollary V.2 follows from the verified two-factor bound by enlarging indices. -/
theorem corV2 (α : ℝ) (hα : 1 ≤ α) (k₁ k₂ n : ℕ) (hn : 1 ≤ n)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    (Nat.factorial (k₁ + k₂) : ℝ) /
        ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
      ((k₁ + n + 1 - i : ℕ) : ℝ) ^ (α * ((k₁ + n + 1 - i : ℕ) : ℝ)) *
      ((k₂ + i : ℕ) : ℝ) ^ (α * ((k₂ + i : ℕ) : ℝ))
    ≤ (4 : ℝ) ^ (-(α - 1) * ((min (k₁ + 1) (k₂ + 1) : ℕ) : ℝ)) *
      ((k₁ + k₂ + n + 1 : ℕ) : ℝ) ^
        (α * ((k₁ + k₂ + n + 1 : ℕ) : ℝ)) := by
  have hbase := Qatlib.Papers.SwitchAdiab12.MainResults.SourceLemmaV1.lemma_V1
    α hα (k₁ + (n - i)) (k₂ + i) 1 (by omega)
  have he₁ : k₁ + (n - i) + 1 = k₁ + n + 1 - i := by omega
  have he₂ : k₁ + (n - i) + (k₂ + i) + 1 = k₁ + k₂ + n + 1 := by omega
  rw [he₁, he₂] at hbase
  have hc : (Nat.factorial (k₁ + k₂) : ℝ) /
      ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) ≤
      (Nat.factorial (k₁ + (n-i) + (k₂+i)) : ℝ) /
      ((Nat.factorial (k₁+(n-i)) : ℝ) * (Nat.factorial (k₂+i) : ℝ)) := by
    rw [← Nat.cast_add_choose, ← Nat.cast_add_choose]
    exact_mod_cast chooseGrow k₁ k₂ (n-i) i
  have hm : min (k₁+1) (k₂+1) ≤ min (k₁+n+1-i) (k₂+i) := by
    exact min_le_min (by omega) (by omega)
  have hexp : -(α-1) * ((min (k₁+n+1-i) (k₂+i) : ℕ) : ℝ) ≤
      -(α-1) * ((min (k₁+1) (k₂+1) : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hm) (by linarith)
  calc
    _ ≤ (Nat.factorial (k₁+(n-i)+(k₂+i)) : ℝ) /
        ((Nat.factorial (k₁+(n-i)) : ℝ) * (Nat.factorial (k₂+i) : ℝ)) *
      ((k₁+n+1-i : ℕ) : ℝ) ^ (α*((k₁+n+1-i : ℕ) : ℝ)) *
      ((k₂+i : ℕ) : ℝ) ^ (α*((k₂+i : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ ≤ _ := hbase
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
end Qatlib.Papers.SwitchAdiab12.MainResults.ConvCor
