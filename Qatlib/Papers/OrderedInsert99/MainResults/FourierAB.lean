/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Fourier matching identities and small two-query cases

The cosine sums `A0fun` and `B0fun` describe the initial Fourier data for the invariant
ordered-insertion framework of [FarhiEtAl1999]. Symmetric and antisymmetric coefficient sums
vanish at the corresponding half-grid angles. Explicit formulas establish `TwoQueryCondition`
for `N = 2, 3, 4`.

## Main statements

* `A_sum_vanishes_half`: A cosine sum with coefficients symmetric under `r ↦ N - r` vanishes
  whenever `cos (N * θ / 2) = 0`.
* `B_sum_vanishes_roots`: A cosine sum with coefficients antisymmetric under `r ↦ N - r`
  vanishes whenever `sin (N * θ / 2) = 0`.
* `twoQueryCondition_four`: The two-query nonnegativity condition holds for `N = 4`.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators

/-- The sum of `cos (r * θ)` over integer frequencies `1 ≤ r < N`. -/
def A0fun (N : ℕ) (θ : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 N, Real.cos ((r : ℝ) * θ)

/-- The cosine sum over `1 ≤ r < N` with coefficient `1 - 2 * r / N`. -/
def B0fun (N : ℕ) (θ : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 N, (1 - 2 * (r : ℝ) / (N : ℝ)) * Real.cos ((r : ℝ) * θ)

/-- The condition that `1 + B0fun N θ` is nonnegative for every real angle `θ`. -/
def TwoQueryCondition (N : ℕ) : Prop := ∀ θ : ℝ, 0 ≤ 1 + B0fun N θ

/-- For `1 ≤ r < N`, the coefficient at `r` is the negative of the coefficient at `N - r`. -/
theorem B0coeff_antisymm {N r : ℕ} (h1 : 1 ≤ r) (h2 : r < N) :
    (1 - 2 * (r : ℝ) / (N : ℝ))
      = -(1 - 2 * ((N - r : ℕ) : ℝ) / (N : ℝ)) := by
  have hNr : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) := by
    rw [Nat.cast_sub (by omega : r ≤ N)]
  rw [hNr]
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  field_simp
  ring

/-- For positive `N`, the sum of the initial A and B functions is `2 / N` times the cosine sum
weighted by `N - r` [FarhiEtAl1999]. -/
theorem A0fun_add_B0fun {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) :
    A0fun N θ + B0fun N θ
      = (2 / (N : ℝ)) *
          ∑ r ∈ Finset.Ico 1 N, ((N : ℝ) - (r : ℝ)) * Real.cos ((r : ℝ) * θ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  unfold A0fun B0fun
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  field_simp
  ring

/-- Reindexing a sum over `1 ≤ r < N` by `r ↦ N - r` preserves the sum. -/
theorem sum_Ico_reindex {N : ℕ} (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Ico 1 N, f (N - r)) = ∑ r ∈ Finset.Ico 1 N, f r := by
  have h := Finset.sum_Ico_reflect (f := f) (k := 1) (m := N) (n := N)
    (by omega : N ≤ N + 1)
  simpa using h

/-- A cosine sum with coefficients symmetric under `r ↦ N - r` vanishes whenever `cos (N * θ /
2) = 0` [FarhiEtAl1999]. -/
theorem A_sum_vanishes_half {N : ℕ} (a : ℕ → ℝ)
    (ha : ∀ r, 1 ≤ r → r < N → a r = a (N - r))
    {θ : ℝ} (hθ : Real.cos ((N : ℝ) * θ / 2) = 0) :
    ∑ r ∈ Finset.Ico 1 N, a r * Real.cos ((r : ℝ) * θ) = 0 := by
  set S : ℝ := ∑ r ∈ Finset.Ico 1 N, a r * Real.cos ((r : ℝ) * θ) with hS
  have hreindex :
      (∑ r ∈ Finset.Ico 1 N, a (N - r) * Real.cos (((N - r : ℕ) : ℝ) * θ)) = S := by
    rw [hS]
    exact sum_Ico_reindex (fun j : ℕ => a j * Real.cos ((j : ℝ) * θ))
  have hdouble :
      2 * S = ∑ r ∈ Finset.Ico 1 N,
        (a r * Real.cos ((r : ℝ) * θ)
          + a (N - r) * Real.cos (((N - r : ℕ) : ℝ) * θ)) := by
    rw [Finset.sum_add_distrib, hreindex, ← hS]
    ring
  have hterm : ∀ r ∈ Finset.Ico 1 N,
      a r * Real.cos ((r : ℝ) * θ)
          + a (N - r) * Real.cos (((N - r : ℕ) : ℝ) * θ)
        = 2 * Real.cos ((N : ℝ) * θ / 2) *
            (a r * Real.cos (((2 * (r : ℝ) - (N : ℝ)) * θ) / 2)) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hr
    have hrle : r ≤ N := by omega
    have hcast : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) := by
      rw [Nat.cast_sub hrle]
    have har : a (N - r) = a r := (ha r hr1 hr2).symm
    rw [har, hcast]
    have hfac : a r * Real.cos ((r : ℝ) * θ)
          + a r * Real.cos (((N : ℝ) - (r : ℝ)) * θ)
        = a r * (Real.cos ((r : ℝ) * θ) + Real.cos (((N : ℝ) - (r : ℝ)) * θ)) := by
      ring
    have hcos := Real.cos_add_cos ((r : ℝ) * θ) (((N : ℝ) - (r : ℝ)) * θ)
    have h1 : ((r : ℝ) * θ + ((N : ℝ) - (r : ℝ)) * θ) / 2 = (N : ℝ) * θ / 2 := by
      ring
    have h2 : ((r : ℝ) * θ - ((N : ℝ) - (r : ℝ)) * θ) / 2
        = ((2 * (r : ℝ) - (N : ℝ)) * θ) / 2 := by
      ring
    rw [hfac, hcos, h1, h2]
    ring
  have hzero : 2 * S = 0 := by
    rw [hdouble, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hθ]
    ring
  linarith

/-- A cosine sum with coefficients antisymmetric under `r ↦ N - r` vanishes whenever `sin (N * θ
/ 2) = 0` [FarhiEtAl1999]. -/
theorem B_sum_vanishes_roots {N : ℕ} (b : ℕ → ℝ)
    (hb : ∀ r, 1 ≤ r → r < N → b (N - r) = -b r)
    {θ : ℝ} (hθ : Real.sin ((N : ℝ) * θ / 2) = 0) :
    ∑ r ∈ Finset.Ico 1 N, b r * Real.cos ((r : ℝ) * θ) = 0 := by
  set S : ℝ := ∑ r ∈ Finset.Ico 1 N, b r * Real.cos ((r : ℝ) * θ) with hS
  have hreindex :
      (∑ r ∈ Finset.Ico 1 N, b (N - r) * Real.cos (((N - r : ℕ) : ℝ) * θ)) = S := by
    rw [hS]
    exact sum_Ico_reindex (fun j : ℕ => b j * Real.cos ((j : ℝ) * θ))
  have hdouble :
      2 * S = ∑ r ∈ Finset.Ico 1 N,
        (b r * Real.cos ((r : ℝ) * θ)
          + b (N - r) * Real.cos (((N - r : ℕ) : ℝ) * θ)) := by
    rw [Finset.sum_add_distrib, hreindex, ← hS]
    ring
  have hterm : ∀ r ∈ Finset.Ico 1 N,
      b r * Real.cos ((r : ℝ) * θ)
          + b (N - r) * Real.cos (((N - r : ℕ) : ℝ) * θ)
        = (-2 * Real.sin ((N : ℝ) * θ / 2)) *
            (b r * Real.sin (((2 * (r : ℝ) - (N : ℝ)) * θ) / 2)) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hr
    have hrle : r ≤ N := by omega
    have hcast : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) := by
      rw [Nat.cast_sub hrle]
    have hbr : b (N - r) = -b r := hb r hr1 hr2
    rw [hbr, hcast]
    have hfac : b r * Real.cos ((r : ℝ) * θ)
          + (-b r) * Real.cos (((N : ℝ) - (r : ℝ)) * θ)
        = b r * (Real.cos ((r : ℝ) * θ) - Real.cos (((N : ℝ) - (r : ℝ)) * θ)) := by
      ring
    have hcos := Real.cos_sub_cos ((r : ℝ) * θ) (((N : ℝ) - (r : ℝ)) * θ)
    have h1 : ((r : ℝ) * θ + ((N : ℝ) - (r : ℝ)) * θ) / 2 = (N : ℝ) * θ / 2 := by
      ring
    have h2 : ((r : ℝ) * θ - ((N : ℝ) - (r : ℝ)) * θ) / 2
        = ((2 * (r : ℝ) - (N : ℝ)) * θ) / 2 := by
      ring
    rw [hfac, hcos, h1, h2]
    ring
  have hzero : 2 * S = 0 := by
    rw [hdouble, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hθ]
    ring
  linarith

/-- The initial B cosine sum is identically zero for `N = 2`. -/
theorem B0fun_two (θ : ℝ) : B0fun 2 θ = 0 := by
  have hIco : Finset.Ico 1 2 = ({1} : Finset ℕ) := by decide
  unfold B0fun
  rw [hIco]
  norm_num

/-- The expression `1 + B0fun 2 θ` is nonnegative at every angle. -/
theorem B0_nonneg_two (θ : ℝ) : 0 ≤ 1 + B0fun 2 θ := by
  rw [B0fun_two]
  norm_num

/-- For `N = 3`, the initial B function is one third of `cos θ - cos (2 * θ)`. -/
theorem B0fun_three (θ : ℝ) :
    B0fun 3 θ = (1 / 3) * Real.cos θ - (1 / 3) * Real.cos (2 * θ) := by
  have hIco : Finset.Ico 1 3 = ({1, 2} : Finset ℕ) := by decide
  unfold B0fun
  rw [hIco]
  norm_num [Finset.sum_pair]
  ring

/-- The expression `1 + B0fun 3 θ` is nonnegative at every angle. -/
theorem B0_nonneg_three (θ : ℝ) : 0 ≤ 1 + B0fun 3 θ := by
  rw [B0fun_three]
  have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  rw [h2]
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.cos θ)]

/-- For `N = 4`, the initial B function is one half of `cos θ - cos (3 * θ)`. -/
theorem B0fun_four (θ : ℝ) :
    B0fun 4 θ = (1 / 2) * Real.cos θ - (1 / 2) * Real.cos (3 * θ) := by
  have hIco : Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) := by decide
  unfold B0fun
  rw [hIco]
  norm_num [Finset.sum_insert]
  ring

/-- The expression `1 + B0fun 4 θ` is nonnegative at every angle. -/
theorem B0_nonneg_four (θ : ℝ) : 0 ≤ 1 + B0fun 4 θ := by
  rw [B0fun_four, Real.cos_three_mul]
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hc2 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have key : 1 + 2 * Real.cos θ - 2 * Real.cos θ ^ 3
      = (1 - Real.cos θ) * (2 * Real.cos θ ^ 2 + 2 * Real.cos θ + 1 / 2)
        + (1 + Real.cos θ) / 2 := by ring
  have h1 : 0 ≤ 1 - Real.cos θ := by linarith
  have h2 : 0 ≤ 2 * Real.cos θ ^ 2 + 2 * Real.cos θ + 1 / 2 := by
    nlinarith [sq_nonneg (Real.cos θ + 1 / 2)]
  have h3 : 0 ≤ 1 + Real.cos θ := by linarith
  nlinarith [key, mul_nonneg h1 h2, h3]

/-- The two-query nonnegativity condition holds for `N = 2` [FarhiEtAl1999]. -/
theorem twoQueryCondition_two : TwoQueryCondition 2 := B0_nonneg_two

/-- The two-query nonnegativity condition holds for `N = 3` [FarhiEtAl1999]. -/
theorem twoQueryCondition_three : TwoQueryCondition 3 := B0_nonneg_three

/-- The two-query nonnegativity condition holds for `N = 4` [FarhiEtAl1999]. -/
theorem twoQueryCondition_four : TwoQueryCondition 4 := B0_nonneg_four

end Qatlib.Papers.OrderedInsert99.MainResults
