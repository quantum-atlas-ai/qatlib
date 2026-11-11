/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFCountBounds

/-!
# Choosing amplification rounds from coefficient mass

This module chooses the least number `rounds` for which the coefficient mass fits the sine
amplitude at the associated odd query count. The resulting `normalization` bounds the mass and
is bounded by `queries`, providing a linear query estimate for the amplification construction
associated with [AftabAnTrivisa2026].

## Main statements

* `queries_minimal`: proves minimality among feasible odd query counts.
* `queries_linear`: bounds the query count above and below in terms of mass.
* `queries_one`: handles unit coefficient mass.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAChoice

open scoped Classical
set_option warningAsError false

/-- The amplification angle π/(2q) associated with query count q. -/
def angle (q : ℕ) : ℝ := Real.pi / (2 * (q : ℝ))

/-- For positive q, the amplification angle lies in (0, π/2]. -/
theorem angle_bounds (q : ℕ) (hq : 0 < q) : 0 < angle q ∧ angle q ≤ Real.pi / 2 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  exact ⟨by unfold angle; positivity,
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)⟩

/-- The sine of the amplification angle is positive for positive q. -/
theorem sin_pos (q : ℕ) (hq : 0 < q) : 0 < Real.sin (angle q) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_bounds q hq).1 (by linarith [(angle_bounds q hq).2, Real.pi_pos])

/-- For positive q, the sine of π/(2q) is at least 1/q. -/
theorem inv_query_le_sin (q : ℕ) (hq : 0 < q) : 1 / (q : ℝ) ≤ Real.sin (angle q) := by
  have h := Real.mul_le_sin (angle_bounds q hq).1.le (angle_bounds q hq).2
  have he : (2 / Real.pi) * angle q = 1 / (q : ℝ) := by
    unfold angle
    field_simp
  rwa [he] at h

/-- The condition that A times the sine amplitude for 2n + 1 queries is at most 1. -/
def admissible (A : ℝ) (n : ℕ) : Prop := A * Real.sin (angle (2 * n + 1)) ≤ 1

/-- The ceiling of π|A|/4 is a feasible amplification round count. -/
theorem admissible_witness (A : ℝ) : admissible A (Nat.ceil (Real.pi * |A| / 4)) := by
  let n := Nat.ceil (Real.pi * |A| / 4)
  have hn : Real.pi * |A| / 4 ≤ (n : ℝ) := Nat.le_ceil _
  have hq : 0 < 2 * n + 1 := by omega
  have hsin := Real.sin_le (angle_bounds (2 * n + 1) hq).1.le
  have hangle : |A| * angle (2 * n + 1) ≤ 1 := by
    rw [angle, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((2 * n + 1 : ℕ) : ℝ))).mpr
    push_cast
    nlinarith
  exact (mul_le_mul_of_nonneg_right (le_abs_self A) (sin_pos _ hq).le).trans
    ((mul_le_mul_of_nonneg_left hsin (abs_nonneg A)).trans hangle)

/-- Every real coefficient mass parameter has a feasible amplification round count. -/
theorem admissible_exists (A : ℝ) : ∃ n, admissible A n := ⟨_, admissible_witness A⟩

/-- The least natural number of rounds satisfying the sine-amplitude feasibility condition. -/
def rounds (A : ℝ) : ℕ := Nat.find (admissible_exists A)

/-- The odd query count 2 times the selected round count plus 1. -/
def queries (A : ℝ) : ℕ := 2 * rounds A + 1

/-- The selected query count is strictly positive. -/
theorem queries_pos (A : ℝ) : 0 < queries A := by unfold queries; omega

/-- The selected query count is odd. -/
theorem queries_odd (A : ℝ) : Odd (queries A) := ⟨rounds A, by unfold queries; omega⟩

/-- The selected query count satisfies the sine-amplitude feasibility condition. -/
theorem selected_admissible (A : ℝ) : A * Real.sin (angle (queries A)) ≤ 1 :=
  Nat.find_spec (admissible_exists A)

/-- Every smaller round count makes A times its sine amplitude strictly greater than 1. -/
theorem smaller_fails (A : ℝ) (n : ℕ) (hn : n < rounds A) :
    1 < A * Real.sin (angle (2 * n + 1)) :=
  lt_of_not_ge (Nat.find_min (admissible_exists A) hn)

/-- The selected query count is at most the odd query count of any feasible round choice. -/
theorem queries_minimal (A : ℝ) (n : ℕ) (hn : admissible A n) : queries A ≤ 2 * n + 1 := by
  have h : rounds A ≤ n := Nat.find_min' (admissible_exists A) hn
  unfold queries
  omega

/-- The reciprocal sine amplitude at the selected query count. -/
def normalization (A : ℝ) : ℝ := 1 / Real.sin (angle (queries A))

/-- The chosen reciprocal-sine normalization is at least A. -/
theorem mass_le_normalization (A : ℝ) : A ≤ normalization A :=
  (le_div_iff₀ (sin_pos _ (queries_pos A))).mpr (selected_admissible A)

/-- The chosen reciprocal-sine normalization is at most the selected query count. -/
theorem normalization_le_queries (A : ℝ) : normalization A ≤ (queries A : ℝ) := by
  have hqR : 0 < (queries A : ℝ) := by exact_mod_cast queries_pos A
  have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / (queries A : ℝ))
    (inv_query_le_sin _ (queries_pos A))
  simpa only [one_div_one_div] using! h

/-- For A ≥ 0, the selected query count is at most πA/2 + 3. -/
theorem queries_bound (A : ℝ) (hA : 0 ≤ A) : (queries A : ℝ) ≤ Real.pi * A / 2 + 3 := by
  have h := queries_minimal A _ (admissible_witness A)
  have hR : (queries A : ℝ) ≤ 2 * (Nat.ceil (Real.pi * |A| / 4) : ℝ) + 1 := by exact_mod_cast h
  rw [abs_of_nonneg hA] at hR
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.pi * A / 4 by positivity)
  linarith

/-- For A ≥ 1, the selected query count lies between A and (π/2 + 3)A. -/
theorem queries_linear (A : ℝ) (hA : 1 ≤ A) :
    A ≤ (queries A : ℝ) ∧ (queries A : ℝ) ≤ (Real.pi / 2 + 3) * A := by
  refine ⟨(mass_le_normalization A).trans (normalization_le_queries A), ?_⟩
  exact (queries_bound A (by linarith)).trans (by nlinarith)

/-- Unit mass requires zero amplification rounds. -/
theorem rounds_one : rounds 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h : admissible 1 0 := by norm_num [admissible, angle]
  exact Nat.find_min' (admissible_exists 1) h

/-- Unit mass requires one query. -/
theorem queries_one : queries 1 = 1 := by simp [queries, rounds_one]

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAChoice
