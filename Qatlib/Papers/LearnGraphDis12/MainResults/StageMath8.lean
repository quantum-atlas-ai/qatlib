/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
Arithmetic components of Belovs, arXiv:1205.1534v2, Sections 4.2 and 5.2.
These identities do not construct a learning graph or a quantum query algorithm.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearnGraphDis12.MainResults

/-! ## The exponent arithmetic of §5.2

At the balanced choice of the parameters `r₁,…,r_{k−1}` the paper's recurrences
reduce to one fixed-point equation for the exponent `ρ₁ = log_n r₁`
(p. 14):

`ρ₁ = 1/2 + (1/2 + ⋯ + 1/2^{k−1})(1−ρ₁)`.

Since `1/2 + ⋯ + 1/2^{k−1} = 1 − 2^{−(k−1)}`, this is the equation below; its
solution is `ρ₁ = 1 − 2^{k−2}/(2^k − 1)`.
-/

/-- Fixed arXiv:1205.1534v2, §5.2 (pp. 13–14).  The exponent
`ρ = 1 − 2^{k−2}/(2^k − 1)` of Theorem 8 satisfies the paper's fixed-point
equation `ρ = 1/2 + (1 − 2^{−(k−1)})·(1 − ρ)`.

(The paper derives this equation by equating the first term `r₁` of (12) with
the last term `n^{k}/(r₁⋯r_{k−1})` and substituting `ρ_i = log_n r_i`.) -/
theorem kDistinctness_exponent_fixed_point (k : ℕ) (hk : 2 ≤ k) :
    1 - (2 : ℝ) ^ (k - 2) / ((2 : ℝ) ^ k - 1) =
      1 / 2 + (1 - ((2 : ℝ) ^ (k - 1))⁻¹) *
        (1 - (1 - (2 : ℝ) ^ (k - 2) / ((2 : ℝ) ^ k - 1))) := by
  set A : ℝ := (2 : ℝ) ^ k with hAdef
  have hA2 : (2 : ℝ) ≤ A := by
    rw [hAdef]
    have h : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    norm_num at h ⊢
    linarith
  have hA0 : A ≠ 0 := by linarith
  have hAne : A - 1 ≠ 0 := by linarith
  have hpow2 : (2 : ℝ) ^ (k - 2) = A / 4 := by
    have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk
    have h : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 2) * 4 := by
      conv_lhs => rw [← hk2]
      rw [pow_add]
      norm_num
    rw [hAdef, h]
    ring
  have hpow1 : (2 : ℝ) ^ (k - 1) = A / 2 := by
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
    have h : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      conv_lhs => rw [← hk1]
      rw [pow_add]
      norm_num
    rw [hAdef, h]
    ring
  rw [hpow2, hpow1]
  field_simp
  ring

/-- Sanity check, paper §5.2 / p. 14: at `k = 2` the exponent is `2/3`, the
element-distinctness complexity `Θ(n^{2/3})` quoted in the introduction. -/
theorem kDistinctness_exponent_two :
    (1 : ℝ) - (2 : ℝ) ^ (2 - 2) / ((2 : ℝ) ^ 2 - 1) = 2 / 3 := by
  norm_num

/-- The exponent lies strictly between `0` and `1` for every `k ≥ 2`, so
Theorem 8's bound is a genuine sublinear-in-`n` query count. -/
theorem kDistinctness_exponent_pos_lt_one (k : ℕ) (hk : 2 ≤ k) :
    0 < 1 - (2 : ℝ) ^ (k - 2) / ((2 : ℝ) ^ k - 1) ∧
      1 - (2 : ℝ) ^ (k - 2) / ((2 : ℝ) ^ k - 1) < 1 := by
  set A : ℝ := (2 : ℝ) ^ k with hAdef
  have hA2 : (2 : ℝ) ≤ A := by
    rw [hAdef]
    have h : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    norm_num at h ⊢
    linarith
  have hpow2 : (2 : ℝ) ^ (k - 2) = A / 4 := by
    have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk
    have h : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 2) * 4 := by
      conv_lhs => rw [← hk2]
      rw [pow_add]
      norm_num
    rw [hAdef, h]
    ring
  rw [hpow2]
  constructor
  · rw [sub_pos, div_lt_iff₀ (by linarith : (0 : ℝ) < A - 1)]
    linarith
  · rw [sub_lt_self_iff, div_pos_iff]
    left
    constructor <;> linarith


end Qatlib.Papers.LearnGraphDis12.MainResults
