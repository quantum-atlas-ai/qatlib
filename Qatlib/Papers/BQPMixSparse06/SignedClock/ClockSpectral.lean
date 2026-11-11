/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Lemma3SparseConversion
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Signed-clock entries and spectral tail bounds

The matrix `signScale W` is the rescaled symmetrization `√2 • (W + Wᵀ)`. The predicates
`TwoBranchEntries` and `NoBacktrack` ensure its entries belong to `{-1, 0, 1}`, and row and
column sparsity bounds control its row support.

The scalar spectral estimates pair reflected odd moments, isolate an endpoint contribution, and
suppress the remaining clock modes. These estimates support the signed-clock reductions of
[JanzingWocjan2006].

## Main statements

* `signScale_entry_three`: the rescaled clock matrix has signed integer entries under the stated
  entry and orientation assumptions.
* `clock_tail_polynomial_gap`: a logarithmic lower bound on the moment order suppresses the
  geometric tail.
* `clock_endpoint_gap`: the endpoint contribution survives with an additive loss at most `w /
  2`.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.SignedClock

open Finset Matrix

/-- The rescaled symmetrization `√2 • (W + Wᵀ)` of a real matrix. -/
def signScale {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Real.sqrt 2 • (W + Wᵀ)

/-- Each entry of `signScale W` is `√2 * (W i j + W j i)`. -/
theorem signScale_apply {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    signScale W i j = Real.sqrt 2 * (W i j + W j i) := by
  simp [signScale, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.transpose_apply]

/-- The condition that every entry of `W` is zero, `√2 / 2`, or `-√2 / 2`. -/
def TwoBranchEntries {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, W i j = 0 ∨ W i j = Real.sqrt 2 / 2 ∨ W i j = -(Real.sqrt 2 / 2)

/-- The condition that for every pair of indices at least one of `W i j` and `W j i` is zero. -/
def NoBacktrack {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, W i j = 0 ∨ W j i = 0

/-- Under the two-branch entry condition and the no-backtracking condition, each entry of
`signScale W` is zero, one, or minus one [JanzingWocjan2006]. -/
theorem signScale_entry_three {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (hW : TwoBranchEntries W) (hun : NoBacktrack W) (i j : Fin N) :
    signScale W i j = 0 ∨ signScale W i j = 1 ∨ signScale W i j = -1 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpos : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by nlinarith
  have hneg : Real.sqrt 2 * (-(Real.sqrt 2 / 2)) = -1 := by nlinarith
  rw [signScale_apply]
  rcases hun i j with h | h
  · rw [h, zero_add]
    rcases hW j i with h0 | h1 | h1
    · rw [h0]; exact Or.inl (by ring)
    · rw [h1]; exact Or.inr (Or.inl hpos)
    · rw [h1]; exact Or.inr (Or.inr hneg)
  · rw [h, add_zero]
    rcases hW i j with h0 | h1 | h1
    · rw [h0]; exact Or.inl (by ring)
    · rw [h1]; exact Or.inr (Or.inl hpos)
    · rw [h1]; exact Or.inr (Or.inr hneg)

/-- If every row and column of `W` has at most two nonzero entries, each row of `signScale W`
has at most four [JanzingWocjan2006]. -/
theorem signScale_row_card_le_four {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (hrow : ∀ i, (univ.filter (fun j : Fin N => W i j ≠ 0)).card ≤ 2)
    (hcol : ∀ i, (univ.filter (fun j : Fin N => W j i ≠ 0)).card ≤ 2)
    (i : Fin N) :
    (univ.filter (fun j : Fin N => signScale W i j ≠ 0)).card ≤ 4 := by
  have hs : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  have hset : (univ.filter (fun j : Fin N => signScale W i j ≠ 0)) =
      (univ.filter (fun j : Fin N => W i j + W j i ≠ 0)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, signScale_apply]
    rw [mul_ne_zero_iff]
    simp [hs]
  rw [hset]
  exact Qatlib.Papers.BQPMixSparse06.MainResults.add_transpose_row_card_le_four
    W hrow hcol i

/-- For odd `M`, a complex number has `M`th power minus one exactly when its negative has `M`th
power one [JanzingWocjan2006]. -/
theorem antiRoot_eq_neg {M : ℕ} (hM : Odd M) (w : ℂ) :
    w ^ M = -1 ↔ (-w) ^ M = 1 := by
  rw [Odd.neg_pow hM]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have := congrArg Neg.neg h
    simpa using this

/-- For odd moment order, the weighted moments of `x` and its reflection combine into the weight
difference times the moment of `x` [JanzingWocjan2006]. -/
theorem reflected_cosine_moment {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (p0 p1 : ℝ) (m : ℕ) (hm : Odd m) :
    (∑ l, p0 * x l ^ m) + (∑ l, p1 * (-(x l)) ^ m) =
      (p0 - p1) * ∑ l, x l ^ m := by
  have hneg : ∀ l : ι, (-(x l)) ^ m = -(x l ^ m) := fun l => Odd.neg_pow hm (x l)
  simp only [hneg]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_neg_distrib]
  ring

/-- If the distinguished clock value is one, its contribution can be separated from the weighted
moment sum [JanzingWocjan2006]. -/
theorem clock_endpoint_extract {M : ℕ} [NeZero M] (x : Fin M → ℝ)
    (hx0 : x 0 = 1) (p : ℝ) (m : ℕ) :
    p * (∑ l, x l ^ m) = p + p * (∑ l ∈ (univ \ {0}), x l ^ m) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin M)), hx0, one_pow, ← Finset.erase_eq]
  ring

/-- If all nonendpoint values have absolute value at most `c`, the absolute tail moment is at
most `(M - 1) * c ^ m` [JanzingWocjan2006]. -/
theorem clock_tail_bound {M : ℕ} [NeZero M] (x : Fin M → ℝ) (c : ℝ) (m : ℕ)
    (_hc : 0 ≤ c) (hx : ∀ l, l ≠ 0 → |x l| ≤ c) :
    |∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), x l ^ m| ≤
      ((M - 1 : ℕ) : ℝ) * c ^ m := by
  classical
  have hcard : ((Finset.univ : Finset (Fin M)) \ {0}).card = M - 1 := by
    rw [Finset.card_sdiff]
    simp
  calc |∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), x l ^ m|
      ≤ ∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), |x l ^ m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), |x l| ^ m := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_pow]
    _ ≤ ∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), c ^ m := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hl0 : l ≠ 0 := by
          simpa using (Finset.mem_sdiff.mp hl).2
        exact pow_le_pow_left₀ (abs_nonneg (x l)) (hx l hl0) m
    _ = (((Finset.univ : Finset (Fin M)) \ {0}).card : ℝ) * c ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((M - 1 : ℕ) : ℝ) * c ^ m := by rw [hcard]

/-- For a natural clock length at least three, `cos (π / M)` is strictly less than one. -/
theorem cos_pi_div_lt_one {M : ℕ} (hM : 3 ≤ M) : Real.cos (Real.pi / M) < 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxpos : 0 < Real.pi / M := by positivity
  have hx1 : -(2 * Real.pi) < Real.pi / M := by
    have : Real.pi / M < Real.pi := by
      rw [div_lt_iff₀ hMpos]
      nlinarith [hpi, hM3]
    nlinarith
  have hx2 : Real.pi / M < 2 * Real.pi := by
    have h1 : Real.pi / M ≤ Real.pi / 3 := by
      exact div_le_div_of_nonneg_left (le_of_lt hpi) (by norm_num) (by exact_mod_cast hM)
    have h2 : Real.pi / 3 < 2 * Real.pi := by nlinarith
    linarith
  rcases lt_or_eq_of_le (Real.cos_le_one (Real.pi / M)) with h | h
  · exact h
  · exfalso
    have hzero : Real.pi / M = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hx1 hx2).mp h
    linarith [hxpos]

/-- For `0 < c < 1` and positive `w` and `M`, the stated logarithmic lower bound on `m` implies
`M * c ^ m ≤ w / 2` [JanzingWocjan2006]. -/
theorem clock_tail_polynomial_gap {M m : ℕ} (c w : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hw : 0 < w) (hM : 0 < M)
    (hbig : Real.log (2 * (M : ℝ) / w) ≤ (m : ℝ) * (-Real.log c)) :
    (M : ℝ) * c ^ m ≤ w / 2 := by
  have hlogc : Real.log c < 0 := Real.log_neg hc0 hc1
  have hpos : 0 < 2 * (M : ℝ) / w := by positivity
  have hkey : (m : ℝ) * Real.log c ≤ -Real.log (2 * (M : ℝ) / w) := by
    nlinarith
  have hexp : c ^ m = Real.exp ((m : ℝ) * Real.log c) := by
    conv_lhs => rw [← Real.exp_log hc0]
    rw [← Real.exp_nat_mul (Real.log c) m]
  rw [hexp]
  have hle : Real.exp ((m : ℝ) * Real.log c) ≤
      Real.exp (-Real.log (2 * (M : ℝ) / w)) :=
    Real.exp_le_exp.mpr hkey
  have hrhs : Real.exp (-Real.log (2 * (M : ℝ) / w)) = w / (2 * (M : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
  rw [hrhs] at hle
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hval : (M : ℝ) * (w / (2 * (M : ℝ))) = w / 2 := by
    field_simp
  calc (M : ℝ) * Real.exp ((m : ℝ) * Real.log c)
      ≤ (M : ℝ) * (w / (2 * (M : ℝ))) :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hMpos)
    _ = w / 2 := hval

/-- For `0 ≤ p ≤ 1`, a distinguished value one and the stated bounds on the other values and
moment order imply `p - w / 2 ≤ p * ∑ l, x l ^ m` [JanzingWocjan2006]. -/
theorem clock_endpoint_gap {M : ℕ} [NeZero M] (x : Fin M → ℝ) (c w p : ℝ) (m : ℕ)
    (hc0 : 0 < c) (hc1 : c < 1) (hw : 0 < w) (hM : 0 < M)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx0 : x 0 = 1)
    (hx : ∀ l, l ≠ 0 → |x l| ≤ c)
    (hbig : Real.log (2 * (M : ℝ) / w) ≤ (m : ℝ) * (-Real.log c)) :
    p - w / 2 ≤ p * (∑ l, x l ^ m) := by
  have htail := clock_tail_bound x c m (le_of_lt hc0) hx
  have hgap := clock_tail_polynomial_gap c w hc0 hc1 hw hM hbig
  have hMle : ((M - 1 : ℕ) : ℝ) * c ^ m ≤ w / 2 := by
    have hcast : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
      have : M - 1 ≤ M := Nat.sub_le M 1
      exact_mod_cast this
    have hcm : 0 ≤ c ^ m := pow_nonneg (le_of_lt hc0) m
    calc ((M - 1 : ℕ) : ℝ) * c ^ m ≤ (M : ℝ) * c ^ m :=
          mul_le_mul_of_nonneg_right hcast hcm
      _ ≤ w / 2 := hgap
  have htail2 : |∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), x l ^ m| ≤ w / 2 :=
    le_trans htail hMle
  have htail_ge : -(w / 2) ≤
      ∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), x l ^ m := by
    have := abs_le.mp htail2
    linarith
  have hsplit := clock_endpoint_extract x hx0 p m
  rw [hsplit]
  have hw2 : (0 : ℝ) ≤ w / 2 := le_of_lt (by positivity)
  have hmul : p * (-(w / 2)) ≤
      p * (∑ l ∈ ((Finset.univ : Finset (Fin M)) \ {0}), x l ^ m) :=
    mul_le_mul_of_nonneg_left htail_ge hp0
  have hpw : -(w / 2) ≤ p * (-(w / 2)) := by
    have h1 : p * (w / 2) ≤ 1 * (w / 2) := mul_le_mul_of_nonneg_right hp1 hw2
    nlinarith
  linarith

end Qatlib.Papers.BQPMixSparse06.SignedClock
