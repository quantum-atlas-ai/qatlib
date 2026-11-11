/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# RobustQLearn14.MainResults.ClassicalNoiseless — classical learning from ideal queries

Fixed source: Cross--Smith--Smolin, *Quantum learning robust to noise*,
arXiv:1407.5088v1 (18 Jul 2014).

Claim `c002` (Sec. III, Eq. (5), pp. 2--3): the classical oracle returns
`(x, f_a(x))` with `x` uniform on `{0,1}^n`.  Since `f_a(x) = <a,x>` is linear,
`n` examples suffice to recover `a` exactly with constant probability; the
probability that `n` examples are linearly independent is

  `∏_{j=0}^{n-1} (1 - 2^{j-n})`,                                    (5)

which is greater than `1/4` for every `n > 1`.  Recovery is then Gaussian
elimination.

A uniform random sequence of `n` examples from `{0,1}^n` is exactly a uniform
random `n × n` matrix over `GF(2)`; the examples are linearly independent iff
the matrix is invertible.  So the probability is `|GL_n(GF(2))| / 2^{n²}`, and
Mathlib's `Matrix.card_GL_field` computes the numerator.  This file records
Eq. (5) and the `1/4` bound; the Gaussian-elimination recovery step is the
standard linear-algebra fact that an invertible system over `GF(2)` has a
unique solution, and is not restated here.
-/

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.RobustQLearn14.MainResults

noncomputable section

/-! ## The linear-independence probability -/

/-- `c002` / Eq. (5): probability that `n` uniformly random examples from
`{0,1}^n` are linearly independent, expressed as the fraction of invertible
`n × n` matrices over `GF(2)`.  Source: arXiv:1407.5088v1, Sec. III, p. 2. -/
def independentExampleProb (n : ℕ) : ℝ :=
  (Nat.card (GL (Fin n) (ZMod 2)) : ℝ) / (2 : ℝ) ^ (n * n)

/-- Reusable finite-product inequality: over a finite set, if every
`a i ∈ [0,1]` then `∏ (1 - a i) ≥ 1 - ∑ a i`.  This is the elementary
"probability of the complement is at least one minus the sum of the
probabilities" bound used to lower-bound the product in Eq. (5). -/
theorem prod_one_sub_ge_one_sub_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.prod_insert hx]
      have hsum_nonneg : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha0 i
      have hkey : 1 - (a x + ∑ i ∈ s, a i)
          ≤ (1 - a x) * (1 - ∑ i ∈ s, a i) := by
        nlinarith [ha0 x, hsum_nonneg, mul_nonneg (ha0 x) hsum_nonneg]
      have hmul : (1 - a x) * (1 - ∑ i ∈ s, a i)
          ≤ (1 - a x) * ∏ i ∈ s, (1 - a i) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [ha1 x (Finset.mem_insert_self x s)])
        exact ih (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
      linarith

/-- `c002` / Eq. (5), exact form: the linear-independence probability equals
`∏_{i : Fin n} (1 - 2^{i} / 2^{n}) = ∏_{j=0}^{n-1} (1 - 2^{j-n})`.
Source: arXiv:1407.5088v1, Sec. III, Eq. (5), p. 2.  Uses
`Matrix.card_GL_field` (Mathlib, `LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean`). -/
theorem independentExampleProb_eq_prod (n : ℕ) :
    independentExampleProb n
      = ∏ i : Fin n, (1 - (2 : ℝ) ^ (i : ℕ) / (2 : ℝ) ^ n) := by
  unfold independentExampleProb
  have hcard : (Nat.card (GL (Fin n) (ZMod 2)) : ℝ)
      = ∏ i : Fin n, ((2 : ℝ) ^ n - (2 : ℝ) ^ (i : ℕ)) := by
    have hnat : Nat.card (GL (Fin n) (ZMod 2))
        = ∏ i : Fin n, ((2 : ℕ) ^ n - (2 : ℕ) ^ (i : ℕ)) := by
      simpa using Matrix.card_GL_field (𝔽 := ZMod 2) n
    rw [hnat, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    have hi : (i : ℕ) ≤ n := Nat.le_of_lt i.isLt
    have hle : (2 : ℕ) ^ (i : ℕ) ≤ (2 : ℕ) ^ n :=
      Nat.pow_le_pow_right (by norm_num) hi
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow]
    norm_num
  rw [hcard]
  have hden : (2 : ℝ) ^ (n * n) = ∏ _i : Fin n, (2 : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hden, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  field_simp

/-- `c002` / Eq. (5), bound: for `n > 1` the probability that `n` examples are
linearly independent is strictly greater than `1/4`.  Source:
arXiv:1407.5088v1, Sec. III, p. 3 ("which is greater than 1/4 for any n > 1"). -/
theorem independentExampleProb_gt_quarter (n : ℕ) (hn : 1 < n) :
    (1 / 4 : ℝ) < independentExampleProb n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 0 < m := by omega
  have hrange : (∏ i : Fin (m + 1), (1 - (2 : ℝ) ^ (i : ℕ) / (2 : ℝ) ^ (m + 1)))
      = ∏ i ∈ Finset.range (m + 1), (1 - (2 : ℝ) ^ i / (2 : ℝ) ^ (m + 1)) := by
    rw [Finset.prod_range]
  rw [independentExampleProb_eq_prod, hrange, Finset.prod_range_succ]
  set b : ℕ → ℝ := fun i => (2 : ℝ) ^ i / (2 : ℝ) ^ (m + 1) with hb
  have hb0 : ∀ i, 0 ≤ b i := fun i => by positivity
  have hb1 : ∀ i ∈ Finset.range m, b i ≤ 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (m + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact div_le_one (by positivity) |>.mpr hle
  have hlast : b m = 1 / 2 := by
    rw [hb]
    have hpow : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by
      rw [pow_succ]
    rw [hpow]
    field_simp
  have hgeom : (∑ i ∈ Finset.range m, (2 : ℝ) ^ i) = (2 : ℝ) ^ m - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [h21, div_one]
  have hsum_lt : (∑ i ∈ Finset.range m, b i) < 1 / 2 := by
    have hsum_b : (∑ i ∈ Finset.range m, b i)
        = (∑ i ∈ Finset.range m, (2 : ℝ) ^ i) / (2 : ℝ) ^ (m + 1) := by
      rw [hb]
      rw [div_eq_mul_inv, Finset.sum_mul]
      simp only [div_eq_mul_inv]
    rw [hsum_b, hgeom]
    have hpow : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := pow_succ _ _
    rw [hpow]
    have h2m : 0 < (2 : ℝ) ^ m := by positivity
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hprod_ge : 1 - (∑ i ∈ Finset.range m, b i)
      ≤ ∏ i ∈ Finset.range m, (1 - b i) :=
    prod_one_sub_ge_one_sub_sum _ _ hb0 hb1
  have hprod_pos : (1 / 2 : ℝ) < ∏ i ∈ Finset.range m, (1 - b i) := by
    linarith
  change (1 / 4 : ℝ) < (∏ i ∈ Finset.range m, (1 - b i)) * (1 - b m)
  rw [hlast]
  nlinarith

/-- `c002` corollary: a single batch of `n > 1` classical queries succeeds with
probability greater than `1/4`, so a constant number of repetitions amplifies
the success probability, matching the paper's `log_{1/p}(1/δ)` remark
(arXiv:1407.5088v1, Sec. III, p. 3). -/
theorem classical_batch_success_gt_quarter (n : ℕ) (hn : 1 < n) :
    (1 / 4 : ℝ) < independentExampleProb n :=
  independentExampleProb_gt_quarter n hn

end

end Qatlib.Papers.RobustQLearn14.MainResults
