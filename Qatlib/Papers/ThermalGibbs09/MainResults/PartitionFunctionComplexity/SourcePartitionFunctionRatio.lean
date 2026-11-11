/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalGibbs09.MainResults.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalGibbs09 — sequential partition-function ratio estimation (p. 4)

Poulin--Wocjan, fixed arXiv:0905.2199, p. 4 (the paragraph after eq. (7),
describing the estimate of the ratios `F_k` and the evaluation of `Z(β)`).

This file formalises the *correctness* half of claim `c002`: the paper
evaluates the partition function as a telescoping product of ratios
`F_k = Z(β_{k+1}) / Z(β_k)` and argues that, because each ratio is estimated
by quantum counting to relative accuracy `ε / ℓ`, the product inherits a
relative accuracy `ε` (using `1 + x ≤ eˣ`).  We prove:

* `prod_ratio_telescope`: the ratio factors telescope,
  `∏_{k<n} Z(β_{k+1})/Z(β_k) = Z(β_n)/Z(β_0)` — the identity behind
  `Z(β) = Z(β_0) ∏ F_k` with `Z(β_0) = D`;
* `prod_relative_error_bound`: if every factor carries relative error at most
  `δ`, the product carries relative error at most `(1+δ)^n - 1`;
* `prod_estimate_error` / `ratio_product_error_exp`: the same statement in the
  partition-function normalisation, with the `(1+δ)^n` factor controlled by
  `e^{nδ}` (the paper's `1 + x ≤ eˣ` step).

## Boundary

The runtime ledger `O(sqrt(D/Z(β)) · β⁵ E_max⁵ / ε²)` and the quantum-counting
circuit that produces each ratio estimate are *not* rebuilt here; this file
covers only the finite arithmetic of the telescoping product and its error
propagation, which is what the paper invokes after the counting subroutine.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionComplexity

open Qatlib.Papers.ThermalGibbs09.MainResults

/-- The telescoping identity behind the paper's ratio product: for a nowhere
zero real sequence `Z`, `∏_{k<n} Z(k+1)/Z(k) = Z(n)/Z(0)`.  With
`Z(k) = Z(β_k)` this is `Z(β) = Z(β_0) ∏_k F_k`, and `Z(β_0) = D`. -/
theorem prod_ratio_telescope (Z : ℕ → ℝ) (hZ : ∀ k, Z k ≠ 0) (n : ℕ) :
    (∏ k ∈ Finset.range n, Z (k + 1) / Z k) = Z n / Z 0 := by
  induction n with
  | zero => simpa using (div_self (hZ 0)).symm
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      have hm : Z m ≠ 0 := hZ m
      have h0 : Z 0 ≠ 0 := hZ 0
      field_simp

/-- `|1 + e| ≤ 1 + δ` whenever `|e| ≤ δ` and `δ ≥ 0`. -/
theorem abs_one_add_le {e δ : ℝ} (he : |e| ≤ δ) (hδ : 0 ≤ δ) :
    |1 + e| ≤ 1 + δ := by
  have h1 : |1 + e| ≤ |(1 : ℝ)| + |e| := abs_add_le _ _
  rw [abs_one] at h1
  linarith

/-- **Relative-error propagation through a product.** If every factor
`1 + e k` departs from `1` by at most `δ` in absolute value, then the product
of `n` factors departs from `1` by at most `(1+δ)^n - 1`.  This is the
finite-arithmetic content of the paper's statement that estimating `ℓ`
sequential ratios each to relative accuracy `ε/ℓ` gives a product of relative
accuracy `(1+ε/ℓ)^ℓ - 1 ≤ ε`. -/
theorem prod_relative_error_bound (e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ∀ k, |e k| ≤ δ) (n : ℕ) :
    |(∏ k ∈ Finset.range n, (1 + e k)) - 1| ≤ (1 + δ) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ]
      have hPabs : |(∏ k ∈ Finset.range m, (1 + e k))| ≤ (1 + δ) ^ m := by
        rw [Finset.abs_prod]
        calc (∏ k ∈ Finset.range m, |1 + e k|)
            ≤ ∏ k ∈ Finset.range m, (1 + δ) := by
              apply Finset.prod_le_prod₀
              · intro k _; exact abs_nonneg _
              · intro k _; exact abs_one_add_le (he k) hδ
          _ = (1 + δ) ^ m := by rw [Finset.prod_const, Finset.card_range]
      have key : (∏ k ∈ Finset.range m, (1 + e k)) * (1 + e m) - 1
          = ((∏ k ∈ Finset.range m, (1 + e k)) - 1)
            + (∏ k ∈ Finset.range m, (1 + e k)) * e m := by
        ring
      rw [key]
      calc |((∏ k ∈ Finset.range m, (1 + e k)) - 1)
              + (∏ k ∈ Finset.range m, (1 + e k)) * e m|
          ≤ |(∏ k ∈ Finset.range m, (1 + e k)) - 1|
              + |(∏ k ∈ Finset.range m, (1 + e k)) * e m| := abs_add_le _ _
        _ = |(∏ k ∈ Finset.range m, (1 + e k)) - 1|
              + |(∏ k ∈ Finset.range m, (1 + e k))| * |e m| := by rw [abs_mul]
        _ ≤ ((1 + δ) ^ m - 1) + (1 + δ) ^ m * δ := by
              have hmul : |(∏ k ∈ Finset.range m, (1 + e k))| * |e m|
                  ≤ (1 + δ) ^ m * δ :=
                mul_le_mul hPabs (he m) (abs_nonneg _) (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + δ) m)
              linarith [ih, hmul]
        _ = (1 + δ) ^ (m + 1) - 1 := by rw [pow_succ]; ring

/-- `(1 + δ)^n ≤ e^{nδ}` for `δ ≥ 0`, the paper's `1 + x ≤ eˣ` step in the
relative-error ledger. -/
theorem pow_one_add_le_exp (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    (1 + δ) ^ n ≤ Real.exp ((n : ℝ) * δ) := by
  have h := Real.prod_one_add_le_exp_sum (Finset.range n) (f := fun _ => δ) (fun _ => hδ)
  simpa [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul] using h

/-- **Product estimate error with relative per-factor accuracy.** If
`Fhat k = F k * (1 + e k)` with `F k ≥ 0` and `|e k| ≤ δ`, then the product
estimate deviates from the true product by at most `((1+δ)^n - 1)` times the
true product.  This is the exact normalisation in which the paper estimates
`Z(β) = Z(β_0) ∏ F_k`. -/
theorem prod_estimate_error (n : ℕ) (F e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : ∀ k, 0 ≤ F k) (he : ∀ k, |e k| ≤ δ) :
    |(∏ k ∈ Finset.range n, F k * (1 + e k))
        - (∏ k ∈ Finset.range n, F k)|
      ≤ ((1 + δ) ^ n - 1) * (∏ k ∈ Finset.range n, F k) := by
  rw [Finset.prod_mul_distrib]
  have hP := prod_relative_error_bound e δ hδ he n
  have hFnn : 0 ≤ ∏ k ∈ Finset.range n, F k :=
    Finset.prod_nonneg (fun k _ => hF k)
  have key : (∏ k ∈ Finset.range n, F k) * (∏ k ∈ Finset.range n, (1 + e k))
      - (∏ k ∈ Finset.range n, F k)
      = (∏ k ∈ Finset.range n, F k)
        * ((∏ k ∈ Finset.range n, (1 + e k)) - 1) := by
    ring
  rw [key, abs_mul, abs_of_nonneg hFnn]
  calc (∏ k ∈ Finset.range n, F k)
        * |(∏ k ∈ Finset.range n, (1 + e k)) - 1|
      ≤ (∏ k ∈ Finset.range n, F k) * ((1 + δ) ^ n - 1) :=
        mul_le_mul_of_nonneg_left hP hFnn
    _ = ((1 + δ) ^ n - 1) * (∏ k ∈ Finset.range n, F k) := by ring

/-- The partition-function error ledger: with each of `n` ratios known to
relative accuracy `δ`, the product estimate deviates from the true partition
function by at most `(e^{nδ} - 1)` times the true value.  This packages
`prod_estimate_error` with the exponential relaxation `(1+δ)^n ≤ e^{nδ}`. -/
theorem ratio_product_error_exp (n : ℕ) (F e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : ∀ k, 0 ≤ F k) (he : ∀ k, |e k| ≤ δ) :
    |(∏ k ∈ Finset.range n, F k * (1 + e k))
        - (∏ k ∈ Finset.range n, F k)|
      ≤ (Real.exp ((n : ℝ) * δ) - 1) * (∏ k ∈ Finset.range n, F k) := by
  have h1 := prod_estimate_error n F e δ hδ hF he
  have h2 := pow_one_add_le_exp δ hδ n
  have hFnn : 0 ≤ ∏ k ∈ Finset.range n, F k :=
    Finset.prod_nonneg (fun k _ => hF k)
  have hle : (1 + δ) ^ n - 1 ≤ Real.exp ((n : ℝ) * δ) - 1 := by linarith
  exact h1.trans (mul_le_mul_of_nonneg_right hle hFnn)

end Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionComplexity
