/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 6.10: the supervised-clustering scalar identity and its tensor norms

Source: arXiv:1910.06151v4 (fixed version), Section 6.3 (supervised clustering), Problem 6.9 and
Corollary 6.10.

The paper reduces the objective `(wM)(wM)ᵀ` to a single inner product of two flattened
three-index tensors. With `m k := ‖M(k, ·)‖` the vector of row norms of `M : ℝ^{n×d}` and
`w : ℝ^n`, it sets

```
u_{i,j,k} = M(i,j) · m(k)
v_{i,j,k} = w(i) w(k) M(k,j) / m(k)
```

and claims `‖u‖ = ‖M‖_F²`, `‖v‖ = ‖w‖²`, so that estimating `⟨u, v⟩` to additive error `ε`
with probability `≥ 1 - δ` costs `O(‖M‖_F⁴ ‖w‖⁴ ε⁻² log(1/δ))` samples.

The printed `v` writes `M(j,k)` while `j` runs over `[d]`; for an `n × d` matrix the row that
carries the normalizing norm `m(k)` must be row `k`, so the formula is read as `M(k,j)` with
`j ∈ [d]`. That is the only reading under which the printed norm claims below hold when `n ≠ d`.

This file proves the algebraic content that the sampling step relies on:

* `tensor_inner_eq` — the contraction is the diagonal (trace) part of the objective,
  `⟨u, v⟩ = ∑_j (∑_i w(i) M(i,j))²`; the printed proof contains a matching scalar identity,
  and the vector of column sums is exactly `wM`;
* `tensorU_norm_sq` / `tensorV_norm_sq` — the printed norm claims `‖u‖² = ‖M‖_F⁴`,
  `‖v‖² = ‖w‖⁴` (with `m(k) > 0`, the zero-row guard);
* `tensor_sample_cost` — substituting the norms in the Lemma 4.12 sample count gives
  `‖M‖_F⁴‖w‖⁴ε⁻²log(1/δ)`, the paper's cost.

Not covered here: the actual `SQ(u)` construction (sampling `i` by `m`, `j` by `M(i,·)`, `k` by
`m`, and answering `u_{i,j,k} = M(i,j)m(k)`), the point-query access to `v`, the Lemma 4.12
estimator and its failure probability, and the full `d × d` matrix output rather than its
diagonal contraction.
-/

set_option autoImplicit false

namespace Qatlib.Papers.LowRankMatrix19.ClusterEstimate

open scoped BigOperators

noncomputable section

/-- The row-norm vector `m` of Definition 3.7: `m k = ‖M(k, ·)‖`. -/
noncomputable def rowNorm {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (k : Fin n) : ℝ :=
  Real.sqrt (∑ j, M k j ^ 2)

/-- The first flattened tensor `u = M ⊗ m` of Corollary 6.10's proof. -/
noncomputable def tensorU {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ)
    (i : Fin n) (j : Fin d) (k : Fin n) : ℝ :=
  M i j * rowNorm M k

/-- The second flattened tensor `v` of Corollary 6.10's proof, with `M(k, ·)` the row that
carries the normalizing row norm. -/
noncomputable def tensorV {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (i : Fin n) (j : Fin d) (k : Fin n) : ℝ :=
  w i * w k * M k j / rowNorm M k

/-- The `j`-th entry of `wM`: the column sum of `M` against the weight vector `w`. -/
noncomputable def rowMeans {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (j : Fin d) : ℝ :=
  ∑ i, w i * M i j

/-- The squared row norm is the sum of the squared row entries. -/
theorem rowNorm_sq {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (k : Fin n) :
    rowNorm M k ^ 2 = ∑ j, M k j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (M k j)))

/-- **Scalar identity of Corollary 6.10.** The contraction of the two printed flattenings is
`∑_j (wM)_j²`, the diagonal sum of `(wM)(wM)ᵀ`; the row norms cancel exactly. Here `M k j` is
the `j`-th entry of row `k`, as required by the printed norm claims. -/
theorem tensor_inner_eq {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hm : ∀ k, 0 < rowNorm M k) :
    (∑ i, ∑ j, ∑ k, tensorU M i j k * tensorV M w i j k)
      = ∑ j, rowMeans M w j ^ 2 := by
  have hterm : ∀ (i : Fin n) (j : Fin d) (k : Fin n),
      tensorU M i j k * tensorV M w i j k = (w i * M i j) * (w k * M k j) := by
    intro i j k
    unfold tensorU tensorV
    have hk : rowNorm M k ≠ 0 := ne_of_gt (hm k)
    field_simp
  simp only [hterm, rowMeans]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sq, ← Finset.sum_mul_sum]

/-- Factoring a sum of rank-one terms: `∑_i ∑_j ∑_k A_ij B_k = (∑_i ∑_j A_ij)(∑_k B_k)`. -/
theorem sum_sum_mul_sum_const {n d : ℕ} (A : Fin n → Fin d → ℝ) (B : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, A i j * B k) = (∑ i, ∑ j, A i j) * (∑ k, B k) := by
  calc (∑ i, ∑ j, ∑ k, A i j * B k)
      = ∑ i, ∑ j, A i j * (∑ k, B k) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [Finset.mul_sum]
    _ = ∑ i, (∑ j, A i j) * (∑ k, B k) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
    _ = (∑ i, ∑ j, A i j) * (∑ k, B k) := by
        rw [Finset.sum_mul]

/-- The printed norm claim `‖u‖² = ‖M‖_F⁴`. -/
theorem tensorU_norm_sq {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) :
    (∑ i, ∑ j, ∑ k, tensorU M i j k ^ 2)
      = (∑ i, ∑ j, M i j ^ 2) ^ 2 := by
  have hterm : ∀ (i : Fin n) (j : Fin d) (k : Fin n),
      tensorU M i j k ^ 2 = M i j ^ 2 * (rowNorm M k) ^ 2 := by
    intro i j k
    unfold tensorU
    ring
  simp only [hterm, rowNorm_sq]
  rw [sum_sum_mul_sum_const (fun i j => M i j ^ 2) (fun k => ∑ j, M k j ^ 2)]
  have hTS : (∑ k, ∑ j, M k j ^ 2) = (∑ i, ∑ j, M i j ^ 2) := rfl
  rw [hTS]
  ring

/-- The printed norm claim `‖v‖² = ‖w‖⁴`. -/
theorem tensorV_norm_sq {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hm : ∀ k, 0 < rowNorm M k) :
    (∑ i, ∑ j, ∑ k, tensorV M w i j k ^ 2)
      = (∑ i, w i ^ 2) ^ 2 := by
  have hterm : ∀ (i : Fin n) (j : Fin d) (k : Fin n),
      tensorV M w i j k ^ 2 = w i ^ 2 * (w k ^ 2 * (M k j ^ 2 / (rowNorm M k) ^ 2)) := by
    intro i j k
    unfold tensorV
    have hk : rowNorm M k ≠ 0 := ne_of_gt (hm k)
    field_simp
  simp only [hterm]
  have hswap : ∀ i : Fin n,
      (∑ j, ∑ k, w i ^ 2 * (w k ^ 2 * (M k j ^ 2 / (rowNorm M k) ^ 2)))
        = ∑ k, ∑ j, w i ^ 2 * (w k ^ 2 * (M k j ^ 2 / (rowNorm M k) ^ 2)) := by
    intro i
    rw [Finset.sum_comm]
  have hrow : ∀ k : Fin n, (∑ j, M k j ^ 2 / (rowNorm M k) ^ 2) = 1 := by
    intro k
    rw [← Finset.sum_div, ← rowNorm_sq M k]
    exact div_self (pow_ne_zero 2 (ne_of_gt (hm k)))
  have hinner : ∀ (i k : Fin n),
      (∑ j, w i ^ 2 * (w k ^ 2 * (M k j ^ 2 / (rowNorm M k) ^ 2)))
        = w i ^ 2 * w k ^ 2 := by
    intro i k
    have hfac : ∀ j : Fin d,
        w i ^ 2 * (w k ^ 2 * (M k j ^ 2 / (rowNorm M k) ^ 2))
          = (w i ^ 2 * w k ^ 2) * (M k j ^ 2 / (rowNorm M k) ^ 2) := by
      intro j; ring
    simp only [hfac]
    rw [← Finset.mul_sum, hrow k, mul_one]
  simp only [hswap, hinner]
  rw [← Finset.sum_mul_sum]
  ring

/-- Corollary 6.10's sample count after substituting the tensor norms:
`‖u‖²‖v‖²ε⁻²log(1/δ) = ‖M‖_F⁴‖w‖⁴ε⁻²log(1/δ)`. -/
theorem tensor_sample_cost {Mf wnorm eps delta : ℝ} (heps : eps ≠ 0) :
    (Mf ^ 2) ^ 2 * (wnorm ^ 2) ^ 2 / eps ^ 2 * Real.log (1 / delta)
      = Mf ^ 4 * wnorm ^ 4 / eps ^ 2 * Real.log (1 / delta) := by
  field_simp

end

end Qatlib.Papers.LowRankMatrix19.ClusterEstimate
