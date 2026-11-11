/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelParameters

/-!
# Finite integer sampling approximations

`integerSample` weights evaluations on the real lattice, and `integerLCUSum` forms a symmetric
finite sum. Contractivity on the real axis gives absolute summability and a uniform
exponentially small truncation estimate.

The module combines truncation with control of auxiliary residues to approximate the corrected
infinite series within `δ`. An assumed series identity then transfers this bound to `U (-i)`,
following the sampling construction of [WangEtAl2026].

## Main statements

* `integerSample_tail_norm_le`: bounds the finite-sum truncation error.
* `integerLCU_approximation_of_series_identity`: transfers the corrected-series bound to the
  target.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators

section Propagator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The evaluation of `U` at the real lattice point `k / a`, multiplied by `integerWeight m a (k
/ a)`. -/
noncomputable def integerSample (m : ℕ) (a : ℝ) (U : ℂ → E) (k : ℤ) : E :=
  integerWeight m a ((k : ℝ) / a) • U (((k : ℝ) / a : ℝ) : ℂ)

/-- The sum of the weighted integer samples with indices from `-K` to `K`. -/
noncomputable def integerLCUSum (m : ℕ) (a : ℝ) (K : ℕ) (U : ℂ → E) : E :=
  ∑ k ∈ Finset.Icc (-(K : ℤ)) K, integerSample m a U k

/-- If `a ≥ 1` and `U` has norm at most one on the real axis, the norms of its weighted integer
samples form a summable series. -/
theorem integerSample_norm_summable (m : ℕ) {a : ℝ} (ha : 1 ≤ a) (U : ℂ → E)
    (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1) : Summable (fun k : ℤ => ‖integerSample m a U k‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => ?_) (integerWeight_lattice_norm_summable m ha)
  rw [integerSample, norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hUreal _) (norm_nonneg _)

variable [CompleteSpace E]

/-- For `m ≥ 1`, `a ≥ 1`, and `K ≥ 2am`, real-axis contractivity bounds the error of the finite
LCU sum by `kernelTailConstant * exp (-2m)`. -/
theorem integerSample_tail_norm_le (m : ℕ) (hm : 1 ≤ m) {a : ℝ} (ha : 1 ≤ a)
    (K : ℕ) (hK : 2 * a * m ≤ K) (U : ℂ → E)
    (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1) :
    ‖(∑' k : ℤ, integerSample m a U k) - integerLCUSum m a K U‖ ≤
      kernelTailConstant * Real.exp (-2 * (m : ℝ)) := by
  have hsn := integerSample_norm_summable m ha U hUreal
  have hs := hsn.of_norm
  let s := Finset.Icc (-(K : ℤ)) K
  have hsplit := hs.sum_add_tsum_subtype_compl s
  have hiff (k : ℤ) : k ∉ s ↔ (K : ℤ) < |k| := by
    dsimp [s]
    simp only [Finset.mem_Icc, ← abs_le, not_le]
  let e := Equiv.subtypeEquivRight hiff
  have heq : (∑' k : {k : ℤ // k ∉ s}, integerSample m a U k.val) =
      ∑' k : {k : ℤ // (K : ℤ) < |k|}, integerSample m a U k.val := by
    exact e.tsum_eq (fun k => integerSample m a U k.val)
  have htailnorm := hsn.subtype (fun k => (K : ℤ) < |k|)
  have hwnorm := (integerWeight_lattice_norm_summable m ha).subtype (fun k => (K : ℤ) < |k|)
  calc
    _ = ‖∑' k : {k : ℤ // (K : ℤ) < |k|}, integerSample m a U k.val‖ := by
      rw [← heq, ← hsplit]
      change ‖(∑ k ∈ s, integerSample m a U k) +
        (∑' k : {k : ℤ // k ∉ s}, integerSample m a U k.val) -
        (∑ k ∈ s, integerSample m a U k)‖ = _
      simp only [add_sub_cancel_left]
    _ ≤ ∑' k : {k : ℤ // (K : ℤ) < |k|}, ‖integerSample m a U k.val‖ :=
      norm_tsum_le_tsum_norm htailnorm
    _ ≤ ∑' k : {k : ℤ // (K : ℤ) < |k|}, ‖integerWeight m a ((k.val : ℝ) / a)‖ := by
      apply Summable.tsum_le_tsum _ htailnorm hwnorm
      intro k
      change ‖integerSample m a U k.val‖ ≤ ‖integerWeight m a ((k.val : ℝ) / a)‖
      rw [integerSample, norm_smul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hUreal _) (norm_nonneg _)
    _ ≤ _ := integerWeight_tail_tsum_le m hm ha K hK

/-- For `0 < δ ≤ 1` and the stated real-axis and auxiliary growth bounds, the prescribed finite
LCU sum approximates the infinite sample sum minus the auxiliary correction within `δ`. -/
theorem integerLCU_series_error_le (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (U : ℂ → E) (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1)
    (hUtop : ‖U (2 * Complex.I)‖ ≤ Real.exp (2 * ρ))
    (hUrow : ∀ r ∈ Finset.Icc (-(kernelOrder (δ / 2) : ℤ)) (kernelOrder (δ / 2)),
      ‖U ((r : ℂ) + Complex.I)‖ ≤ Real.exp ρ) :
    let m := kernelOrder (δ / 2)
    let a := kernelSpacing ρ (δ / 2) m
    let K := kernelCutoff a (δ / 2)
    ‖((∑' k : ℤ, integerSample m a U k) - integerAuxiliaryCorrection m a U) -
      integerLCUSum m a K U‖ ≤ δ := by
  (try dsimp only)
  let m := kernelOrder (δ / 2)
  let a := kernelSpacing ρ (δ / 2) m
  have hδ2 : 0 < δ / 2 := by positivity
  have ha : 1 ≤ a := kernelSpacing_ge_one _ _ _
  have ht := integerSample_tail_norm_le m (kernelOrder_pos _) ha
    (kernelCutoff a (δ / 2)) (Nat.le_ceil _) U hUreal
  have ht' : ‖(∑' k : ℤ, integerSample m a U k) -
      integerLCUSum m a (kernelCutoff a (δ / 2)) U‖ ≤ δ / 2 :=
    ht.trans (kernelOrder_tail_budget hδ2)
  have haux : ‖integerAuxiliaryCorrection m a U‖ ≤ δ / 2 :=
    integerAuxiliary_chosen_le m ρ hδ2 (by linarith) U hUtop hUrow
  change ‖((∑' k : ℤ, integerSample m a U k) - integerAuxiliaryCorrection m a U) -
    integerLCUSum m a (kernelCutoff a (δ / 2)) U‖ ≤ δ
  rw [sub_right_comm]
  exact (norm_sub_le _ _).trans (by linarith)

/-- If the corrected infinite sample sum equals `U (-i)`, then the prescribed finite LCU sum
approximates `U (-i)` within `δ` under the stated norm bounds and `0 < δ ≤ 1`
[WangEtAl2026]. -/
theorem integerLCU_approximation_of_series_identity (ρ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (U : ℂ → E)
    (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1)
    (hUtop : ‖U (2 * Complex.I)‖ ≤ Real.exp (2 * ρ))
    (hUrow : ∀ r ∈ Finset.Icc (-(kernelOrder (δ / 2) : ℤ)) (kernelOrder (δ / 2)),
      ‖U ((r : ℂ) + Complex.I)‖ ≤ Real.exp ρ)
    (hseries : let m := kernelOrder (δ / 2)
      let a := kernelSpacing ρ (δ / 2) m
      U (-Complex.I) = (∑' k : ℤ, integerSample m a U k) - integerAuxiliaryCorrection m a U) :
    let m := kernelOrder (δ / 2)
    let a := kernelSpacing ρ (δ / 2) m
    ‖U (-Complex.I) - integerLCUSum m a (kernelCutoff a (δ / 2)) U‖ ≤ δ := by
  dsimp only at hseries ⊢
  rw [hseries]
  exact integerLCU_series_error_le ρ hδ hδ1 U hUreal hUtop hUrow

end Propagator
end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
