/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShorElliptic03.MainResults.FidelityAndSuccess

@[expose] public section

/-!
# Conditional joint readout bound

Combines the two one-register bounds of [ProosZalka2003], Appendix A, for the
product readout at a fixed Fourier peak. The hypotheses relate the actual bad
masses to the finite tail sums and compare the discrete cutoff with the real
rounding window.
-/

set_option autoImplicit false

open Qatlib.Papers.ShorElliptic03.MainResults.FidelityAndSuccess

namespace Qatlib.Papers.ShorElliptic03.MainResults

/-- The positive and negative peak weights strictly beyond `Δ` and through `K`. -/
noncomputable def truncatedPeakTail (N K Δ : ℕ) (δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico (Δ + 1) (K + 1), (peakWeight N δ (j : ℤ) + peakWeight N δ (-(j : ℤ)))

/-- The failure weight of two independent finite readouts is bounded by the sum of the
individual failure weights. -/
theorem independent_readout_failure_le_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (px : ι → ℝ) (py : κ → ℝ) (Gx : Finset ι) (Gy : Finset κ)
    (hpx : ∀ x, 0 ≤ px x) (hpy : ∀ y, 0 ≤ py y)
    (hx : ∑ x, px x = 1) (hy : ∑ y, py y = 1) :
    1 - (∑ x ∈ Gx, ∑ y ∈ Gy, px x * py y) ≤ (1 - ∑ x ∈ Gx, px x) + (1 - ∑ y ∈ Gy, py y) := by
  have hGx : ∑ x ∈ Gx, px x ≤ 1 := by
    rw [← hx]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Gx) (fun x _ _ => hpx x)
  have hGy : ∑ y ∈ Gy, py y ≤ 1 := by
    rw [← hy]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Gy) (fun y _ _ => hpy y)
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr hGx) (sub_nonneg.mpr hGy)]

/-- At a fixed peak, the two truncated tail bounds imply the joint readout lower bound
under the stated cutoff and bad-mass comparisons. See [ProosZalka2003], Appendix A. -/
theorem dlog_success_le_joint_product_readout {ι κ : Type*} [Fintype ι] [Fintype κ]
    (px : ι → ℝ) (py : κ → ℝ) (Gx : Finset ι) (Gy : Finset κ)
    (hpx : ∀ x, 0 ≤ px x) (hpy : ∀ y, 0 ≤ py y)
    (hx : ∑ x, px x = 1) (hy : ∑ y, py y = 1)
    (N q K Δ : ℕ) (δx δy : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hK : 2 * (K + 1) ≤ N) (hΔ : 1 ≤ Δ) (hΔK : Δ ≤ K)
    (hδx0 : 0 ≤ δx) (hδx1 : δx < 1) (hδy0 : 0 ≤ δy) (hδy1 : δy < 1)
    (hwindow : readoutWindow N q ≤ (Δ : ℝ))
    (hTailX : 1 - ∑ x ∈ Gx, px x ≤ truncatedPeakTail N K Δ δx)
    (hTailY : 1 - ∑ y ∈ Gy, py y ≤ truncatedPeakTail N K Δ δy) :
    dlogSuccessLowerBound N q ≤ ∑ x ∈ Gx, ∑ y ∈ Gy, px x * py y := by
  have hw : 0 < readoutWindow N q := by
    unfold readoutWindow
    have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    positivity
  have hscale : 2 / (Δ : ℝ) ≤ 2 / readoutWindow N q :=
    div_le_div_of_nonneg_left (by norm_num) hw hwindow
  have hTailX' : truncatedPeakTail N K Δ δx ≤ 2 / (Δ : ℝ) :=
    peak_tail_bound N K δx Δ (hΔ.trans hΔK) hK hδx0 hδx1 hΔ hΔK
  have hTailY' : truncatedPeakTail N K Δ δy ≤ 2 / (Δ : ℝ) :=
    peak_tail_bound N K δy Δ (hΔ.trans hΔK) hK hδy0 hδy1 hΔ hΔK
  calc
    dlogSuccessLowerBound N q ≤ 1 - ((1 - ∑ x ∈ Gx, px x) + (1 - ∑ y ∈ Gy, py y)) :=
      dlog_success_of_register_tails N q hN hq _ _
        (hTailX.trans (hTailX'.trans hscale)) (hTailY.trans (hTailY'.trans hscale))
    _ ≤ ∑ x ∈ Gx, ∑ y ∈ Gy, px x * py y := by
      linarith [independent_readout_failure_le_sum px py Gx Gy hpx hpy hx hy]

end Qatlib.Papers.ShorElliptic03.MainResults
