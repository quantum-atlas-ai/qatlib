/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussLinking
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Banded writhe geometry: cutting the near-diagonal of the self Gauss kernel

[Kedia2018SuperfluidHelicity], Section II and Eq. (6),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The writhe of a closed curve is the Gauss linking integral of the curve with itself, whose
kernel is singular on the diagonal `s = t`. The paper regulates it by excising a band around
the diagonal before integrating. This module defines that band-regularized integral
`writheBand γ δ` on the parameter square `[0, 2π]²` and proves the geometric facts available
without any topology: for a curve contained in an affine plane the banded integral vanishes
identically for every band width (hence also in the limit as the band shrinks), and for a
nonpositive band width the cutoff is inactive.

Scope notes, stated honestly: the band here is measured by parameter difference on the
square, so the wrap-around diagonal (`s` near `0`, `t` near `2π`) of the closed curve is
not excised; the existence of the writhe limit `δ → 0⁺` for non-planar `C²` curves, its
relation to the average tangent crossing number, and the full diagonal analysis of the
near-singular kernel are not proved in this module. Singular vortex dynamics and
reconnection remain outside.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open MeasureTheory
open Filter

/-- The self Gauss kernel of a single curve at a parameter pair. -/
noncomputable def writheKernel (γ : ℝ → (Fin 3 → ℝ)) (s t : ℝ) : ℝ :=
  gaussKernel γ γ s t

/-- The band-regularized writhe integral: the self Gauss kernel integrated over the
parameter square with the near-diagonal band `|s - t| < δ` removed. -/
noncomputable def writheBand (γ : ℝ → (Fin 3 → ℝ)) (δ : ℝ) : ℝ :=
  ∫ p, if |p.1 - p.2| < δ then 0 else writheKernel γ p.1 p.2 ∂gaussMeasure

/-- The self kernel of a planar curve vanishes identically, including on the diagonal where
both the numerator triple product and the denominator degenerate. -/
theorem writheKernel_planar_eq_zero (γ : ℝ → (Fin 3 → ℝ)) (n : Fin 3 → ℝ) (hn : n ≠ 0)
    (c : ℝ) (hper : ∀ s, dot3 n (γ s) = c) (hc : ContDiff ℝ 1 γ) :
    ∀ s t, writheKernel γ s t = 0 := by
  intro s t
  have hnum : dot3 (cross3 (deriv γ s) (deriv γ t)) (γ s - γ t) = 0 :=
    dot3_cross3_eq_zero hn
      (dot3_deriv_eq_zero_of_planar hc hper s)
      (dot3_deriv_eq_zero_of_planar hc hper t)
      (by rw [dot3_sub, hper s, hper t]; ring)
  simp [writheKernel, gaussKernel, hnum]

/-- The banded writhe integral of a curve contained in an affine plane vanishes for every
band width: planarity kills the kernel before any regularization is needed. -/
theorem writheBand_coplanar_eq_zero (γ : ℝ → (Fin 3 → ℝ)) (n : Fin 3 → ℝ) (hn : n ≠ 0)
    (c : ℝ) (hper : ∀ s, dot3 n (γ s) = c) (hc : ContDiff ℝ 1 γ) (δ : ℝ) :
    writheBand γ δ = 0 := by
  have hzero := writheKernel_planar_eq_zero γ n hn c hper hc
  have hfun : (fun p : ℝ × ℝ => if |p.1 - p.2| < δ then 0 else writheKernel γ p.1 p.2)
      = fun _ => 0 := by
    funext p
    by_cases hlt : |p.1 - p.2| < δ
    · simp [hlt]
    · simp [hlt, hzero p.1 p.2]
  simp only [writheBand, hfun]
  simp

/-- Shrinking the band to zero collapses the banded writhe of a planar curve to zero: the
regularized integral is constantly zero, so the limit exists trivially. -/
theorem tendsto_writheBand_planar_nhds_zero (γ : ℝ → (Fin 3 → ℝ)) (n : Fin 3 → ℝ)
    (hn : n ≠ 0) (c : ℝ) (hper : ∀ s, dot3 n (γ s) = c) (hc : ContDiff ℝ 1 γ) :
    Tendsto (fun δ => writheBand γ δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hconst : (fun δ => writheBand γ δ) = fun _ => 0 :=
    funext fun δ => writheBand_coplanar_eq_zero γ n hn c hper hc δ
  rw [hconst]
  exact tendsto_const_nhds

/-- A nonpositive band width excises nothing: the indicator is everywhere false and the
banded integral agrees with the plain self Gauss integral. This records the convention that
only positive widths regularize. -/
theorem writheBand_of_nonpos (γ : ℝ → (Fin 3 → ℝ)) {δ : ℝ} (hδ : δ ≤ 0) :
    writheBand γ δ = gaussLinking γ γ := by
  have hband : ∀ p : ℝ × ℝ, ¬ |p.1 - p.2| < δ := by
    intro p hlt
    exact absurd ((abs_nonneg (p.1 - p.2)).trans_lt hlt) (not_lt.2 hδ)
  simp only [writheBand, writheKernel]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp [hband p]

/-! ### Shrinking the band -/

/-- The self Gauss kernel vanishes identically on the parameter diagonal, since both the
numerator triple product and the denominator degenerate and real division by zero yields
zero. -/
theorem writheKernel_diag_eq_zero (γ : ℝ → (Fin 3 → ℝ)) (s : ℝ) :
    writheKernel γ s s = 0 := by
  simp [writheKernel, gaussKernel, dot3, sub_self]

/-- Band-shrink limit: if the self Gauss kernel is integrable over the parameter square
— true for `C²` curves because the numerator vanishes to second order at the diagonal, a
bound not reproved here — then the banded writhe integral converges, as the band width
shrinks to `0⁺`, to the full self Gauss integral. This is the regularization limit in the
sense of dominated convergence, with the kernel's absolute value as dominator. -/
theorem tendsto_writheBand_nhds_selfKernel (γ : ℝ → (Fin 3 → ℝ))
    (hint : Integrable (fun p : ℝ × ℝ => writheKernel γ p.1 p.2) gaussMeasure) :
    Tendsto (fun δ => writheBand γ δ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ p, writheKernel γ p.1 p.2 ∂gaussMeasure)) := by
  refine tendsto_of_seq_tendsto fun seq hseq => ?_
  have hpos : ∀ᶠ k in atTop, 0 < seq k := hseq.eventually self_mem_nhdsWithin
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun p : ℝ × ℝ => if |p.1 - p.2| < seq k then 0 else writheKernel γ p.1 p.2)
      gaussMeasure := by
    intro k
    have hind : (fun p : ℝ × ℝ => if |p.1 - p.2| < seq k then 0 else writheKernel γ p.1 p.2)
        = Set.indicator {p : ℝ × ℝ | seq k ≤ |p.1 - p.2|}
            (fun p => writheKernel γ p.1 p.2) := by
      funext p
      by_cases h : |p.1 - p.2| < seq k
      · simp [Set.indicator, h]
      · simp [Set.indicator, h, le_of_not_gt h]
    rw [hind]
    have hm : Measurable fun p : ℝ × ℝ => |p.1 - p.2| :=
      ((continuous_fst.sub continuous_snd).abs).measurable
    exact hint.aestronglyMeasurable.indicator (measurableSet_le measurable_const hm)
  have hbound : ∀ k : ℕ, ∀ᵐ p : ℝ × ℝ ∂gaussMeasure,
      ‖(if |p.1 - p.2| < seq k then 0 else writheKernel γ p.1 p.2)‖
        ≤ |writheKernel γ p.1 p.2| :=
    fun k => Filter.Eventually.of_forall fun p => by
      by_cases h : |p.1 - p.2| < seq k <;> simp [h]
  have hlim : ∀ p : ℝ × ℝ, Tendsto
      (fun k : ℕ => if |p.1 - p.2| < seq k then 0 else writheKernel γ p.1 p.2) atTop
      (nhds (writheKernel γ p.1 p.2)) := by
    intro p
    have hEv : (fun k : ℕ => if |p.1 - p.2| < seq k then 0 else writheKernel γ p.1 p.2)
        =ᶠ[atTop] fun _ : ℕ => writheKernel γ p.1 p.2 := by
      by_cases hd : p.1 - p.2 = 0
      · filter_upwards [hpos] with k hk
        have hd2 : |p.1 - p.2| = 0 := by rw [hd, abs_zero]
        have hK : writheKernel γ p.1 p.2 = 0 := by
          have hp : p.1 = p.2 := sub_eq_zero.mp hd
          rw [hp]; exact writheKernel_diag_eq_zero γ p.2
        rw [hd2]
        simp only [hk, ite_true, hK]
      · have hIioEv : ∀ᶠ y in nhdsWithin 0 (Set.Ioi 0), y ∈ Set.Iio |p.1 - p.2| :=
          eventually_nhdsWithin_of_eventually_nhds
            (show ∀ᶠ y in nhds 0, y ∈ Set.Iio |p.1 - p.2| by
              rw [Filter.eventually_iff, Set.ofPred_mem_eq]
              exact Iio_mem_nhds (abs_pos.mpr hd))
        filter_upwards [hseq.eventually hIioEv] with k hk
        simp [lt_asymm (Set.mem_Iio.mp hk)]
    exact Tendsto.congr' hEv.symm tendsto_const_nhds
  exact tendsto_integral_of_dominated_convergence
    (fun p => |writheKernel γ p.1 p.2|) hmeas hint.abs hbound
    (Filter.Eventually.of_forall hlim)

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
