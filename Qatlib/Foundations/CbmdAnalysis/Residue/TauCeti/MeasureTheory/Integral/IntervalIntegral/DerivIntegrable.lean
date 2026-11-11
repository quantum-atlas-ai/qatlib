/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Integrability of derivatives on compact intervals

Proves `ContDiffOn.intervalIntegrable_deriv`: continuous differentiability of order at least one
on an unordered closed interval yields interval integrability of the derivative.

This compact-interval regularity fact supports contour integration in the framework associated
with [WangEtAl2026].

## Main statements

* `ContDiffOn.intervalIntegrable_deriv`: A function continuously differentiable to order at
  least one on the unordered closed interval has an interval-integrable derivative.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open MeasureTheory Set
open scoped ContDiff

/-- A function continuously differentiable to order at least one on the unordered closed
interval has an interval-integrable derivative. -/
theorem ContDiffOn.intervalIntegrable_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {n : ℕ∞ω} (hf : ContDiffOn ℝ n f (uIcc a b)) (hn : 1 ≤ n) :
    IntervalIntegrable (deriv f) volume a b := by
  rcases eq_or_ne a b with rfl | hab
  · exact IntervalIntegrable.refl
  have hlt : min a b < max a b := min_lt_max.mpr hab
  rw [← Icc_min_max] at hf
  have hint : IntervalIntegrable (derivWithin f (Icc (min a b) (max a b))) volume a b :=
    ((hf.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) hn).mono
      Icc_min_max.symm.subset).intervalIntegrable
  rw [intervalIntegrable_iff] at hint ⊢
  refine hint.congr ?_
  rw [uIoc, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

end
end Qatlib.Foundations.CbmdAnalysis.Residue
