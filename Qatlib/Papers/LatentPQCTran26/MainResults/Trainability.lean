/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.Overlap

/-!
# Trainability from gradient-rich coverage

`proposition13` turns a lower bound on the measure of `gradRichSet` into an integral lower
bound. It applies to any nonnegative integrable real function under a finite measure, with
nonnegative threshold and measurable superlevel set. See [TranEtAl2026] for the paper context.

## Main statements

* `proposition13`: If an integrable nonnegative function under a finite measure has a measurable
  superlevel set at nonnegative `c` with real measure at least `q`, then its integral is at
  least `c * q`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.Trainability

open Qatlib.Papers.LatentPQCTran26.MainResults.Overlap

/-- If an integrable nonnegative function under a finite measure has a measurable superlevel set
at nonnegative `c` with real measure at least `q`, then its integral is at least `c * q`
[TranEtAl2026]. -/
theorem proposition13
    {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) [IsFiniteMeasure μ]
    (F : Θ → ℝ) (c q : ℝ) (hc : 0 ≤ c)
    (hS : MeasurableSet (gradRichSet F c))
    (hF_int : Integrable F μ) (hF_nonneg : ∀ θ, 0 ≤ F θ)
    (hcover : q ≤ μ.real (gradRichSet F c)) :
    c * q ≤ ∫ θ, F θ ∂μ := by
  have hbase := integral_ge_mul_measure μ F c hS hF_int hF_nonneg
  have hcq : c * q ≤ c * μ.real (gradRichSet F c) :=
    mul_le_mul_of_nonneg_left hcover hc
  linarith [hbase, hcq]

end Qatlib.Papers.LatentPQCTran26.MainResults.Trainability
