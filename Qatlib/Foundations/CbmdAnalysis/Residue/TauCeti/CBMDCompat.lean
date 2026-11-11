/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Open-interval congruence for interval integrals

Provides `intervalIntegrable_congr_uIoo`, `IntervalIntegrable.congr_uIoo`, and
`intervalIntegral.integral_congr_uIoo` for functions equal between the integration endpoints.
The statements use the ambient measure hypotheses to disregard endpoint values.

These compatibility lemmas support the contour integration development associated with
[WangEtAl2026].

## Main statements

* `intervalIntegrable_congr_uIoo`: Functions equal on the open interval between `a` and `b` have
  equivalent interval integrability under the ambient measure hypotheses.
* `intervalIntegral.integral_congr_uIoo`: Functions equal on the open interval between the
  endpoints have equal interval integrals under the ambient measure hypotheses.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open MeasureTheory Set
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : ℝ → E} {a b : ℝ} {μ : Measure ℝ} [NullSingletonClass μ]

omit [NormedSpace ℝ E] in

/-- Functions equal on the open interval between `a` and `b` have equivalent interval
integrability under the ambient measure hypotheses. -/
theorem intervalIntegrable_congr_uIoo (h : EqOn f g (uIoo a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  apply intervalIntegrable_congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [μ.ae_ne (max a b)] with t ht hmem
  exact h ⟨hmem.1, hmem.2.lt_of_ne ht⟩

omit [NormedSpace ℝ E] in

/-- Transfers interval integrability to a function equal on the open interval between the
endpoints. -/
theorem IntervalIntegrable.congr_uIoo (hf : IntervalIntegrable f μ a b)
    (h : EqOn f g (uIoo a b)) : IntervalIntegrable g μ a b :=
  (intervalIntegrable_congr_uIoo h).mp hf

/-- Functions equal on the open interval between the endpoints have equal interval integrals
under the ambient measure hypotheses. -/
theorem intervalIntegral.integral_congr_uIoo (h : EqOn f g (uIoo a b)) :
    (∫ t in a..b, f t ∂μ) = ∫ t in a..b, g t ∂μ := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [μ.ae_ne (max a b)] with t ht hmem
  exact h ⟨hmem.1, hmem.2.lt_of_ne ht⟩

end
end Qatlib.Foundations.CbmdAnalysis.Residue
