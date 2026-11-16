/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HeisenbergLim10.MainResults.AttainmentExample

@[expose] public section


/-! # The actual source example and its printed resource normalization

Fixed arXiv:1004.3944v3, Eqs.(8) and (11). The actual normalized two-component
example has propagated error one and resource one half at N=1, phi=pi/2.
These literal numbers do not obey the printed error-times-resource lower
bound one. The propagated formula is DeltaX/|dmean|; no unbiased estimator,
statistical MSE theorem or universal physical counterexample is asserted.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Papers.HeisenbergLim10.MainResults

namespace Qatlib.Papers.HeisenbergLim10.MainResults.SourceAudit

/-- A real nonsingular operating phase of the actual example. -/
def phasePoint : ℝ := Real.pi / 2

/-- The exact propagated error formula used by the fixed source. -/
def propagated : ℝ := meanSquaredError |Real.sin phasePoint| (-Real.sin phasePoint)

/-- The actual real resource expectation of the source's N=1 state. -/
def resource : ℝ := (numberSquaredExpectation 1 phasePoint).re

/-- The concrete source state is actually normalized. -/
theorem normalized : xSecondMoment phasePoint = 1 := xSecondMoment_eq _

/-- The chosen operating point satisfies the nonzero derivative premise. -/
theorem nonzeroSin : Real.sin phasePoint ≠ 0 := by simp [phasePoint]

/-- The actual nonsingular error propagation is one. -/
theorem propagatedEq : propagated = 1 := by
  simpa [propagated] using eq11_mean_squared_error 1 phasePoint (by decide) (by simpa using nonzeroSin)

/-- The actual resource value of the normalized state is one half. -/
theorem resourceEq : resource = 1/2 := by
  simp [resource, numberSquaredExpectation_eq]

/-- Literal Eq.(11) has error-times-resource one half, not the printed Eq.(8) value one. -/
theorem printedProduct : propagated * resource = 1/2 := by rw [propagatedEq, resourceEq]; norm_num

/-- The actual propagated values violate the printed scalar inequality under that identification. -/
theorem printedGap : propagated < 1 / resource := by rw [propagatedEq, resourceEq]; norm_num

end Qatlib.Papers.HeisenbergLim10.MainResults.SourceAudit
