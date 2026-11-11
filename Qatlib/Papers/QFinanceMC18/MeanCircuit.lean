/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PhaseGeometry.AngleEncoding

/-!
# Error bounds for the phase-to-mean decoder

`corrected_decoder_bounds` combines the restricted trigonometric decoder estimate with its
global Lipschitz bound. `discounted_decoder_error` propagates phase error through an arbitrary
real scale and discount factor. The mathematical context is [RebentrostGuptBromley2018].

## Main statements

* `corrected_decoder_bounds`: Under the stated nonnegative-angle, closeness, guard, and
  error-range hypotheses, the decoder error satisfies both the cosine-difference bound and one
  quarter of the phase difference.
* `discounted_decoder_error`: Scaling and discounting the phase-to-mean decoder bounds its
  output error by `|discount * scale|` times one quarter of the phase difference.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

namespace Qatlib.Papers.QFinanceMC18.MeanCircuit
set_option autoImplicit false
open Qatlib.Foundations.PhaseGeometry.AngleEncoding

/-- Under the stated nonnegative-angle, closeness, guard, and error-range hypotheses, the
decoder error satisfies both the cosine-difference bound and one quarter of the phase
difference. See [RebentrostGuptBromley2018]. -/
theorem corrected_decoder_bounds {θhat θ ε : ℝ}
    (hθ : 0 ≤ θ) (hclose : |θhat-θ| ≤ ε) (h0 : 0 ≤ θhat)
    (hguard : θhat ≤ Real.pi - 2*ε) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |phaseMean θhat-phaseMean θ| ≤
      (1/2)*|Real.cos ((θhat+ε)/2)-Real.cos (θhat/2)| ∧
    |phaseMean θhat-phaseMean θ| ≤ |θhat-θ|/4 :=
  ⟨phaseMean_error_restricted hθ hclose h0 hguard hε0 hε1, phaseMean_lipschitz θhat θ⟩

/-- Scaling and discounting the phase-to-mean decoder bounds its output error by `|discount *
scale|` times one quarter of the phase difference. -/
theorem discounted_decoder_error (scale discount θhat θ : ℝ) :
    |discount * scale * phaseMean θhat - discount * scale * phaseMean θ| ≤
      |discount * scale| * (|θhat-θ|/4) := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (phaseMean_lipschitz θhat θ) (abs_nonneg _)

end Qatlib.Papers.QFinanceMC18.MeanCircuit
