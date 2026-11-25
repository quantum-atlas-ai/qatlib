/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Qatlib.Papers.QuantumSearch05.MainResults.UncertaintyLaw
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Mean failure under a uniform marked fraction

Computes the mean of the two failure laws from [Grover2005], Section 5, using the uniform
density 4 on the interval from 3/4 to 1.

## References

* [Grover, 2005][Grover2005], [arXiv:quant-ph/0503205v1](https://arxiv.org/abs/quant-ph/0503205v1)
-/

set_option autoImplicit false

open scoped Interval
open Qatlib.Papers.QuantumSearch05.MainResults

namespace Qatlib.Papers.QuantumSearch05.MainResults

/-- The mean of the classical two-pick failure law for a uniform marked fraction on
`[3 / 4, 1]` is `1 / 48`. -/
theorem classical_two_pick_uniform_mean :
    (4 : ℝ) * (∫ f in (3 / 4 : ℝ)..1, classicalTwoPickFailure f) = 1 / 48 := by
  unfold classicalTwoPickFailure
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) 1,
    integral_pow]
  norm_num

/-- The mean of the fixed-point phase-shift failure law for a uniform marked fraction on
`[3 / 4, 1]` is `1 / 256`. -/
theorem phase_shift_uniform_mean :
    (4 : ℝ) * (∫ f in (3 / 4 : ℝ)..1, phaseShiftFailure f) = 1 / 256 := by
  unfold phaseShiftFailure
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 3) 1,
    integral_pow]
  norm_num

end Qatlib.Papers.QuantumSearch05.MainResults
