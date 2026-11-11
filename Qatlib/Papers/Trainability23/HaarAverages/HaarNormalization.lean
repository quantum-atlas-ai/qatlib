/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Complex scalar factors in Haar integrals

This module supplies `integral_const_mul_complex`, a scalar-linearity identity for complex
Bochner integrals used in Haar moment calculations. The statement applies to an arbitrary
measure. See [RudolphEtAl2024].

## Main statements

* `integral_const_mul_complex`: a fixed complex factor can be taken outside the integral.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

set_option warningAsError false

namespace Qatlib.Papers.Trainability23.HaarAverages

open scoped BigOperators Matrix MeasureTheory

/-- A fixed complex multiplicative factor can be taken outside a complex-valued integral. -/
theorem integral_const_mul_complex {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (c : ℂ) (f : α → ℂ) :
    MeasureTheory.integral μ (fun a => c * f a) = c * MeasureTheory.integral μ f :=
  MeasureTheory.integral_const_mul c f

end Qatlib.Papers.Trainability23.HaarAverages
