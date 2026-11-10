/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option warningAsError false

namespace Qatlib.Papers.Trainability23.HaarAverages

open scoped BigOperators Matrix MeasureTheory

theorem integral_const_mul_complex {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (c : ℂ) (f : α → ℂ) :
    MeasureTheory.integral μ (fun a => c * f a) = c * MeasureTheory.integral μ f :=
  MeasureTheory.integral_const_mul c f

end Qatlib.Papers.Trainability23.HaarAverages
