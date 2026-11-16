/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section


/-! Scalar deviation expressions for sampled threshold approximation.

The definitions preserve the source constants. They do not impose a random-matrix
law or assert a high-probability matrix approximation theorem.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QRecommender16.MainResults.MatrixSampling

/-- The constant `3√η k^{1/4} μ^{−1/4}` from (9), with fourth roots written
as iterated square roots: `k^{1/4} = sqrt (sqrt k)` and
`μ^{−1/4} = 1 / sqrt (sqrt μ)`. -/
def samplingError (η μ : ℝ) (k : ℕ) : ℝ :=
  3 * Real.sqrt η * Real.sqrt (Real.sqrt (k : ℝ)) * (1 / Real.sqrt (Real.sqrt μ))


/-- The constant `3√η k^{1/4} μ^{−1/4} (2 + (1−κ)^{−1/2})` of (10), with fourth
roots as iterated square roots. -/
def precisionError (η μ κ : ℝ) (k : ℕ) : ℝ :=
  3 * Real.sqrt η * Real.sqrt (Real.sqrt (k : ℝ)) * (1 / Real.sqrt (Real.sqrt μ))
    * (2 + 1 / Real.sqrt (1 - κ))


end Qatlib.Papers.QRecommender16.MainResults.MatrixSampling
