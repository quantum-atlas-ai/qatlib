/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation

@[expose] public section

/-!
# LowRankMatrix19 — partition-function perturbations

This file formalizes the finite-dimensional matrix-analysis core of
[ChiaEtAl2022], Lemma 6.28.  The matrix norm is the induced
Euclidean `L2Operator` norm supplied by `Matrix.Norms.L2Operator`.  The result
does not assume that the two Hermitian matrices commute.  The index type is
finite and nonempty, matching the positive-dimensional matrices of the lemma
and excluding the empty index, where both sides of the bound vanish.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LowRankMatrix19.MatrixFunctions

open Matrix
open Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
open scoped Matrix.Norms.L2Operator

/-- The two-sided partition-function perturbation estimate from Lemma 6.28.

For Hermitian `H` and `K` on a nonempty finite index type, the absolute change
of the real partition function is bounded by the trace norm of the exponential
difference, which is in turn controlled by the Euclidean operator norm of
`H - K`.  The universal estimate is quantified over that index type before the
matrices, so its constants are uniform and independent of the positive
dimension and of the particular pair.
-/
theorem partition_function_perturbation :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (H K : Matrix I I ℂ),
      H.IsHermitian → K.IsHermitian →
      |(Matrix.trace (NormedSpace.exp K)).re -
          (Matrix.trace (NormedSpace.exp H)).re| ≤
        Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) ∧
      Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) ≤
        (Real.exp ‖H - K‖ - 1) *
          (Matrix.trace (NormedSpace.exp H)).re := by
  intro I _ _ _ H K hH hK
  have hreal :
      |(Matrix.trace (NormedSpace.exp K - NormedSpace.exp H)).re| ≤
        Matrix.traceNorm (NormedSpace.exp K - NormedSpace.exp H) := by
    exact (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  have hfirst :
      |(Matrix.trace (NormedSpace.exp K)).re -
          (Matrix.trace (NormedSpace.exp H)).re| ≤
        Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) := by
    calc
      |(Matrix.trace (NormedSpace.exp K)).re -
          (Matrix.trace (NormedSpace.exp H)).re| =
          |(Matrix.trace (NormedSpace.exp K - NormedSpace.exp H)).re| := by
            rw [Matrix.trace_sub]
            rfl
      _ ≤ Matrix.traceNorm (NormedSpace.exp K - NormedSpace.exp H) := hreal
      _ = Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) := by
        rw [← Matrix.traceNorm_neg, neg_sub]
  exact ⟨hfirst, noncommuting_exp_trace_norm I H K hH hK⟩

end Qatlib.Papers.LowRankMatrix19.MatrixFunctions
