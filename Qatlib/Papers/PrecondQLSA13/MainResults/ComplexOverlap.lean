/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.TensorRegisters.SwapReadout.BranchWeights
public import Qatlib.Papers.PrecondQLSA13.MainResults.ReadoutOverlap.SourceReadoutOverlap

@[expose] public section

/-!
# Complex SWAP readout on the prepared solution and reference states

In [Clader, Jacobs and Sprouse][CladerJacobsSprouse2013], Eq. (9) uses the branch in which
the first three readout flags are successful. Given the normalized complex solution and
reference states for that branch, the fourth ancilla's zero amplitude is half the
symmetrized tensor amplitude. Its squared mass gives the zero-outcome probability.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators
open Qatlib.Foundations.TensorRegisters.SwapReadout
open Qatlib.Foundations.TensorRegisters.SwapReadout
open Qatlib.Papers.PrecondQLSA13.MainResults.ReadoutOverlap
open Qatlib.Concepts.SqEstimation.InnerProduct

namespace Qatlib.Papers.PrecondQLSA13.MainResults

/-- For the normalized reference and solution states in the prepared branch of Eq. (9),
the fourth ancilla has zero-outcome weight given by the squared complex overlap. -/
theorem swap_test_zero_weight_complex {N : ℕ} (R x : Fin N → ℂ)
    (hR : ∑ j, Complex.normSq (R j) = 1) (hx : ∑ j, Complex.normSq (x j) = 1) :
    (∑ j : Fin N, ∑ k : Fin N, Complex.normSq ((R j * x k + x j * R k) / 2)) =
      (1 + Complex.normSq (overlap R x)) / 2 := by
  have hamplitude (j k : Fin N) :
      (circuit *ᵥ input R x) (false, (j, k)) = (R j * x k + x j * R k) / 2 := by
    rw [circuit_output]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  simpa only [outcomeWeight, hamplitude, overlap, sqInnerTarget, dotProduct, Pi.star_apply]
    using (normalized_outcome_weights R x hR hx).1

end Qatlib.Papers.PrecondQLSA13.MainResults
