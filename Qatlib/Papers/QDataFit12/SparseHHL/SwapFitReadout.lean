/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.TensorRegisters.SwapReadout.BranchWeights
public import Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims.SourceCostModel
public import Qatlib.Papers.StateHSP24.MainResults.SourceSwapTest

@[expose] public section

/-!
# Algorithm 2 swap-test readout for prepared fitting states

Algorithm 2 of [Wiebe, Braun and Lloyd][WiebeBraunLloyd2012] compares two prepared quantum states.
On their tensor product, the ancilla-one amplitude is half the difference of the original
and flipped amplitudes. The normalized SWAP test identifies the resulting Born probability
with the fit-quality model's scalar probability.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.TensorRegisters.SwapReadout
open Qatlib.Foundations.TensorRegisters.SwapReadout
open Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims
open Qatlib.Papers.StateHSP24.MainResults

namespace Qatlib.Papers.QDataFit12.SparseHHL

/-- In Algorithm 2, the SWAP test of the data state and the prepared fitting state
returns ancilla `1` with the one-branch probability determined by their squared overlap. -/
theorem fit_swap_reject_probability (d : ℕ) (y ψ : QState (Fin d))
    (hy : Normalized y) (hψ : Normalized ψ) :
    (∑ p : Fin d × Fin d,
      Complex.normSq (swapTestState d (fun q => y q.1 * ψ q.2) (1, p))) =
        swapTestOneProbability (‖Qatlib.Foundations.PureStateMath.Inner y ψ‖ ^ 2) := by
  have hy' : ∑ i, Complex.normSq (y i) = 1 := by
    simpa only [Normalized, Complex.normSq_eq_norm_sq] using hy
  have hψ' : ∑ i, Complex.normSq (ψ i) = 1 := by
    simpa only [Normalized, Complex.normSq_eq_norm_sq] using hψ
  have hamplitude (i j : Fin d) :
      swapTestState d (fun q => y q.1 * ψ q.2) (1, (i, j)) =
        (circuit *ᵥ input y ψ) (true, (i, j)) := by
    rw [circuit_output]
    simp [swapTestState, swapOp_mulVec_apply]
    ring
  simp only [Fintype.sum_prod_type, hamplitude]
  change outcomeWeight y ψ true = swapTestOneProbability (‖Qatlib.Foundations.PureStateMath.Inner y ψ‖ ^ 2)
  simpa only [swapTestOneProbability, Qatlib.Foundations.PureStateMath.Inner,
    Complex.normSq_eq_norm_sq] using
    (normalized_outcome_weights y ψ hy' hψ').2

end Qatlib.Papers.QDataFit12.SparseHHL
