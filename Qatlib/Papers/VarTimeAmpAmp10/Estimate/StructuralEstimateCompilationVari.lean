/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationStat
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StructuralEstimateCompilationAux

/-!
# Verification of structural estimation compilation

This module proves `StructuralEstimateCompilation` for the variable-time estimation framework
supporting [Ambainis2012]. The theorem `structuralEstimateCompilation_answer` combines unitary
data-word evaluation, compilation preserving circuit execution and weighted time, and the
normalized adaptive-record probability bounds.

## Main statements

* `structuralEstimateCompilation_answer`: Establish the structural estimation compilation
  proposition.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators

/-- The structural estimation compilation proposition holds: legal data words have unitary
matrices and exact compiled estimation realizations, and the corresponding causal adaptive
record laws satisfy the stated probability bounds [Ambainis2012]. -/
theorem structuralEstimateCompilation_answer : StructuralEstimateCompilation := by
  intro C _ _ stages history hl j₀
  refine ⟨?_, ?_, ?_⟩
  · intro word hw
    exact dataVtWordMatrix_unitary stages history j₀ hl word hw
  · intro M hM word hw
    refine ⟨compiledAEWord M word, compiledAEWord_legal M (by omega) stages word hw,
      compiledAEWord_time M word, compiledAEWord_run M stages history j₀ word, ?_⟩
    intro n
    refine ⟨?_, ?_, ?_⟩
    · intro ψ
      apply vtFreshGates_run_congr
      intro χ
      exact (compiledAEWord_run M stages history j₀ word χ).trans
        (vt_executed_gates_run _ _ χ).symm
    · have hrep (k : ℕ) : (List.replicate k (compiledAEWord M word)).flatten.length =
          k*(compiledAEWord M word).length := by
        induction k with
        | zero => simp
        | succ k ih => simp [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm]
      exact hrep n
    · have hrep (k : ℕ) : compiledVtWordTime (List.replicate k (compiledAEWord M word)).flatten =
          k*compiledVtWordTime (compiledAEWord M word) := by
        induction k with
        | zero => simp [compiledVtWordTime]
        | succ k ih => rw [List.replicate_succ, List.flatten_cons, compiledVtWordTime_append, ih]; ring
      rw [hrep, compiledAEWord_time]
      ring
  · intro M hM r n words hw hdep
    exact ⟨dataRecordLaw_sum_one M hM r n stages history j₀ hl words hw hdep,
      dataRecordLaw_nonneg M hM r n stages history j₀ words,
      dataRecordGood_mass M hM r n stages history j₀ hl words hw hdep⟩

end Qatlib.Papers.VarTimeAmpAmp10.Estimate
