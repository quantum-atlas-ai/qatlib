/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.GaussOracle
public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.QueryReduction

@[expose] public section

/-!
# Actual Gauss-oracle execution and observed label distributions

Every true phase is derived from the corresponding finite-field Gauss sum.
The measured record law is computed from executions of the constructed
Gauss unitaries. It equals the product QPE law used by the weight decoder.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.GaussSumEst02.MainResults.Source
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A batch of actual nontrivial multiplicative characters and nonzero frequency. -/
structure GaussBatch (F : Type) [Field F] (terms : ℕ) where
  /-- The actual characters queried by the source algorithm. -/
  character : Fin terms → MultChar F
  /-- Each queried Gauss sum has square-root magnitude. -/
  nontrivial : ∀ a, (character a).IsNontrivial
  /-- The actual additive Fourier character. -/
  additive : AddChar F
  /-- The nonzero field frequency. -/
  frequency : F
  /-- A zero frequency is not a phase query. -/
  frequency_ne : frequency ≠ 0

/-- True phases are supplied by the proved polar form of actual Gauss sums. -/
def gaussPhases {terms : ℕ} (batch : GaussBatch F terms) (a : Fin terms) : ℝ :=
  Classical.choose (gauss_phase_eigen (batch.character a) (batch.nontrivial a)
    batch.additive batch.frequency batch.frequency_ne)

/-- The computed true phase is tied to the actual finite Gauss sum. -/
theorem gaussPhases_eq {terms : ℕ} (batch : GaussBatch F terms) (a : Fin terms) :
    gaussSum (batch.character a).toFun batch.additive batch.frequency =
      (Real.sqrt (Fintype.card F : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * gaussPhases batch a) :=
  (Classical.choose_spec (gauss_phase_eigen (batch.character a) (batch.nontrivial a)
    batch.additive batch.frequency batch.frequency_ne)).1

/-- The actual measured marginal after a counted Gauss-oracle QPE execution. -/
def gaussMarginal (M : ℕ) (hM : 0 < M) (character : MultChar F)
    (additive : AddChar F) (frequency : F) (label : Fin M) : ℝ :=
  ∑ i : F, ‖Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle
      (gaussOracle character additive frequency)))
    (countedPhaseCircuit M)
    (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (chiState character)))
    (label, false, i)‖ ^ 2

/-- The actual marginal equals the QPE law at the actual Gauss phase. -/
theorem gaussMarginal_eq {terms : ℕ} (batch : GaussBatch F terms) (a : Fin terms)
    (M : ℕ) (hM : 0 < M) (label : Fin M) :
    gaussMarginal M hM (batch.character a) batch.additive batch.frequency label =
      bhmt11OutcomeMass M (gaussPhases batch a) label := by
  apply phase_mass M hM (gaussOracle (batch.character a) batch.additive batch.frequency)
    (chiState (batch.character a)) (gaussPhases batch a) (gauss_state_normalized _)
  exact (Classical.choose_spec (gauss_phase_eigen (batch.character a) (batch.nontrivial a)
    batch.additive batch.frequency batch.frequency_ne)).2

/-- Independent actual executions give the record mass used by the certified decoder. -/
theorem gauss_record_law {terms : ℕ} (batch : GaussBatch F terms)
    (M : ℕ) (hM : 0 < M) (record : Fin terms → Fin M) :
    (∏ a, gaussMarginal M hM (batch.character a) batch.additive batch.frequency (record a)) =
      batchMass M (gaussPhases batch) record := by
  unfold batchMass
  apply Finset.prod_congr rfl
  intro a _
  exact gaussMarginal_eq batch a M hM (record a)

/-- Actual Gauss-oracle batch executions have the same counted ledger as the decoder. -/
theorem gauss_query_count {terms : ℕ} (batch : GaussBatch F terms) (M : ℕ) (hM : 0 < M) :
    (∑ _a : Fin terms, QueryCount (countedPhaseCircuit (I := F) M)) = batchQueries terms M := by
  rw [batchQueries_eq terms M hM]
  calc
    _ = (∑ _a : Fin terms, (M - 1)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (counted_offgrid_qpe_clean_flag M hM
        (gaussOracle (batch.character a) batch.additive batch.frequency)
        (chiState (batch.character a))).2.1
    _ = _ := by simp

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
