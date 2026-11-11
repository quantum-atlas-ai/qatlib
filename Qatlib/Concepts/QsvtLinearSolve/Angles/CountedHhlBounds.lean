/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtLinearSolve.Angles.CountedHhlDefs

/-!
# Explicit query and gate ledgers for an HHL word

The counted HHL construction separates forward and inverse oracle calls,
proves unitarity of controlled preparation, and charges input preparation in
its gate ledger. A resolution hypothesis yields a query-count lower estimate.
Further identities compare fresh retries with amplification in the local
resource model.

The algorithmic background is [HarrowHassidimLloyd2009] and
[Brassard et al., amplitude amplification][BrassardEtAl2002]. The exact constants
and ledger identities are those of the counted construction defined here.
-/
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtLinearSolve.AnglesCore

open Matrix Qatlib

/-- Collect the exact forward and backward HHL query counts, unitarity of controlled input
preparation, and the preparation-inclusive gate ledger. The endpoint also records the
distinct gate totals of one fresh retry and one amplification round in the setting of
[HarrowHassidimLloyd2009]. -/
theorem clause31_endpoint :
    (∀ (D M : ℕ) (c : ℝ) (B : Operator D), 0 < M →
      fwdCount (countedHHLWord (D := D) M c B) = M - 1 ∧
        bwdCount (countedHHLWord (D := D) M c B) = M - 1) ∧
    (∀ (D M : ℕ) {B : Operator D},
      B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      controlOracle (countedHHLPrepMain (D := D) (M := M) B)
        ∈ Matrix.unitaryGroup (Bool × (Fin M × (Bool × Fin D))) ℂ) ∧
    (∀ (D M : ℕ) (c : ℝ) (B : Operator D) (hM : 0 < M) (tB : ℕ),
      (countedLedger D M tB).totalGates
        = tB + adjointGateCount (countedHHLWord (D := D) M c B)) ∧
    (∀ (tB g r q : ℕ),
      (freshRetryLedger tB g r q).totalQueries
          = (amplificationLedger tB g r q).totalQueries ∧
        (freshRetryLedger tB g r q).totalGates = 2 * (tB + g) ∧
        (amplificationLedger tB g r q).totalGates = tB + g + r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D M c B hM
    exact countedHHLWord_forward_backward_split M c B hM
  · intro D M B hB
    exact controlled_preparation_is_unitary hB
  · intro D M c B hM tB
    exact countedLedger_charges_input_preparation M c B hM tB
  · intro tB g r q
    exact fresh_retry_is_not_amplification tB g r q

/-- Collect the resolution lower estimate and the exact gate and query totals
for the counted HHL word. Compare [Harrow, Hassidim & Lloyd][HarrowHassidimLloyd2009]
for the linear-system algorithm motivating the construction. -/
theorem clause30_endpoint :
    (∀ (M : ℕ) {ε : ℝ}, 0 < M → 0 < ε →
      (1 : ℝ) / (M : ℝ) ≤ ε → ((2 * (M - 1) : ℕ) : ℝ) ≥ 2 / ε - 2) ∧
    (∀ (D M : ℕ) (tB : ℕ),
      (countedLedger D M tB).totalGates = tB + 4 * (M - 1) + 6) ∧
    (∀ (D M : ℕ) (tB : ℕ),
      (countedLedger D M tB).totalQueries = 2 * (M - 1) + (M - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro M ε hM hε hres
    exact countedHHLWord_queryCount_ge_accuracy_resolution M hM hε hres
  · intro D M tB
    exact countedLedger_totalGates D M tB
  · intro D M tB
    exact countedLedger_totalQueries D M tB

end Qatlib.Concepts.QsvtLinearSolve.AnglesCore
