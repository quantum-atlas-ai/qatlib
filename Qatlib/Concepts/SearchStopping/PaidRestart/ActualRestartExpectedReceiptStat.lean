/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.RestartSearchDefs
set_option warningAsError false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

def ActualRestartExpectedReceipt : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (T' : Matrix I I ℂ) (v : QState I), T' ∈ Matrix.unitaryGroup I ℂ →
    ∀ hv : Normalized v, T' *ᵥ v = Uniform I → ∀ (A : Finset I) (j : ℕ)
      (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j)) (price : ℕ), 0 < price →
    let p := MeasureProb (GroverState A j) A
    let next := bbhtActualRestartNextPrice T' v j A hC hv price
    (p = 0 → generalNeverMass (branchClockNext next) (branchClockEmbed (Sum.inr ())) = 1 ∧
      generalUnboundedTime (branchClockNext next) (branchClockEmbed (Sum.inr ())) = ⊤) ∧
    (0 < p → generalNeverMass (branchClockNext next) (branchClockEmbed (Sum.inr ())) = 0 ∧
    generalUnboundedTime (branchClockNext next) (branchClockEmbed (Sum.inr ())) =
      ENNReal.ofReal ((price : ℝ) / p) ∧
    (∑' r : ℕ, (((r + 1) * j : ℕ) : ℝ≥0∞) *
      ∑ i : I, branchHaltJoint next (Sum.inr ()) i ((r + 1) * price)) =
      ENNReal.ofReal ((j : ℝ) / p))

end Qatlib.Concepts.SearchStopping.PaidRestart
