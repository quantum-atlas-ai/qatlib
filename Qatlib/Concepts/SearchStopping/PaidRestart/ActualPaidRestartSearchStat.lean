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

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

def ActualPaidRestartSearch : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (T' : Matrix I I ℂ) (seed : I), T' ∈ Matrix.unitaryGroup I ℂ →
    T' *ᵥ Ket seed = Uniform I → ∀ (t : ℕ) (θ : ℝ),
    0 < θ → θ < Real.pi / 2 →
    (Real.sin θ) ^ 2 = (t : ℝ) / (Fintype.card I : ℝ) →
    let v := Ket seed
    let hv := normalized_ket seed
    ∃ (j : ℕ) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j)),
      (j : ℝ) ≤ Real.pi / (8 * θ) + 1 ∧
      ∀ (A : Finset I), A.card = t →
      generalNeverMass (branchClockNext (bbhtActualRestartNext T' v j A hC hv))
        (branchClockEmbed (Sum.inr ())) = 0 ∧
      generalUnboundedTime (branchClockNext (bbhtActualRestartNext T' v j A hC hv))
        (branchClockEmbed (Sum.inr ())) ≤ ENNReal.ofReal (Real.pi / (4 * θ) + 4) ∧
      generalUnboundedTime
        (branchClockNext (bbhtActualRestartNextPrice T' v j A hC hv (j + 2)))
        (branchClockEmbed (Sum.inr ())) ≤ ENNReal.ofReal (Real.pi / (4 * θ) + 6) ∧
      generalUnboundedTime (branchClockNext (bbhtActualRestartNextPrice T' v j A hC hv 2))
        (branchClockEmbed (Sum.inr ())) ≤ 4 ∧
      ∀ (i : I) (k : ℕ), i ∉ A →
        branchHaltJoint (bbhtActualRestartNext T' v j A hC hv) (Sum.inr ()) i k = 0

end Qatlib.Concepts.SearchStopping.PaidRestart
