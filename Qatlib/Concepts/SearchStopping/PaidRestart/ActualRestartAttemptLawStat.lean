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
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

def ActualRestartAttemptLaw : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (T' : Matrix I I ℂ) (v : QState I), T' ∈ Matrix.unitaryGroup I ℂ →
    ∀ hv : Normalized v, T' *ᵥ v = Uniform I → ∀ (A : Finset I) (j : ℕ)
      (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j)) (price : ℕ),
    let p := MeasureProb (GroverState A j) A
    let next := bbhtActualRestartNextPrice T' v j A hC hv price
    (∀ i : I, next () (Sum.inl i, price) =
      if i ∈ A then ENNReal.ofReal (BornProb (GroverState A j) i) else 0) ∧
    next () (Sum.inr (), price) = ENNReal.ofReal (1 - p) ∧
    ∀ (cfg : I ⊕ Unit) (k : ℕ), k ≠ price → next () (cfg, k) = 0

end Qatlib.Concepts.SearchStopping.PaidRestart
