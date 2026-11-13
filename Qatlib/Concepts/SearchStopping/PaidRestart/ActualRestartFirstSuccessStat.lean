/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.RestartSearchDefs

/-!
# Statement of the restart first-success law

Defines `ActualRestartFirstSuccess`, the joint law of the returned address and total receipt in
a fixed-price Grover restart process. The mass after `r` failed attempts is the failure
probability to power `r` times the marked address's Born mass, and only positive multiples of
the price can occur. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `ActualRestartFirstSuccess`: The proposition specifying geometric first-success masses at
  receipts `(r + 1) * price`, zero mass on unmarked addresses, and zero mass at all other
  receipts for positive-price restarts.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

/-- The proposition specifying geometric first-success masses at receipts `(r + 1) * price`,
zero mass on unmarked addresses, and zero mass at all other receipts for positive-price
restarts. -/
def ActualRestartFirstSuccess : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (T' : Matrix I I ℂ) (v : QState I), T' ∈ Matrix.unitaryGroup I ℂ →
    ∀ hv : Normalized v, T' *ᵥ v = Uniform I → ∀ (A : Finset I) (j : ℕ)
      (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j)) (price : ℕ), 0 < price →
    let p := MeasureProb (GroverState A j) A
    let next := bbhtActualRestartNextPrice T' v j A hC hv price
    (∀ (r : ℕ) (i : I), branchHaltJoint next (Sum.inr ()) i ((r + 1) * price) =
      (ENNReal.ofReal (1 - p)) ^ r *
        (if i ∈ A then ENNReal.ofReal (BornProb (GroverState A j) i) else 0)) ∧
    (∀ (i : I) (k : ℕ), i ∉ A → branchHaltJoint next (Sum.inr ()) i k = 0) ∧
    ∀ (i : I) (k : ℕ), (∀ r : ℕ, k ≠ (r + 1) * price) →
      branchHaltJoint next (Sum.inr ()) i k = 0

end Qatlib.Concepts.SearchStopping.PaidRestart
