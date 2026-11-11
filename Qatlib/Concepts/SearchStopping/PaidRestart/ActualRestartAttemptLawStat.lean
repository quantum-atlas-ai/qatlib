/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.RestartSearchDefs

/-!
# Statement of the paid restart attempt law

Defines `ActualRestartAttemptLaw`, the one-attempt distributional specification for a prepared
Grover search followed by verification. Successful marked addresses carry their Grover Born
masses, failure has the complementary mass, and the receipt always records the prescribed price.
For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `ActualRestartAttemptLaw`: The proposition that one verified restart attempt has
  marked-address Born masses, failure mass `1 - p`, and a receipt supported only at the
  specified price.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

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

/-- The proposition that one verified restart attempt has marked-address Born masses, failure
mass `1 - p`, and a receipt supported only at the specified price. -/
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
