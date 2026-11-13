/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.RestartSearchDefs

/-!
# Paid restart search guarantees

`ActualPaidRestartSearch` states the existence of a source-prepared restart search with a
bounded iteration count, zero nontermination mass, and explicit expected clock-cost bounds. It
includes charged execution with prices j + 2 and 2, together with zero joint halt mass at every
unmarked address.

For the mathematical background, see [BoyerEtAl1998].

## Main statements

* `ActualPaidRestartSearch`: The proposition asserting a common valid restart circuit with j ≤
  π/(8θ) + 1, zero nontermination mass, expected clock costs bounded by π/(4θ) + 4, π/(4θ) + 6,
  and 4 for the specified price models, and no halting output outside the marked set.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

/-- The proposition asserting a common valid restart circuit with j ≤ π/(8θ) + 1, zero
nontermination mass, expected clock costs bounded by π/(4θ) + 4, π/(4θ) + 6, and 4 for the
specified price models, and no halting output outside the marked set. -/
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
