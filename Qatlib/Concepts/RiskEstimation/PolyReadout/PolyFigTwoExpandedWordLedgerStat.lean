/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedDefs

/-!
# Specification of expanded polynomial resource counts

This module states `PolyFigTwoExpandedWordLedger`, recording the rotation-word length bound and
exact counted amplitude-estimation costs for expanded payoff preparation.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `PolyFigTwoExpandedWordLedger`: The proposition that the expanded angle word has length at
  most `31 * (d + 1) * n ^ (d + 1)`, for `d = fp.natDegree * (2 * u + 1)` and `n ≥ 1`, together
  with the stated exact access, query, and gate counts for `2 * r + 1` repetitions.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix

/-- The proposition that the expanded angle word has length at most `31 * (d + 1) * n ^ (d +
1)`, for `d = fp.natDegree * (2 * u + 1)` and `n ≥ 1`, together with the stated exact
access, query, and gate counts for `2 * r + 1` repetitions. -/
def PolyFigTwoExpandedWordLedger : Prop :=
  ∀ (n u : ℕ) (hn : 1 ≤ n) (A : Matrix (Reg n) (Reg n) ℂ) (j : Reg n) (c : ℝ)
    (fp : Polynomial ℝ) (M r : ℕ), A ∈ Matrix.unitaryGroup (Reg n) ℂ → (hM : 2 ≤ M) →
    (figTwoAngleWord n u c fp).length ≤
      31*(fp.natDegree*(2*u+1)+1)*n^(fp.natDegree*(2*u+1)+1) ∧
    (2*r+1)*aeForwardAccesses (aeAccessWord (I := Reg (n+1+(n-1))) M) = (2*r+1)*M ∧
    (2*r+1)*aeBackwardAccesses (aeAccessWord (I := Reg (n+1+(n-1))) M) = (2*r+1)*(M-1) ∧
    (2*r+1)*QueryCount
        (countedAECircuit M (figTwoExpandedPreparation n A u c fp) (figTwoStart n j)) =
      (2*r+1)*(M-1) ∧
    (2*r+1)*GateCount
        (countedAECircuit M (figTwoExpandedPreparation n A u c fp) (figTwoStart n j)) =
      (2*r+1)*(5*(M-1)+3)

end Qatlib.Concepts.RiskEstimation.PolyReadout
