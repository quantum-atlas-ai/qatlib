/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix

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
