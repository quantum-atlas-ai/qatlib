/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalance
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Qatlib

def QuantumDetailedBalanceFixedPoint : Prop :=
  ∀ (D : ℕ) (T : QuantumChannel D D) (σ : Operator D),
    IsDensityOperator σ → QuantumDetailedBalance T.map σ → T.map σ = σ

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
