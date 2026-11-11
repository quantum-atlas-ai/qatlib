/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs

/-!
# Statement of G-unit existence

This module defines `GUnitExistence`, the proposition that each finite local QTM has a unitary
matrix on three-cell windows satisfying `GUnitFixesH` and `GUnitSteps`. It packages the
fixed-family and transition requirements for the local G gate in the circuit simulation of
[Yao1993].

## Main statements

* `GUnitExistence`: state the existence of a unitary window matrix with the required
  fixed-family and local-step behavior.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

/-- The proposition that every local QTM with finite state and alphabet types possesses a
unitary three-cell window matrix satisfying `GUnitFixesH` and `GUnitSteps`, corresponding to
[Yao, Lemma 2][Yao1993]. -/
def GUnitExistence : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
      (M : LocalQTM Q A),
    ∃ G : Matrix (GWindow Q A) (GWindow Q A) ℂ,
      G ∈ Matrix.unitaryGroup (GWindow Q A) ℂ ∧
      GUnitFixesH M G ∧ GUnitSteps M G

end Qatlib.Foundations.StandardDefs.WindowSim
