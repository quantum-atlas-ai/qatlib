/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.FiniteStrang

namespace Qatlib.Concepts.TrotterFormula.LieStrang

open scoped Matrix.Norms.L2Operator

def TrotterFirstOrderTailSum : Prop :=
  ∀ (D m r : ℕ) (H : Fin m → Operator D) (t : ℝ), 0 < r →
    (∀ j, (H j).IsHermitian) →
    ‖pfFamily H t r - HamiltonianEvolution (∑ j, H j) t‖ ≤
      |t| ^ 2 / (2 * (r : ℝ)) * ∑ j : Fin m, ‖pfComm (finiteStrangTail H j) (H j)‖

end Qatlib.Concepts.TrotterFormula.LieStrang
