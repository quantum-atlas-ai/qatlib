/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutator

/-!
# Statement of the first-order Trotter tail-sum bound

This module defines `TrotterFirstOrderTailSum`, the segmented Lie error estimate expressed using
commutators with later-term sums. Its formulation retains cancellations within each tail sum, as
in [ChildsEtAl2021Trotter].

## Main statements

* `TrotterFirstOrderTailSum`: the positive-segment tail-commutator error proposition for
  Hermitian families.

## References

* [Childs et al., Proposition 15][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.FiniteStrang

namespace Qatlib.Concepts.TrotterFormula.LieStrang

open scoped Matrix.Norms.L2Operator

/-- The proposition that every Hermitian finite family with positive segment count has Lie error
at most `|t|² / (2 * r)` times the sum of tail-commutator norms, as in [Childs et al.,
Proposition 15][ChildsEtAl2021Trotter]. -/
def TrotterFirstOrderTailSum : Prop :=
  ∀ (D m r : ℕ) (H : Fin m → Operator D) (t : ℝ), 0 < r →
    (∀ j, (H j).IsHermitian) →
    ‖pfFamily H t r - HamiltonianEvolution (∑ j, H j) t‖ ≤
      |t| ^ 2 / (2 * (r : ℝ)) * ∑ j : Fin m, ‖pfComm (finiteStrangTail H j) (H j)‖

end Qatlib.Concepts.TrotterFormula.LieStrang
