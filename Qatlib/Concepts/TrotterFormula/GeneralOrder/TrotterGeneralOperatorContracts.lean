/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts

/-!
# Proposed general-operator scaling statement

This module defines `TrotterGeneralOperatorScaling`, a proposed error contract for segmented
matrix words matching the target exponential through positive order `p`. In the setting of
[ChildsEtAl2021Trotter], the stated budget uses `pfCommAlphaSelf`, a denominator `(p + 1)! * r ^
p`, and exponential norm inflation; this formulation has no additional numerator factor `p!`.

## Main statements

* `TrotterGeneralOperatorScaling`: records the proposed general-operator segmented error bound.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposed general-operator error bound for segmented matched-order words using
`pfCommAlphaSelf` and exponential norm inflation without an additional `p!` factor. -/
def TrotterGeneralOperatorScaling : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (p r : ℕ), 1 ≤ p → 0 < r →
    (∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n) →
    ∀ t : ℝ,
    let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten
    ‖w.prod - NormedSpace.exp (t • H)‖ ≤
      pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
        (((p + 1).factorial : ℝ) * (r : ℝ) ^ p) *
        Real.exp (4 * |t| * (suzukiMass xs + ‖H‖))

end Qatlib.Concepts.TrotterFormula.GeneralOrder
