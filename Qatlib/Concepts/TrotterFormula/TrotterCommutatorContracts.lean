/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.NestedCommutatorScaling

/-!
# Commutator-scaling specification for product formulas

The proposition `TrotterCommutatorScaling` specifies a repeated product-formula guarantee for
skew-Hermitian generators whose coefficient series matches the target exponential through a
prescribed order. It combines unitarity, the exact exponential-factor count, and an error
estimate involving `pfCommAlphaSelf`.

The specification expresses the dependence on time, order, and number of repetitions used in
commutator-based Trotter error analysis [ChildsEtAl2021Trotter].

## Main statements

* `TrotterCommutatorScaling`: the universal repeated-word specification with error bounded by
  `pfCommAlphaSelf xs (p + 1) * |t|^(p + 1) / ((p + 1)! * r^p)`.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The universal specification that a repeated exponential word with skew-Hermitian generators
and coefficients matching a skew-Hermitian target through order `p ≥ 1` is unitary, has `r *
xs.length` factors, and satisfies the commutator error bound `pfCommAlphaSelf xs (p + 1) *
|t|^(p + 1) / ((p + 1)! * r^p)` for positive `r`. -/
def TrotterCommutatorScaling : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (p r : ℕ), 1 ≤ p → 0 < r →
    (∀ X ∈ xs, Xᴴ = -X) → Hᴴ = -H →
    (∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n) →
    ∀ t : ℝ,
    let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten
    w.prod ∈ Matrix.unitaryGroup I ℂ ∧
    w.length = r * xs.length ∧
    ‖w.prod - NormedSpace.exp (t • H)‖ ≤
      pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
        (((p + 1).factorial : ℝ) * (r : ℝ) ^ p)

end Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts
