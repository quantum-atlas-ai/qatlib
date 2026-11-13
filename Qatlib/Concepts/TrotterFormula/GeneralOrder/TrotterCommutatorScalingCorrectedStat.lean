/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.NestedCommutatorScaling

/-!
# Statement of corrected commutator scaling

This module defines `TrotterCommutatorScalingCorrected`, a segmented product-formula statement
in the commutator-scaling setting of [ChildsEtAl2021Trotter]. It requires positive order and
segment count, skew-Hermitian generators and target, and coefficient matching through order `p`;
its conclusions give unitarity, length `r * xs.length`, and the factorial-normalized commutator
error estimate.

## Main statements

* `TrotterCommutatorScalingCorrected`: specifies the unitary segmented word and its error
  budget.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposition asserting unitarity, word length, and a factorial-normalized commutator
error bound for segmented skew-Hermitian words whose coefficients match through order `p`. -/
def TrotterCommutatorScalingCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (p r : ℕ), 1 ≤ p → 0 < r →
    (∀ X ∈ xs, Xᴴ = -X) → Hᴴ = -H →
    (∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n) →
    ∀ t : ℝ,
    let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten
    w.prod ∈ Matrix.unitaryGroup I ℂ ∧
    w.length = r * xs.length ∧
    ‖w.prod - NormedSpace.exp (t • H)‖ ≤
      (p.factorial : ℝ) * pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
        (((p + 1).factorial : ℝ) * (r : ℝ) ^ p)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
