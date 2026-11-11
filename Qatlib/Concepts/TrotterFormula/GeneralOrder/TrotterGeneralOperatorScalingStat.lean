/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrectedStat

/-!
# Statement of corrected general-operator scaling

This module defines `TrotterGeneralOperatorScalingCorrected` for segmented product formulas
whose coefficients match the target exponential through order `p`. The contract records the
factorial-normalized commutator budget and exponential norm inflation for general matrices in
the setting of [ChildsEtAl2021Trotter].

## Main statements

* `TrotterGeneralOperatorScalingCorrected`: specifies the corrected segmented general-matrix
  error estimate.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposition asserting the general-operator segmented error bound with numerator `p! *
pfCommAlphaSelf xs (p + 1)` and exponential norm inflation. -/
def TrotterGeneralOperatorScalingCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (p r : ℕ), 1 ≤ p → 0 < r →
    (∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n) →
    ∀ t : ℝ,
    let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten
    ‖w.prod - NormedSpace.exp (t • H)‖ ≤
      (p.factorial : ℝ) * pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
        (((p + 1).factorial : ℝ) * (r : ℝ) ^ p) *
        Real.exp (4 * |t| * (suzukiMass xs + ‖H‖))

end Qatlib.Concepts.TrotterFormula.GeneralOrder
