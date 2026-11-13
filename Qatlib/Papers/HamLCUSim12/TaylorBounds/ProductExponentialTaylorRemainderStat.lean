/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.TaylorBounds.ExponentialProductTaylor

/-!
# Exponential-product Taylor remainder statement

The proposition `ProductExponentialTaylorRemainder` specifies a norm bound for the difference
between an ordered product of Hamiltonian evolutions and `expProductTaylor`. The bound uses the
scalar sum S = ∑ⱼ |aⱼ| ‖Hⱼ‖ |t| and applies to arbitrary finite complex matrix families. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `ProductExponentialTaylorRemainder`: The proposition bounding the norm of the total-degree-ℓ
  exponential-product Taylor remainder by S^(ℓ + 1) exp S / (ℓ + 1)!, with S = ∑ⱼ |aⱼ| ‖Hⱼ‖ |t|.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib
set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.TaylorBounds

open scoped Matrix.Norms.L2Operator

/-- The proposition bounding the norm of the total-degree-ℓ exponential-product Taylor remainder
by S^(ℓ + 1) exp S / (ℓ + 1)!, with S = ∑ⱼ |aⱼ| ‖Hⱼ‖ |t|. -/
def ProductExponentialTaylorRemainder : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I],
    ∀ (M : ℕ) (a : Fin M → ℝ) (H : Fin M → Matrix I I ℂ) (t : ℝ) (ℓ : ℕ),
      ‖expProductMul (fun j => HamiltonianEvolution (H j) (a j * t)) -
          expProductTaylor (expProductGenerator a H) t ℓ‖ ≤
        ((∑ j, |a j| * ‖H j‖ * |t|) ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ)) *
          Real.exp (∑ j, |a j| * ‖H j‖ * |t|)

end Qatlib.Papers.HamLCUSim12.TaylorBounds
