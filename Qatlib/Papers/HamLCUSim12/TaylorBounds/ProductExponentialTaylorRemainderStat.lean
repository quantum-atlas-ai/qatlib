/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.TaylorBounds.ExponentialProductTaylor
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib
set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.TaylorBounds

open scoped Matrix.Norms.L2Operator

def ProductExponentialTaylorRemainder : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I],
    ∀ (M : ℕ) (a : Fin M → ℝ) (H : Fin M → Matrix I I ℂ) (t : ℝ) (ℓ : ℕ),
      ‖expProductMul (fun j => HamiltonianEvolution (H j) (a j * t)) -
          expProductTaylor (expProductGenerator a H) t ℓ‖ ≤
        ((∑ j, |a j| * ‖H j‖ * |t|) ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ)) *
          Real.exp (∑ j, |a j| * ‖H j‖ * |t|)

end Qatlib.Papers.HamLCUSim12.TaylorBounds
