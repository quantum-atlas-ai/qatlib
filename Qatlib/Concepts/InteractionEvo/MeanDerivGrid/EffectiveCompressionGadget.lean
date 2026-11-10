/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix

theorem effectiveCompression_naive_reuse_counterexample :
    ∃ (R : Matrix Bool Unit ℂ) (U : Matrix Bool Bool ℂ),
      U ∈ Matrix.unitaryGroup Bool ℂ ∧ Rᴴ*R=1 ∧ Rᴴ*U*R=0 ∧ Rᴴ*(U*U)*R=1 := by
  let R : Matrix Bool Unit ℂ := fun b _ => if b then 0 else 1
  refine ⟨R,PauliX,pauliX_unitary,?_,?_,?_⟩ <;>
    ext i j <;> cases i <;> cases j <;>
    simp [R,Matrix.mul_apply,Matrix.conjTranspose_apply,PauliX,permMatrix]

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
