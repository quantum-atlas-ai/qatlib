/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasis
set_option warningAsError false

open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

def OrbitFourierBasisSubgoal : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E],
    (∀ χ η : AddChar E ℂ,
        Inner (orbitFourierVec E χ) (orbitFourierVec E η) = if χ = η then 1 else 0)
    ∧ (∀ (g₀ : E) (χ : AddChar E ℂ),
        ApplyGate (orbitRegMatrix E g₀) (orbitFourierVec E χ)
          = (χ (-g₀)) • orbitFourierVec E χ)
    ∧ ( (∑ χ : AddChar E ℂ,
          ((Real.sqrt ((Fintype.card E : ℝ)))⁻¹ • orbitFourierVec E χ)) = Ket (0 : E))

end Qatlib.Concepts.HspRecovery.AbelianSampling
