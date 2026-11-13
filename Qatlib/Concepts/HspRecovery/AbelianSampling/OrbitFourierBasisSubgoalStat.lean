/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasis

/-!
# Specification of the orbit Fourier basis identities

`OrbitFourierBasisSubgoal` collects three identities for the regular representation of a finite
abelian group: character vector orthonormality, the translation eigenvalue `χ (-g₀)`, and the
equal amplitude expansion of `Ket 0`. These identities specify the Fourier decomposition used in
stabilizer phase sampling. [Kitaev1995]

## Main statements

* `OrbitFourierBasisSubgoal`: the proposition collecting the three Fourier vector identities.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

/-- The proposition that normalized character vectors are orthonormal, translation by `g₀` acts
on the vector for `χ` with eigenvalue `χ (-g₀)`, and their equal amplitude sum is `Ket 0`. -/
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
