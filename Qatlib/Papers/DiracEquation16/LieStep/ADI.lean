/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiracEquation16.SpinGates.Spin

/-!
# Ordered alternating-direction Dirac steps

`adiStep` composes the vector, scalar, mass, and three directional matrices in a fixed order.
The module records this product explicitly and proves that the composite satisfies the
conjugate-transpose identity when each factor does.

This development follows [FillionGourdeauMacLeanLaflamme2017].

## Main statements

* `adiStep_eq_ordered`: the step is the ordered product of its six factors.
* `adiStep_unitary`: factorwise conjugate-transpose identities pass to the step.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.DiracEquation16.LieStep
open Qatlib.Papers.DiracEquation16.SpinGates

section ADI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordered six-factor matrix product for an alternating-direction Dirac step. -/
def adiStep (QA QV Qm Qz Qy Qx : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  QA * (QV * (Qm * (Qz * (Qy * Qx))))

omit [DecidableEq ι] in

/-- The alternating-direction step equals the left-associated product `QA * QV * Qm * Qz * Qy *
Qx`. -/
theorem adiStep_eq_ordered (QA QV Qm Qz Qy Qx : Matrix ι ι ℂ) :
    adiStep QA QV Qm Qz Qy Qx = ((((QA * QV) * Qm) * Qz) * Qy) * Qx := by
  unfold adiStep
  noncomm_ring

/-- If each of the six factors satisfies `Qᴴ * Q = 1`, their alternating-direction product
satisfies the same identity. -/
theorem adiStep_unitary (QA QV Qm Qz Qy Qx : Matrix ι ι ℂ)
    (hA : QAᴴ * QA = 1) (hV : QVᴴ * QV = 1) (hM : Qmᴴ * Qm = 1)
    (hZ : Qzᴴ * Qz = 1) (hY : Qyᴴ * Qy = 1) (hX : Qxᴴ * Qx = 1) :
    (adiStep QA QV Qm Qz Qy Qx)ᴴ * adiStep QA QV Qm Qz Qy Qx = 1 := by
  unfold adiStep
  exact unitary_mul hA (unitary_mul hV (unitary_mul hM (unitary_mul hZ (unitary_mul hY hX))))

end ADI

end Qatlib.Papers.DiracEquation16.LieStep
