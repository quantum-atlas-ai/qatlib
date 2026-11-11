/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalance

/-!
# Basis operators for detailed-balance criteria

This module defines rank-one operators, weighted basis sums, and bra-ket matrix elements used to
express the finite basis criterion for quantum detailed balance in [TemmeEtAl2011]. The
definitions accept arbitrary vectors and weights; orthonormality and probability assumptions
enter later statements.

## Main statements

* `ketbra`: The rank-one matrix formed from two vectors.
* `gibbsBasis`: A weighted sum of rank-one basis operators.
* `braKetElem`: A matrix element between two vectors.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Matrix

variable {D : ℕ}

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

/-- The rank-one operator with entries `u i * star (v j)`. -/
noncomputable def ketbra (u v : QState (Fin D)) : Operator D :=
  Matrix.of fun i j => u i * star (v j)

/-- The sum of the rank-one operators of `ψ i`, weighted by the real coefficients `p i`. -/
noncomputable def gibbsBasis (ψ : Fin D → QState (Fin D)) (p : Fin D → ℝ) : Operator D :=
  ∑ i, p i • ketbra (ψ i) (ψ i)

/-- The matrix element `Inner u (X *ᵥ w)` of `X` between `u` and `w`. -/
noncomputable def braKetElem (X : Operator D) (u w : QState (Fin D)) : ℂ :=
  Inner u (X *ᵥ w)
end Qatlib.Concepts.QuantumGibbs.DetailedBalance
