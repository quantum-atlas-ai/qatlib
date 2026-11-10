/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalance
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Matrix

variable {D : ℕ}

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

noncomputable def ketbra (u v : QState (Fin D)) : Operator D :=
  Matrix.of fun i j => u i * star (v j)

noncomputable def gibbsBasis (ψ : Fin D → QState (Fin D)) (p : Fin D → ℝ) : Operator D :=
  ∑ i, p i • ketbra (ψ i) (ψ i)

noncomputable def braKetElem (X : Operator D) (u w : QState (Fin D)) : ℂ :=
  Inner u (X *ᵥ w)
end Qatlib.Concepts.QuantumGibbs.DetailedBalance
