/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.Macros
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

def SdpDualPayoffRange : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (α : ℝ),
    0 < D → 0 < α → 1 ≤ α →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α)) →
    ∀ s, (sdpDualPayoff D m A Cv α y s).IsHermitian ∧
      (0 : Operator D) ≤ sdpDualPayoff D m A Cv α y s ∧
      sdpDualPayoff D m A Cv α y s ≤ 1

end Qatlib.Concepts.SdpMmwSolver.SdpContract
