/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitSignal
set_option warningAsError false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial

def Lemma9ChebyshevWord : Prop :=
  ∀ (d : ℕ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 →
    reflectionWord x (chebyshevAngles d) 0 0 =
      Complex.ofReal ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval x)

end Qatlib.Concepts.QsvtCore.PhaseExistence
