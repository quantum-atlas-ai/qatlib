/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitSignal

/-!
# Chebyshev reflection-word specification

This module defines `Lemma9ChebyshevWord`, the proposition that the upper-left entry of a
reflection word with angles `chebyshevAngles d` equals the degree-`d` Chebyshev polynomial on
`[-1, 1]`. It isolates the statement associated with [GilyenSuLowWiebe2019] for use by its proof
module.

## Main statements

* `Lemma9ChebyshevWord`: the Chebyshev response identity for every natural order and every input
  in the unit interval.

## References

* [Gilyén et al., Lemma 9][GilyenSuLowWiebe2019]
-/

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial

/-- States that the `(0, 0)` entry of the reflection word with `chebyshevAngles d` is the
complex embedding of `T_d(x)` for every `x ∈ [-1, 1]`. -/
def Lemma9ChebyshevWord : Prop :=
  ∀ (d : ℕ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 →
    reflectionWord x (chebyshevAngles d) 0 0 =
      Complex.ofReal ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval x)

end Qatlib.Concepts.QsvtCore.PhaseExistence
