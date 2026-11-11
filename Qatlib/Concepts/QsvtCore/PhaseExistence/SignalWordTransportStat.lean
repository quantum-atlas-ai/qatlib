/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitSignal

/-!
# Specification of signal word transport

`SignalWordTransport` specifies a matrix identity between a single-qubit signal word and the
response pair `eq3Pair`. It uses coefficientwise conjugation for the lower row and the real
square-root factor in the off-diagonal entries. See [GilyenSuLowWiebe2019].

## Main statements

* `SignalWordTransport`: the polynomial matrix formula on `[-1, 1]`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-- The assertion that every signal word on `[-1, 1]` equals the matrix assembled from its
`eq3Pair` polynomials, their coefficientwise conjugates, and the factor `I * sqrt (1 -
x^2)`. -/
def SignalWordTransport : Prop :=
  ∀ (z0 : ℂ) (zs : List ℂ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 →
    signalWord x z0 zs =
      !![(eq3Pair z0 zs).1.eval (x : ℂ),
         Complex.I * Real.sqrt (1 - x ^ 2) * (eq3Pair z0 zs).2.eval (x : ℂ);
         Complex.I * Real.sqrt (1 - x ^ 2) * (conjugatePolynomial (eq3Pair z0 zs).2).eval (x : ℂ),
         (conjugatePolynomial (eq3Pair z0 zs).1).eval (x : ℂ)]

end Qatlib.Concepts.QsvtCore.PhaseExistence
