/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-!
# Specification of upper polynomial completion

`Theorem4PCharacterization` specifies when an upper response polynomial possesses a partner
making a `CompletedPair`. Besides degree and parity, the criterion controls its squared norm
inside and outside the real unit interval and, for even length, on the imaginary axis. See
[GilyenSuLowWiebe2019].

## Main statements

* `Theorem4PCharacterization`: the upper response completion criterion.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Polynomial

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

/-- The upper-polynomial completion criterion of [Gilyén et al., Theorem
4][GilyenSuLowWiebe2019], expressed through degree, parity, real-axis squared-norm bounds,
and an imaginary-axis bound when `k` is even. -/
def Theorem4PCharacterization : Prop :=
  ∀ (k : ℕ) (P : Polynomial ℂ),
    (∃ Q : Polynomial ℂ,
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair k P Q) ↔
      (P.degree ≤ (k : WithBot ℕ) ∧
        Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity k P ∧
        (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
          Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1) ∧
        (∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
          1 ≤ Complex.normSq (P.eval (Complex.ofReal x))) ∧
        (k % 2 = 0 → ∀ y : ℝ,
          1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))))

end Qatlib.Concepts.QsvtCore.PhaseExistence
