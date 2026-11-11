/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-!
# Specification of lower polynomial completion

`Theorem4QCharacterization` specifies the completion criterion for a lower response polynomial.
It combines a strict degree bound, parity opposite to the length, a weighted squared-norm bound
on `[-1, 1]`, and an additional imaginary-axis condition for odd length. See
[GilyenSuLowWiebe2019].

## Main statements

* `Theorem4QCharacterization`: the lower response completion criterion.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Polynomial

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

/-- The lower-polynomial completion criterion of [Gilyén et al., Theorem
4][GilyenSuLowWiebe2019], using degree, parity, the weight `1 - x^2` on the real interval,
and an imaginary-axis condition for odd `k`. -/
def Theorem4QCharacterization : Prop :=
  ∀ (k : ℕ) (Q : Polynomial ℂ),
    (∃ P : Polynomial ℂ,
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair k P Q) ↔
      (Q.degree < (k : WithBot ℕ) ∧
        Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity (k + 1) Q ∧
        (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
          (1 - x ^ 2) * Complex.normSq (Q.eval (Complex.ofReal x)) ≤ 1) ∧
        (k % 2 = 1 → ∀ y : ℝ,
          1 ≤ (1 + y ^ 2) * Complex.normSq (Q.eval (Complex.ofReal y * Complex.I))))

end Qatlib.Concepts.QsvtCore.PhaseExistence
