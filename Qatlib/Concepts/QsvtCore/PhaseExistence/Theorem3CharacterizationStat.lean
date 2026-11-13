/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge

/-!
# Specification of the polynomial pair characterization

`Theorem3Characterization` formulates the phase-realization criterion for quantum signal
processing polynomial pairs. It equates realization by a phase base and a list of length `k`
with degree bounds, response parities, and weighted squared-norm normalization on `[-1, 1]`. See
[GilyenSuLowWiebe2019].

## Main statements

* `Theorem3Characterization`: the phase-realization equivalence for a polynomial pair.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Polynomial

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

/-- The assertion that a phase realization of length `k` exists exactly for complex polynomial
pairs satisfying the degree, parity, and normalization conditions of [Gilyén et al., Theorem
3][GilyenSuLowWiebe2019]. -/
def Theorem3Characterization : Prop :=
  ∀ (k : ℕ) (P Q : Polynomial ℂ),
    (∃ base : ℂ, ∃ zs : List ℂ,
      Qatlib.Concepts.PhaseGeometry.Phase.IsPhase base ∧
      (∀ z ∈ zs, Qatlib.Concepts.PhaseGeometry.Phase.IsPhase z) ∧
      zs.length = k ∧
      Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP base zs = P ∧
      Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ base zs = Q) ↔
    (P.degree ≤ (k : WithBot ℕ) ∧ Q.degree < (k : WithBot ℕ) ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity k P ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity (k + 1) Q ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (Complex.ofReal x))
          + (1 - x ^ 2) * Complex.normSq (Q.eval (Complex.ofReal x)) = 1))

end Qatlib.Concepts.QsvtCore.PhaseExistence
