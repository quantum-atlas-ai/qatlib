/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support

/-!
# Specification of Jacobi–Anger truncation

`JacobiAngerTruncation` states the existence of an even polynomial A and an odd polynomial Qt
whose trigonometric response approximates exp(−iτ sin θ). It records the degree restrictions and
factorial error bound for 0 ≤ τ ≤ q − 1 used in QSP Hamiltonian simulation [LowChuang2017].

## Main statements

* `JacobiAngerTruncation`: The parity, degree, and uniform approximation requirements for a
  truncated response pair.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.JacobiAnger

open Polynomial

/-- The proposition that for q ≥ 1 and 0 ≤ τ ≤ q − 1, even A and odd Qt exist with degrees at
most and strictly below 2(q − 1), respectively, and trigonometric response error at most
4τ^q/(2^q q!) for θ in [0, 2π]. -/
def JacobiAngerTruncation : Prop :=
  ∀ (q : ℕ) (τ : ℝ), 1 ≤ q → 0 ≤ τ → τ ≤ ((q - 1 : ℕ) : ℝ) →
    ∃ (A Qt : Polynomial ℝ),
      A.comp (-X) = A ∧ Qt.comp (-X) = -Qt ∧
      A.degree ≤ ((2 * (q - 1) : ℕ) : WithBot ℕ) ∧
      Qt.degree < ((2 * (q - 1) : ℕ) : WithBot ℕ) ∧
      (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        ‖((realEval A (Complex.ofReal (Real.cos (θ/2))))
            + Complex.I * ((Real.sin (θ/2) : ℝ) : ℂ) * (realEval Qt (Complex.ofReal (Real.cos (θ/2))))
            - Complex.exp (Complex.I * (-(τ : ℂ) * (Real.sin θ : ℂ))))‖
          ≤ 4 * τ ^ (q : ℝ) / (2 ^ (q : ℝ) * (q.factorial : ℝ)))

end Qatlib.Concepts.QspSimulation.JacobiAnger
