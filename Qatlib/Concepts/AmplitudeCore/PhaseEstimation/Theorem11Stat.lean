/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Operations
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Ampl
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Defs

/-!
# Specification of phase estimation concentration

`expected` collects the normalized phase estimation law, deterministic grid phase recovery, and
the off-grid outcome mass formula. It also specifies the circular tail bound and the nearest
grid window success bound. See [BrassardEtAl2002] for background.

## Main statements

* `expected`: The proposition collecting phase estimation normalization, exact grid phase
  recovery, off-grid sine and inverse square formulas, and the general and nearest circular
  window lower bounds.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

open scoped BigOperators Classical

open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Spec
/-- The proposition collecting phase estimation normalization, exact grid phase recovery,
off-grid sine and inverse square formulas, and the general and nearest circular window lower
bounds. -/
def expected : Prop :=
  (∀ (M : ℕ) (ω : ℝ),
  0 < M → 0 ≤ ω → ω < 1 →
  (∑ x : Fin M, bhmt11OutcomeMass M ω x) = 1 ∧
  ((∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) →
    ∃ x : Fin M, (x.val : ℝ) = (M : ℝ) * ω ∧
      bhmt11OutcomeMass M ω x = 1) ∧
  ((¬ ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) →
    ∀ x : Fin M,
      let Δ := bhmt11CircleDist ω ((x.val : ℝ) / (M : ℝ));
      bhmt11OutcomeMass M ω x =
        Real.sin ((M : ℝ) * Δ * Real.pi) ^ 2 /
          ((M : ℝ) ^ 2 * Real.sin (Δ * Real.pi) ^ 2) ∧
      bhmt11OutcomeMass M ω x ≤
        (1 : ℝ) / (2 * (M : ℝ) * Δ) ^ 2) ∧
  (∀ k : ℝ, 1 < k →
    1 - 1 / (2 * (k - 1)) ≤
      bhmt11WindowMass M ω (k / (M : ℝ))) ∧
  (2 < M →
    8 / Real.pi ^ 2 ≤ bhmt11WindowMass M ω (1 / (M : ℝ))))
end Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Spec
