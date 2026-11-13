/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportStat

/-!
# Signal words as polynomial response matrices

`signalWordTransport` identifies the full single-qubit signal word with the matrix assembled
from `eq3Pair` and its coefficientwise conjugates. The off-diagonal entries carry the factor `I
* sqrt (1 - x^2)` for real signals in `[-1, 1]`. See [GilyenSuLowWiebe2019].

## Main statements

* `signalWordTransport`: prove the polynomial matrix formula for `signalWord`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-- For `x ∈ [-1, 1]`, the signal word equals the matrix of `eq3Pair` evaluations and their
conjugates, with off-diagonal factor `I * sqrt (1 - x^2)`. This is the signal-processing
matrix formula associated with [Gilyén et al., Theorem 3][GilyenSuLowWiebe2019]. -/
theorem signalWordTransport : SignalWordTransport := by
  intro z0 zs x hx
  have hs : (Real.sqrt (1 - x ^ 2) : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by
    have hn : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact_mod_cast Real.sq_sqrt hn
  induction zs using List.reverseRecOn with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [zPhaseGate]
  | append_singleton zs w ih =>
    rw [signalWord_snoc, eq3Pair_snoc, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eq3PairStep, signalRotation, zPhaseGate, Matrix.mul_apply, Fin.sum_univ_two,
        conjugatePolynomial_eval_real] <;>
      ring_nf <;> simp [hs, Complex.I_sq] <;> ring

end Qatlib.Concepts.QsvtCore.PhaseExistence
