/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportStat

/-!
# Reflection word response entries

`singleQubitWordTransport` proves the two entry formulas in `SingleQubitWordTransport` for the
reflection-based signal-processing word. The upper entry is `sourcePhaseResponse`, while the
lower entry is the lower response polynomial multiplied by `sqrt (1 - x^2)`. See
[GilyenSuLowWiebe2019].

## Main statements

* `singleQubitWordTransport`: identify the first column of the reflection word.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false


open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- For signals in `[-1, 1]`, the first column of the reflection word is given by
`sourcePhaseResponse` and the square-root-weighted lower response polynomial, as in [Gilyén
et al., Corollary 8][GilyenSuLowWiebe2019]. -/
theorem singleQubitWordTransport : SingleQubitWordTransport := by
  intro Φ x hx
  have hs : (Real.sqrt (1 - x ^ 2) : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by
    have hn : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact_mod_cast Real.sq_sqrt hn
  change reflectionWord x Φ 0 0 = (responseP 1 (Φ.map anglePhase)).eval (x : ℂ) ∧ _
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    simp only [reflectionWord_cons, List.map_cons, responseP_cons, responseQ_cons,
      eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_one, eval_pow]
    simp [Matrix.mul_apply, Fin.sum_univ_two, zPhaseGate, signalReflection, ih.1, ih.2]
    constructor
    · linear_combination anglePhase φ * (responseQ 1 (Φ.map anglePhase)).eval (x : ℂ) * hs
    · ring

end Qatlib.Concepts.QsvtCore.PhaseExistence
