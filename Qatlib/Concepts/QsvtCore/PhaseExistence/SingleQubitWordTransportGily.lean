/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportStat
set_option warningAsError false


open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

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
