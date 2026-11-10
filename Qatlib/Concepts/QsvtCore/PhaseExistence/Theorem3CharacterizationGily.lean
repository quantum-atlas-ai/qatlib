/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3CharacterizationStat
set_option warningAsError false

open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

private theorem pair_norm_eval (P Q : Polynomial ℂ) (x : ℝ) :
    (responsePairNorm P Q).eval (x : ℂ) =
      Complex.ofReal (Complex.normSq (P.eval (x : ℂ)) +
        (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ))) := by
  simp only [responsePairNorm, eval_add, eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, conjugatePolynomial_eval_real]
  simp only [Complex.star_def]
  rw [mul_assoc (1 - (x : ℂ) ^ 2), Complex.mul_conj, Complex.mul_conj]
  simp

theorem theorem3Characterization : Theorem3Characterization := by
  intro k P Q
  rw [← completedPair_iff_response]
  constructor
  · intro h
    refine ⟨h.degreeP, h.degreeQ, h.parityP, h.parityQ, ?_⟩
    intro x _
    have he := congrArg (fun p : Polynomial ℂ => (p.eval (x : ℂ)).re) h.normalization
    simpa only [pair_norm_eval, Complex.ofReal_re, eval_one, Complex.one_re] using he
  · rintro ⟨hp, hq, hpp, hqp, hn⟩
    refine ⟨hp, hq, hpp, hqp, ?_⟩
    apply Polynomial.eq_of_infinite_eval_eq
    have hi : Set.Infinite (Set.Icc (-1 : ℝ) 1) := Set.Icc_infinite (by norm_num)
    apply (hi.image Complex.ofReal_injective.injOn).mono
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq, pair_norm_eval, eval_one]
    rw [hn x hx, Complex.ofReal_one]

end Qatlib.Concepts.QsvtCore.PhaseExistence
