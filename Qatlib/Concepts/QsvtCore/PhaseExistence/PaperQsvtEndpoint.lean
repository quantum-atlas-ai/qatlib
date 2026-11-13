/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.EffectiveBesselCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Qatlib.Concepts.QsvtCore.PhaseExistence.PaperQsvtEndpointDefs
import Qatlib.Concepts.QsvtCore.PhaseExistence.Ssvt
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.QsvtCore.PhaseExistence.SparseAccessConstruction
import Qatlib.Concepts.QspSimulation.Achievability.LcuQsvt
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtPhaseRecovery

/-!
# QSVT endpoint ledgers and rounded Bessel responses

This module connects source-word ledgers to aggregate resource counts for the QSVT constructions
of [GilyenSuLowWiebe2019]. It collects odd, even, controlled, and multiply controlled word
counts, sparse preparation counts, and finite phase-recovery guarantees under `LayerStripExact`.

The rounded Chebyshev–Bessel polynomials `roundedCos` and `roundedSin` use rational coefficient
tables. Their uniform errors split into the effective truncation error and a weighted
coefficient approximation budget.

## Main statements

* `clause45_endpoint`: the collected ledger and phase-recovery assertions.
* `paper_two_query_prepare`: the sparse encoding word counts.
* `paper_phase_recovery_clause`: conditional inverse-NLFFT guarantees.
* `paper_bessel_rounded_consumer`: uniform error at most `ε + β`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.QsvtCore.PhaseExistence.EffectiveBesselCutoff
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NativeNumerics.NlfftPipeline
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial
open Qatlib
open Qatlib

/-- The aggregated ledger for the odd source word equals `paperOddWordLedger` at the phase list
length. -/
theorem paper_odd_word_ledger (Φ : List ℝ) :
    paperLedger
      ((def15Ledger (def15Steps Φ .odd)).forwardQueries +
        (def15Ledger (def15Steps Φ .odd)).adjointQueries)
      ((def15Ledger (def15Steps Φ .odd)).projectorNotP +
        (def15Ledger (def15Steps Φ .odd)).projectorNotQ)
      (def15Ledger (def15Steps Φ .odd)).phaseMacros 1
      = paperOddWordLedger Φ.length := by
  obtain ⟨hF, hA, hP, hQ, hM⟩ := def15_ledger_components Φ
  simp only [paperLedger, paperOddWordLedger]
  rw [hF, hA, hP, hQ, hM]
  congr 1 <;> omega

/-- The aggregated ledger for the even source word equals `paperEvenWordLedger` at the phase
list length. -/
theorem paper_even_word_ledger (Φ : List ℝ) :
    paperLedger
      ((def15Ledger (def15Steps Φ .even)).forwardQueries +
        (def15Ledger (def15Steps Φ .even)).adjointQueries)
      ((def15Ledger (def15Steps Φ .even)).projectorNotP +
        (def15Ledger (def15Steps Φ .even)).projectorNotQ)
      (def15Ledger (def15Steps Φ .even)).phaseMacros 1
      = paperEvenWordLedger Φ.length := by
  obtain ⟨hF, hA, hP, hQ, hM⟩ := def15_ledger_components_even Φ
  simp only [paperLedger, paperEvenWordLedger]
  rw [hF, hA, hP, hQ, hM]
  congr 1 <;> omega

/-- Gives the even and odd endpoint formulas for the two projector-controlled NOT counts and
shows that their sum is `2d`. -/
theorem paper_projectorNot_parity (d : ℕ) :
    (d % 2 = 0 → 2 * (d / 2) = d ∧ 2 * ((d + 1) / 2) = d) ∧
    (d % 2 = 1 → 2 * (d / 2) = d - 1 ∧ 2 * ((d + 1) / 2) = d + 1) ∧
    (2 * (d / 2) + 2 * ((d + 1) / 2) = 2 * d) :=
  def15_parity_endpoints d

/-- The controlled odd source word has total query count `Φ.length`, twice as many
projector-controlled NOTs, `Φ.length` controlled phase gates, and workspace count one. -/
theorem paper_controlled_word_ledger (Φ : List ℝ) :
    paperLedger
      ((ctrlCounts (ctrlDef15Steps Φ .odd)).dataQueries +
        (ctrlCounts (ctrlDef15Steps Φ .odd)).adjointQueries)
      (ctrlCounts (ctrlDef15Steps Φ .odd)).projectorNots
      (ctrlCounts (ctrlDef15Steps Φ .odd)).controlledPhaseGates 1
      = paperLedger Φ.length (2 * Φ.length) Φ.length 1 := by
  obtain ⟨hD, hA, hP, hM, _⟩ := ctrlDef15_ledger_components_odd Φ
  simp only [paperLedger]
  rw [hD, hA, hP, hM]
  congr 1 <;> omega

/-- The multiply controlled source word has aggregated counts `d`, `2d`, `d`, and one for
queries, projector-controlled NOTs, multiply controlled phases, and workspace. -/
theorem paper_multiplyControlled_word_ledger {m : ℕ} (Φs : List (List ℝ))
    (d : ℕ) :
    paperLedger
      ((ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).dataQueries +
        (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).adjointQueries)
      (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).projectorNots
      (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).multiplyControlledPhaseGates 1
      = paperLedger d (2 * d) d 1 := by
  obtain ⟨hD, hA, hP, hM, _⟩ := mulCtrlDef15_ledger_components_odd (m := m) Φs d
  simp only [paperLedger]
  rw [hD, hA, hP, hM]
  congr 1 <;> omega

/-- Collects the odd, even, controlled, and multiply controlled source-word ledger identities,
sparse preparation counts, and conditional finite inverse-NLFFT phase recovery guarantees. -/
theorem clause45_endpoint :
    (∀ (Φ : List ℝ),
        paperLedger
          ((def15Ledger (def15Steps Φ .odd)).forwardQueries +
            (def15Ledger (def15Steps Φ .odd)).adjointQueries)
          ((def15Ledger (def15Steps Φ .odd)).projectorNotP +
            (def15Ledger (def15Steps Φ .odd)).projectorNotQ)
          (def15Ledger (def15Steps Φ .odd)).phaseMacros 1
          = paperOddWordLedger Φ.length) ∧
    (∀ (Φ : List ℝ),
        paperLedger
          ((def15Ledger (def15Steps Φ .even)).forwardQueries +
            (def15Ledger (def15Steps Φ .even)).adjointQueries)
          ((def15Ledger (def15Steps Φ .even)).projectorNotP +
            (def15Ledger (def15Steps Φ .even)).projectorNotQ)
          (def15Ledger (def15Steps Φ .even)).phaseMacros 1
          = paperEvenWordLedger Φ.length) ∧
    (∀ d : ℕ,
        (d % 2 = 0 → 2 * (d / 2) = d ∧ 2 * ((d + 1) / 2) = d) ∧
        (d % 2 = 1 → 2 * (d / 2) = d - 1 ∧ 2 * ((d + 1) / 2) = d + 1) ∧
        (2 * (d / 2) + 2 * ((d + 1) / 2) = 2 * d)) ∧
    (∀ (Φ : List ℝ),
        paperLedger
          ((ctrlCounts (ctrlDef15Steps Φ .odd)).dataQueries +
            (ctrlCounts (ctrlDef15Steps Φ .odd)).adjointQueries)
          (ctrlCounts (ctrlDef15Steps Φ .odd)).projectorNots
          (ctrlCounts (ctrlDef15Steps Φ .odd)).controlledPhaseGates 1
          = paperLedger Φ.length (2 * Φ.length) Φ.length 1) ∧
    (∀ (m : ℕ) (Φs : List (List ℝ)) (d : ℕ),
        paperLedger
          ((ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).dataQueries +
            (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).adjointQueries)
          (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).projectorNots
          (ctrlCounts (mulCtrlDef15Steps m Φs d .odd)).multiplyControlledPhaseGates 1
          = paperLedger d (2 * d) d 1) ∧

    (∀ (Φ : List ℝ),
        ctrlCounts (ctrlDef15Steps Φ .odd) =
          { dataQueries := (Φ.length + 1) / 2
            adjointQueries := Φ.length / 2
            projectorNots := 2 * (Φ.length / 2) + 2 * ((Φ.length + 1) / 2)
            phaseGates := 0
            controlledPhaseGates := Φ.length
            multiplyControlledPhaseGates := 0
            controlledDataQueries := 0
            controlledAdjointQueries := 0 }) ∧

    (Qatlib.Concepts.QsvtCore.PhaseExistence.rowQueryCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 1 ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.colQueryCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 1 ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.valueQueryCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 2 ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.gateStepCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 3) ∧

    (∀ (A B : Polynomial ℂ) (n : ℕ) (_h1 : 1 ≤ n)
        (_h2 : Qatlib.Concepts.NativeNumerics.NlfftPipeline.LayerStripExact A B n),
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).gammas.length = n ∧
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).gammas =
            (Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2 A B n).gammas ∧
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).eta =
            (Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2 (Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2 A B n).gammas).1 ∧
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).xi =
            (Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2 (Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2 A B n).gammas).2 ∧
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).operations ≤
            Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqPhaseRecoveryOps n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Φ; exact paper_odd_word_ledger Φ
  · intro Φ; exact paper_even_word_ledger Φ
  · intro d; exact paper_projectorNot_parity d
  · intro Φ; exact paper_controlled_word_ledger Φ
  · intro m Φs d; exact paper_multiplyControlled_word_ledger (m := m) Φs d
  · intro Φ; exact ctrlDef15_ledger_odd Φ
  · exact Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord_ledger
  · intro A B n h1 h2
    exact Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.g5.2.2.2.1 A B n h1 h2

/-- The sparse encoding word uses one row query, one column query, two value queries, and three
gate steps. -/
theorem paper_two_query_prepare :
    Qatlib.Concepts.QsvtCore.PhaseExistence.rowQueryCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 1 ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.colQueryCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 1 ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.valueQueryCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 2 ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.gateStepCount
        Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord = 3 :=
  Qatlib.Concepts.QsvtCore.PhaseExistence.encodingWord_ledger

/-- Under `LayerStripExact` and positive order, the finite inverse NLFFT returns `n`
layer-stripping parameters, reproduces the stated forward transform components, and meets
the phase-recovery operation bound. -/
theorem paper_phase_recovery_clause :
    ∀ (A B : Polynomial ℂ) (n : ℕ), 1 ≤ n →
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.LayerStripExact A B n →
      (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).gammas.length = n ∧
      (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).gammas =
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2 A B n).gammas ∧
      (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).eta =
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2 (Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2 A B n).gammas).1 ∧
      (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).xi =
        (Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2 (Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2 A B n).gammas).2 ∧
      (Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B n).operations ≤
        Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqPhaseRecoveryOps n := by
  intro A B n h1 h2
  exact Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.g5.2.2.2.1 A B n h1 h2

end Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QsvtCore.PhaseExistence.BesselCutoffRate
open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open scoped Classical BigOperators

/-- The even Chebyshev truncation using the rational coefficient table `J` in place of the
integral Bessel coefficients. -/
noncomputable def roundedCos (R : ℕ) (J : ℕ → ℚ) : Polynomial ℝ :=
  C (J 0 : ℝ)+∑ k ∈ Finset.Icc 1 R,
    C (2*(-1:ℝ)^k*(J (2*k):ℝ))*Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)

/-- The odd Chebyshev truncation using the rational coefficient table `J` in place of the
integral Bessel coefficients. -/
noncomputable def roundedSin (R : ℕ) (J : ℕ → ℚ) : Polynomial ℝ :=
  ∑ k ∈ Finset.Icc 0 R,
    C (2*(-1:ℝ)^k*(J (2*k+1):ℝ))*Polynomial.Chebyshev.T ℝ ((2*k+1:ℕ):ℤ)

/-- On `[-1, 1]`, changing the coefficients in the displayed finite Chebyshev sum changes its
value by at most twice the sum of absolute coefficient errors. -/
private theorem sparse_cheb_error (I : Finset ℕ) (n : ℕ → ℕ) (a b : ℕ → ℝ)
    (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    |(∑ k ∈ I, 2*(-1:ℝ)^k*a k*(Polynomial.Chebyshev.T ℝ (n k:ℤ)).eval x)-
      (∑ k ∈ I, 2*(-1:ℝ)^k*b k*(Polynomial.Chebyshev.T ℝ (n k:ℤ)).eval x)| ≤
      2*∑ k ∈ I, |a k-b k| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [show 2*(-1:ℝ)^k*a k*(Polynomial.Chebyshev.T ℝ (n k:ℤ)).eval x-
      2*(-1:ℝ)^k*b k*(Polynomial.Chebyshev.T ℝ (n k:ℤ)).eval x =
      2*(-1:ℝ)^k*(a k-b k)*(Polynomial.Chebyshev.T ℝ (n k:ℤ)).eval x by ring]
  have hc := Polynomial.Chebyshev.abs_eval_T_real_le_one (n k:ℤ) (abs_le.mpr hx)
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, show |(2:ℝ)|=2 by norm_num, mul_one] using!
    mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*|a k-b k| by positivity)

/-- The rounded cosine truncation differs from the integral-coefficient truncation by at most
the stated weighted sum of coefficient errors on `[-1, 1]`. -/
theorem roundedCos_error (t : ℝ) (R : ℕ) (J : ℕ → ℚ)
    (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    |(roundedCos R J).eval x-(compactCosPoly t R).eval x| ≤
      |(J 0:ℝ)-besselInt 0 t|+2*∑ k ∈ Finset.Icc 1 R, |(J (2*k):ℝ)-besselInt (2*k) t| := by
  simp only [roundedCos, compactCosPoly, eval_add, eval_finsetSum, eval_mul, eval_C]
  have h := sparse_cheb_error (Finset.Icc 1 R) (fun k => 2*k)
    (fun k => (J (2*k):ℝ)) (fun k => besselInt (2*k) t) x hx
  calc
    _ = |((J 0:ℝ)-besselInt 0 t)+
      ((∑ k ∈ Finset.Icc 1 R, 2*(-1:ℝ)^k*(J (2*k):ℝ)*(Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)).eval x)-
       (∑ k ∈ Finset.Icc 1 R, 2*(-1:ℝ)^k*besselInt (2*k) t*(Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)).eval x))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (le_refl _) h)

/-- The rounded sine truncation differs from the integral-coefficient truncation by at most
twice the sum of the odd coefficient errors on `[-1, 1]`. -/
theorem roundedSin_error (t : ℝ) (R : ℕ) (J : ℕ → ℚ)
    (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    |(roundedSin R J).eval x-(compactSinPoly t R).eval x| ≤
      2*∑ k ∈ Finset.Icc 0 R, |(J (2*k+1):ℝ)-besselInt (2*k+1) t| := by
  simp only [roundedSin, compactSinPoly, eval_finsetSum, eval_mul, eval_C]
  exact sparse_cheb_error (Finset.Icc 0 R) (fun k => 2*k+1)
    (fun k => (J (2*k+1):ℝ)) (fun k => besselInt (2*k+1) t) x hx

/-- At the effective cutoff, coefficient error budgets at most `β` give uniform cosine and sine
approximation errors at most `ε + β` on `[-1, 1]`. -/
theorem paper_bessel_rounded_consumer (t ε : ℚ) (hε : 0 < ε) (J : ℕ → ℚ) (β : ℝ)
    (hc : |(J 0:ℝ)-besselInt 0 (t:ℝ)|+
      2*∑ k ∈ Finset.Icc 1 (cutoff t ε hε), |(J (2*k):ℝ)-besselInt (2*k) (t:ℝ)| ≤ β)
    (hs : 2*∑ k ∈ Finset.Icc 0 (cutoff t ε hε), |(J (2*k+1):ℝ)-besselInt (2*k+1) (t:ℝ)| ≤ β) :
    ∀ x ∈ Set.Icc (-1:ℝ) 1,
      |Real.cos ((t:ℝ)*x)-(roundedCos (cutoff t ε hε) J).eval x| ≤ (ε:ℝ)+β ∧
      |Real.sin ((t:ℝ)*x)-(roundedSin (cutoff t ε hε) J).eval x| ≤ (ε:ℝ)+β := by
  intro x hx
  have hp := cutoff_polynomials t ε hε
  constructor
  · exact (abs_sub_le _ ((compactCosPoly (t:ℝ) (cutoff t ε hε)).eval x) _).trans
      (add_le_add (hp.2.2.2.2.1 x hx)
        (by rw [abs_sub_comm]; exact (roundedCos_error _ _ _ _ hx).trans hc))
  · exact (abs_sub_le _ ((compactSinPoly (t:ℝ) (cutoff t ε hε)).eval x) _).trans
      (add_le_add (hp.2.2.2.2.2 x hx)
        (by rw [abs_sub_comm]; exact (roundedSin_error _ _ _ _ hx).trans hs))

end Qatlib.Concepts.QsvtCore.PhaseExistence.BesselCutoffRate
