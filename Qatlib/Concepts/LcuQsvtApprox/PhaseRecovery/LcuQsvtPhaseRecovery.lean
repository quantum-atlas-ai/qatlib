/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtDefs
import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPGily
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedLowc
import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc
import Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimCorrectedRestrictedLowc
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared

/-!
# Jacobi-Anger truncation and finite phase recovery

`g5` combines corrected Jacobi-Anger degree and tail estimates with a counted truncation
evaluator, exact finite inverse nonlinear Fourier recovery, and a source-word approximation
theorem. The inverse recovery conclusions require `LayerStripExact`; the source compilation
conclusions retain their parity, degree, symmetry, and approximation hypotheses.

These components support the quantum signal-processing approximation framework of
[LowChuang2017].

## Main statements

* `g5`: combine truncation accuracy, degree bounds, finite phase-recovery identities and costs,
  and source-word approximation.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.QspSimulation.SparseWalk
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.SparseSim
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 800000

open Matrix Polynomial
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib.Concepts.QspSimulation.SparseWalk Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.SignalPrimitive.SparseSim

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

namespace Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared in
open Qatlib.Concepts.QueryWordCore.AdjointCircuits in
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing in
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase in
open Qatlib.Concepts.QspSimulation.WordModel in
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing in
open Qatlib.Concepts.NonNormalSpec.ResolventWord in
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis in
open Matrix Polynomial in

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared in
open Qatlib.Concepts.QspSimulation.SparseWalk Qatlib.Concepts.PhaseGeometry.Phase in
open Qatlib.Concepts.QspSimulation.WordModel in
open Qatlib.Concepts.SignalPrimitive.SparseSim in
open Matrix Polynomial in

/-- Combines corrected Jacobi-Anger truncation with error at most `ε / 8`, explicit degree and
evaluation-count bounds, exact finite inverse nonlinear Fourier recovery under
`LayerStripExact`, and length-`N` source compilation with error at most `8 * ε` under the
stated polynomial hypotheses [LowChuang2017]. -/
theorem g5 :

  (∀ (τ ε : ℝ), 0 ≤ τ → 0 < ε → ε ≤ 1 →
    τ + 1 ≤ (lcCorrectedQ τ ε : ℝ) ∧
      ∀ θ : ℝ, ‖Complex.exp (Complex.I * (-(τ : ℂ) * ((Real.sin θ : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (lcCorrectedQ τ ε),
            (lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k))‖ ≤ ε / 8)

  ∧ (∀ (τ ε : ℝ), 0 ≤ τ → 0 < ε → ε ≤ 1 →
      3 * τ ≤ (lcCorrectedQ τ ε : ℝ) ∧
        (lcCorrectedQ τ ε : ℝ) ≤ 3 * τ + 3 * Real.log (32 / ε) + 8 ∧
        (lcCorrectedQ τ ε : ℝ) ≤
          4 * (Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1) + 2))

  ∧ (∀ (τ θ : ℝ) (q : ℕ), 0 ≤ τ →
      (lqJaTruncWithCount (fun k => lcBesselJ k τ) θ q).1
        = ∑ k ∈ Finset.range q, (lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) ∧
        (lqJaTruncWithCount (fun k => lcBesselJ k τ) θ q).2 ≤ lqJaTruncOpCount q)

  ∧ (∀ (A B : Polynomial ℂ) (n : ℕ), 1 ≤ n → LayerStripExact A B n →
      (inverseNLFFTFiniteSU2 A B n).gammas.length = n ∧
        (inverseNLFFTFiniteSU2 A B n).gammas = (layerStripSU2 A B n).gammas ∧
        (inverseNLFFTFiniteSU2 A B n).eta = (nlftSU2 (layerStripSU2 A B n).gammas).1 ∧
        (inverseNLFFTFiniteSU2 A B n).xi = (nlftSU2 (layerStripSU2 A B n).gammas).2 ∧
        (inverseNLFFTFiniteSU2 A B n).operations ≤ lqPhaseRecoveryOps n)

  ∧ (∀ (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (ε : ℝ), Even N → 0 < N →
      (∀ θ : ℝ, h (-θ) = -h θ) → A.comp (-X) = A → Qt.comp (-X) = -Qt →
      A.degree ≤ (N : WithBot ℕ) → Qt.degree < (N : WithBot ℕ) → 0 < ε → ε ≤ 1 / 16 →
      (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        ‖realEval A (Real.cos (θ / 2) : ℂ) +
            Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) *
              realEval Qt (Real.cos (θ / 2) : ℂ) -
            Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ ε) →
      ∃ phis : List ℝ, phis.length = N ∧
        ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
          ‖lcPlusAmp phis θ - Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ 8 * ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ ε hτ hε hε1
    obtain ⟨htail, hlen⟩ := jacobiAngerCorrectedDegree τ ε hτ hε hε1
    refine ⟨hlen, ?_⟩
    have hq1 : 1 ≤ lcCorrectedQ τ ε := by
      have h1 : (1 : ℝ) ≤ (lcCorrectedQ τ ε : ℝ) := by linarith
      exact_mod_cast h1
    have hqle : τ ≤ ((lcCorrectedQ τ ε - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hq1, Nat.cast_one]
      linarith
    intro θ
    have htail' := lcBesselJacobiAnger_tail (lcCorrectedQ τ ε) τ θ hτ hqle
    rw [Real.rpow_natCast τ (lcCorrectedQ τ ε),
      Real.rpow_natCast 2 (lcCorrectedQ τ ε)] at htail
    exact le_trans htail' htail
  · exact lcCorrectedQ_bounds
  · intro τ θ q hτ
    have hterm : ∀ k : ℕ, lqJaTerm (fun k => lcBesselJ k τ) θ k
        = lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k) := fun _ => rfl
    refine ⟨?_, le_refl _⟩
    show (lqJaTruncWithCount (fun k => lcBesselJ k τ) θ q).1
        = ∑ k ∈ Finset.range q, (lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k))
    simp only [lqJaTruncWithCount, lqJaTrunc]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  · intro A B n hn hhex
    obtain ⟨hg, he, hx⟩ := inverseNLFFTFiniteSU2_gammas A B n hhex
    exact ⟨inverseNLFFTFiniteSU2_gammas_length A B n, hg, he, hx,
      inverseNLFFTFiniteSU2_operations A B n hn⟩
  · intro N h A Qt ε hN hp hodd hAeven hQtodd hAdeg hQtdeg hεpos hε16 happrox
    exact lcSourceCompilation N h A Qt ε hN hp hodd hAeven hQtodd hAdeg hQtdeg hεpos
      hε16 happrox
end Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
