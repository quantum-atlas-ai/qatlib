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
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib.Concepts.QspSimulation.SparseWalk Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.SignalPrimitive.SparseSim

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.QsVtMain

namespace Qatlib.Concepts.LcuQsvtApprox.WordSynthesis
open scoped Matrix.Norms.L2Operator

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared in
open Qatlib.Concepts.LcuQsvtApprox.WordSynthesis Qatlib.Concepts.QueryWordCore.AdjointCircuits in
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing in
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel in
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing in
open Qatlib.Concepts.NonNormalSpec.ResolventWord in
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis in
open Matrix Polynomial in

theorem g3 :

  (∀ (z0 : ℂ) (zs : List ℂ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 →
    lqSignalWord x z0 zs = signalWord x z0 zs ∧
      lqSignalWord x z0 zs =
        !![(lqEq3Pair z0 zs).1.eval (x : ℂ),
           Complex.I * Real.sqrt (1 - x ^ 2) * (lqEq3Pair z0 zs).2.eval (x : ℂ);
           Complex.I * Real.sqrt (1 - x ^ 2) *
             (conjugatePolynomial (lqEq3Pair z0 zs).2).eval (x : ℂ),
           (conjugatePolynomial (lqEq3Pair z0 zs).1).eval (x : ℂ)] ∧
      ∀ (Φ : List ℝ), lqReflectionWord x Φ = reflectionWord x Φ)

  ∧ (∀ (n : ℕ) (P Q : Polynomial ℂ), Th3Pair n P Q →
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        (synthesizePair n P Q).2.length = n ∧
          lqReflectionWord x ((synthesizePair n P Q).2.map Complex.arg) 0 0 =
            star (synthesizePair n P Q).1 * P.eval (x : ℂ) ∧
          lqReflectionWord x ((synthesizePair n P Q).2.map Complex.arg) 1 0 =
            Real.sqrt (1 - x ^ 2) *
              (star (synthesizePair n P Q).1 * Q.eval (x : ℂ)))

  ∧ (∀ (p : Polynomial ℝ) (d : ℕ), 0 < d → p.degree ≤ (d : WithBot ℕ) →
      HasRealParity d p → (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
      ∃ Φ : List ℝ, Φ.length = d ∧ ∀ x : ℝ,
        ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x)

  ∧ (∀ (n : ℕ) (P Q : Polynomial ℂ),
      (∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
        zs.length = n ∧ responseP base zs = P ∧ responseQ base zs = Q) ↔
      Th3Pair n P Q)

  ∧ (∀ (n : ℕ) (P Q : Polynomial ℂ), Th3Pair n P Q →
      (lqSynthWithCount n P Q).1 = synthesizePair n P Q ∧
        (lqSynthWithCount n P Q).2 ≤ lqSynthOpCount n ∧
        IsPhase (synthesizePair n P Q).1 ∧
        (∀ z ∈ (synthesizePair n P Q).2, IsPhase z) ∧
        responseP (synthesizePair n P Q).1 (synthesizePair n P Q).2 = P ∧
        responseQ (synthesizePair n P Q).1 (synthesizePair n P Q).2 = Q)

  ∧ (∀ (φ φ' : List ℝ) (ε : ℝ), φ.length = φ'.length → 0 ≤ ε →
      (∀ p ∈ φ.zip φ', |p.1 - p.2| ≤ ε) →
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ (i j : Fin 2),
        ‖QSPWord φ x i j - QSPWord φ' x i j‖ ≤ 4 * (φ.length : ℝ) * ε)

  ∧ (∀ (k : ℕ) (Pt Qt : Polynomial ℝ),
      Pt.degree ≤ (k : WithBot ℕ) → Qt.degree < (k : WithBot ℕ) →
      HasRealParity k Pt → HasRealParity (k + 1) Qt →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, Pt.eval x ^ 2 + (1 - x ^ 2) * Qt.eval x ^ 2 ≤ 1) →
      ∃ (P Q : Polynomial ℂ), Th3Pair k P Q ∧
        P - conjugatePolynomial P = C (2 * Complex.I) * Pt.map Complex.ofRealHom ∧
        Q - conjugatePolynomial Q = C (2 * Complex.I) * Qt.map Complex.ofRealHom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z0 zs x hx
    exact ⟨by rfl, signalWordTransport z0 zs x hx, fun _ => rfl⟩
  · intro n P Q h x hx
    have h' : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair n P Q := h
    obtain ⟨hb, hzs, hp, hq⟩ :=
        Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.synthesizePair_correct h'
    have hlen :=
        Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.synthesizePair_length n P Q
    obtain ⟨t1, t2⟩ := singleQubitWordTransport
      ((synthesizePair n P Q).2.map Complex.arg) x hx
    have hmap : ((synthesizePair n P Q).2.map Complex.arg).map anglePhase
        = (synthesizePair n P Q).2 := by
      rw [List.map_map]
      calc (synthesizePair n P Q).2.map (anglePhase ∘ Complex.arg)
          = (synthesizePair n P Q).2.map id := by
            apply List.map_congr_left
            intro w hw
            exact anglePhase_arg_of_isPhase (hzs w hw)
        _ = (synthesizePair n P Q).2 := List.map_id _
    have hsrcP : sourcePhaseResponse ((synthesizePair n P Q).2.map Complex.arg)
        = C (star (synthesizePair n P Q).1) * P := by
      simp only [sourcePhaseResponse, hmap]
      calc responseP 1 (synthesizePair n P Q).2
          = C (star (synthesizePair n P Q).1)
              * responseP (synthesizePair n P Q).1 (synthesizePair n P Q).2 :=
            (responseP_one_of_phase hb _).1
        _ = C (star (synthesizePair n P Q).1) * P := by rw [hp]
    have hsrcQ : responseQ 1 (((synthesizePair n P Q).2.map Complex.arg).map anglePhase)
        = C (star (synthesizePair n P Q).1) * Q := by
      rw [hmap]
      calc responseQ 1 (synthesizePair n P Q).2
          = C (star (synthesizePair n P Q).1)
              * responseQ (synthesizePair n P Q).1 (synthesizePair n P Q).2 :=
            (responseP_one_of_phase hb _).2
        _ = C (star (synthesizePair n P Q).1) * Q := by rw [hq]
    refine ⟨hlen, ?_, ?_⟩
    · calc lqReflectionWord x ((synthesizePair n P Q).2.map Complex.arg) 0 0
          = reflectionWord x ((synthesizePair n P Q).2.map Complex.arg) 0 0 := by rfl
        _ = (sourcePhaseResponse ((synthesizePair n P Q).2.map Complex.arg)).eval (x : ℂ) :=
            t1
        _ = (C (star (synthesizePair n P Q).1) * P).eval (x : ℂ) := by rw [hsrcP]
        _ = star (synthesizePair n P Q).1 * P.eval (x : ℂ) := by simp
    · calc lqReflectionWord x ((synthesizePair n P Q).2.map Complex.arg) 1 0
          = reflectionWord x ((synthesizePair n P Q).2.map Complex.arg) 1 0 := by rfl
        _ = Real.sqrt (1 - x ^ 2)
              * (responseQ 1 (((synthesizePair n P Q).2.map Complex.arg).map anglePhase)).eval
                  (x : ℂ) := t2
        _ = Real.sqrt (1 - x ^ 2) * (C (star (synthesizePair n P Q).1) * Q).eval (x : ℂ) := by
            rw [hsrcQ]
        _ = Real.sqrt (1 - x ^ 2)
              * (star (synthesizePair n P Q).1 * Q.eval (x : ℂ)) := by simp
  · exact source_length_real_phase_existence
  · intro n P Q
    exact (Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.completedPair_iff_response).symm
  · intro n P Q h
    have h' : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair n P Q := h
    obtain ⟨hb, hzs, hp, hq⟩ :=
        Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.synthesizePair_correct h'
    exact ⟨rfl, lqSynthCount_le_of_completed n P Q h', hb, hzs, hp, hq⟩
  · intro φ φ' ε hlen hε hzip x hx i j
    exact qspWord_entry_lipschitz φ φ' ε hlen hε hzip hx i j
  · intro k Pt Qt hPdeg hQdeg hPpar hQpar hineq
    have hiff := theorem5RealCharacterization k Pt Qt
    obtain ⟨P, Q, hcomp, hP, hQ⟩ := hiff.mp ⟨hPdeg, hQdeg, hPpar, hQpar, hineq⟩
    have hI : (Complex.I : ℂ) ≠ 0 := by norm_num
    have hstarI : star (Complex.I : ℂ) = -(Complex.I : ℂ) := by simp [Complex.conj_I]
    have hII : Complex.I * (star (Complex.I : ℂ)) = 1 := by
      simp [hstarI, Complex.I_mul_I]
    refine ⟨C (Complex.I) * P, C (Complex.I) * Q, ?_, ?_, ?_⟩
    · have hdegP : (C (Complex.I) * P).degree ≤ (k : WithBot ℕ) := by
        rw [Polynomial.degree_C_mul hI]; exact hcomp.degreeP
      have hdegQ : (C (Complex.I) * Q).degree < (k : WithBot ℕ) := by
        rw [Polynomial.degree_C_mul hI]; exact hcomp.degreeQ
      have hparP : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity k (C (Complex.I) * P) := by
        have hstep : (C (Complex.I) * P).comp (-X) = C (Complex.I) * P.comp (-X) := by
          rw [mul_comp, C_comp]
        show (C (Complex.I) * P).comp (-X) = C ((-1 : ℂ) ^ k) * (C (Complex.I) * P)
        rw [hstep, hcomp.parityP]
        ring
      have hparQ : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity (k + 1) (C (Complex.I) * Q) := by
        have hstep : (C (Complex.I) * Q).comp (-X) = C (Complex.I) * Q.comp (-X) := by
          rw [mul_comp, C_comp]
        show (C (Complex.I) * Q).comp (-X) = C ((-1 : ℂ) ^ (k + 1)) * (C (Complex.I) * Q)
        rw [hstep, hcomp.parityQ]
        ring
      have hcP : conjugatePolynomial (C (Complex.I) * P)
          = C (star (Complex.I : ℂ)) * conjugatePolynomial P := by
        rw [conjugatePolynomial_mul, conjugatePolynomial_C]
      have hcQ : conjugatePolynomial (C (Complex.I) * Q)
          = C (star (Complex.I : ℂ)) * conjugatePolynomial Q := by
        rw [conjugatePolynomial_mul, conjugatePolynomial_C]
      have hredP : C (Complex.I) * P
            * (C (star (Complex.I : ℂ)) * conjugatePolynomial P)
          = P * conjugatePolynomial P := by
        calc C (Complex.I) * P
              * (C (star (Complex.I : ℂ)) * conjugatePolynomial P)
            = (C (Complex.I) * C (star (Complex.I : ℂ)))
                * (P * conjugatePolynomial P) := by ring
          _ = C (Complex.I * star (Complex.I : ℂ)) * (P * conjugatePolynomial P) := by
                rw [C_mul]
          _ = P * conjugatePolynomial P := by rw [hII, C_1, one_mul]
      have hredQ : C (Complex.I) * Q
            * (C (star (Complex.I : ℂ)) * conjugatePolynomial Q)
          = Q * conjugatePolynomial Q := by
        calc C (Complex.I) * Q
              * (C (star (Complex.I : ℂ)) * conjugatePolynomial Q)
            = (C (Complex.I) * C (star (Complex.I : ℂ)))
                * (Q * conjugatePolynomial Q) := by ring
          _ = C (Complex.I * star (Complex.I : ℂ)) * (Q * conjugatePolynomial Q) := by
                rw [C_mul]
          _ = Q * conjugatePolynomial Q := by rw [hII, C_1, one_mul]
      have hnorm : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.responsePairNorm (C (Complex.I) * P) (C (Complex.I) * Q) = 1 := by
        show (C (Complex.I) * P) * conjugatePolynomial (C (Complex.I) * P)
            + (1 - X ^ 2) * (C (Complex.I) * Q) * conjugatePolynomial (C (Complex.I) * Q) = 1
        have hredQ' : (1 - X ^ 2) * (C (Complex.I) * Q)
            * (C (star (Complex.I : ℂ)) * conjugatePolynomial Q)
            = (1 - X ^ 2) * Q * conjugatePolynomial Q := by
          rw [mul_assoc, hredQ]
          ring
        rw [hcP, hcQ, hredP, hredQ']
        exact hcomp.normalization
      exact ⟨hdegP, hdegQ, hparP, hparQ, hnorm⟩
    · have hcP : conjugatePolynomial (C (Complex.I) * P)
          = C (star (Complex.I : ℂ)) * conjugatePolynomial P := by
        rw [conjugatePolynomial_mul, conjugatePolynomial_C]
      have hnegC : C (star (Complex.I : ℂ)) = -(C (Complex.I : ℂ)) := by
        rw [hstarI, map_neg]
      calc C (Complex.I) * P - conjugatePolynomial (C (Complex.I) * P)
          = C (Complex.I) * P - C (star (Complex.I : ℂ)) * conjugatePolynomial P := by
            rw [hcP]
        _ = C (Complex.I) * P - (-(C (Complex.I))) * conjugatePolynomial P := by
            rw [hnegC]
        _ = C (Complex.I) * (P + conjugatePolynomial P) := by ring
        _ = C (Complex.I) * (C (2 : ℂ) * Pt.map Complex.ofRealHom) := by rw [hP]
        _ = C (2 * Complex.I) * Pt.map Complex.ofRealHom := by
            rw [C_mul]
            ring
    · have hcQ : conjugatePolynomial (C (Complex.I) * Q)
          = C (star (Complex.I : ℂ)) * conjugatePolynomial Q := by
        rw [conjugatePolynomial_mul, conjugatePolynomial_C]
      have hnegC : C (star (Complex.I : ℂ)) = -(C (Complex.I : ℂ)) := by
        rw [hstarI, map_neg]
      calc C (Complex.I) * Q - conjugatePolynomial (C (Complex.I) * Q)
          = C (Complex.I) * Q - C (star (Complex.I : ℂ)) * conjugatePolynomial Q := by
            rw [hcQ]
        _ = C (Complex.I) * Q - (-(C (Complex.I))) * conjugatePolynomial Q := by
            rw [hnegC]
        _ = C (Complex.I) * (Q + conjugatePolynomial Q) := by ring
        _ = C (Complex.I) * (C (2 : ℂ) * Qt.map Complex.ofRealHom) := by rw [hQ]
        _ = C (2 * Complex.I) * Qt.map Complex.ofRealHom := by
            rw [C_mul]
            ring
end Qatlib.Concepts.LcuQsvtApprox.WordSynthesis
