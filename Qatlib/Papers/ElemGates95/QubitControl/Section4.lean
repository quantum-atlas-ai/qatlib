/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitEuler
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.ElemGates95.QubitControl.Section4

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

def paperPh (δ : ℝ) : Matrix Bool Bool ℂ := Complex.exp ((δ : ℂ) * Complex.I) • 1

abbrev paperRz (α : ℝ) : Matrix Bool Bool ℂ := qubitEulerPhase α

abbrev paperRy (θ : ℝ) : Matrix Bool Bool ℂ := qubitEulerRotation θ

theorem det_paperRz (α : ℝ) : (paperRz α).det = 1 := by
  have h : paperRz α = relabelGate boolEquivFin2.symm
      (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (α / 2)) := rfl
  rw [h, relabelGate, Matrix.det_reindex_self]
  rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation,
    Matrix.det_diagonal]
  rw [Fin.prod_univ_two]
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.isValue, if_true, if_neg h1]
  rw [← Complex.exp_add]
  have hz : ((α / 2 : ℝ) : ℂ) * Complex.I + (-((α / 2 : ℝ) : ℂ)) * Complex.I = 0 := by
    ring
  rw [hz, Complex.exp_zero]

theorem det_paperRy (θ : ℝ) : (paperRy θ).det = 1 := by
  show (qubitEulerRotation θ).det = 1
  rw [det_apply_bool]
  simp only [qubitEulerRotation, Matrix.of_apply]
  simp only [if_true, if_false, Bool.false_eq_true, Bool.true_eq_false]
  have h : ((Real.cos (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)
      - (Real.sin (θ / 2) : ℂ) * (-(Real.sin (θ / 2) : ℂ)))
      = ((Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Real.cos_sq_add_sin_sq]
  norm_num

theorem det_paperRz_mul_paperRy (α θ : ℝ) :
    (paperRz α * paperRy θ).det = 1 := by
  rw [Matrix.det_mul, det_paperRz, det_paperRy, one_mul]

theorem det_paperRy_mul_paperRz (θ β : ℝ) :
    (paperRy θ * paperRz β).det = 1 := by
  rw [Matrix.det_mul, det_paperRy, det_paperRz, one_mul]

theorem det_paperPh (δ : ℝ) : (paperPh δ).det = Complex.exp ((δ : ℂ) * Complex.I) ^ 2 := by
  simp [paperPh, Fintype.card_bool]

theorem lemma4_1 (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ δ α θ β : ℝ,
      U = Complex.exp ((δ : ℂ) * Complex.I) •
        (paperRz α * paperRy θ * paperRz β) := by
  let p := knownQubitAnglesOfUnitary U
  obtain ⟨hrec, -⟩ :=
    knownQubitEuler_explicit_angles_cover_unitaries U hU
  refine ⟨p.delta, p.alpha, p.theta, p.beta, ?_⟩
  show U = knownQubitUnitary p
  exact hrec.symm

theorem lemma4_1_special (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (hdet : U.det = 1) :
    ∃ α θ β : ℝ, U = paperRz α * paperRy θ * paperRz β := by
  obtain ⟨hrec, -⟩ :=
    knownQubitEuler_explicit_angles_cover_unitaries U hU
  let p := knownQubitAnglesOfUnitary U
  have hdelta : p.delta = 0 := by
    simp [p, knownQubitAnglesOfUnitary, hdet]
  have hshape : knownQubitUnitary p = paperRz p.alpha * paperRy p.theta * paperRz p.beta := by
    simp [knownQubitUnitary, hdelta]
  exact ⟨p.alpha, p.theta, p.beta, hrec.symm.trans hshape⟩

theorem lemma4_2 :
    (∀ θ₁ θ₂ : ℝ, paperRy θ₁ * paperRy θ₂ = paperRy (θ₁ + θ₂)) ∧
    (∀ α₁ α₂ : ℝ, paperRz α₁ * paperRz α₂ = paperRz (α₁ + α₂)) ∧
    (∀ δ₁ δ₂ : ℝ, paperPh δ₁ * paperPh δ₂ = paperPh (δ₁ + δ₂)) ∧
    (PauliX * PauliX = (1 : Matrix Bool Bool ℂ)) ∧
    (∀ θ : ℝ, PauliX * paperRy θ * PauliX = paperRy (-θ)) ∧
    (∀ α : ℝ, PauliX * paperRz α * PauliX = paperRz (-α)) := by
  obtain ⟨-, hrotphase, -⟩ := knownQubitEuler_primitives_and_algebra
  have hrot : ∀ θ₁ θ₂ : ℝ, paperRy θ₁ * paperRy θ₂ = paperRy (θ₁ + θ₂) :=
    fun s t => (hrotphase s t).1
  have hphase : ∀ α₁ α₂ : ℝ, paperRz α₁ * paperRz α₂ = paperRz (α₁ + α₂) :=
    fun s t => (hrotphase s t).2
  refine ⟨hrot, hphase, ?_, pauliX_mul_self, ?_, ?_⟩
  · intro δ₁ δ₂
    have hc : Complex.exp ((δ₁ : ℂ) * Complex.I) * Complex.exp ((δ₂ : ℂ) * Complex.I)
        = Complex.exp (((δ₁ + δ₂ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc paperPh δ₁ * paperPh δ₂
        = (Complex.exp ((δ₁ : ℂ) * Complex.I) * Complex.exp ((δ₂ : ℂ) * Complex.I))
            • (1 : Matrix Bool Bool ℂ) := by
          simp only [paperPh]
          rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]
          exact smul_smul _ _ _
      _ = paperPh (δ₁ + δ₂) := by
          simp only [paperPh]
          rw [hc]
  · intro θ
    exact pauliX_mul_qubitEulerRotation θ
  · intro α
    exact pauliX_mul_qubitEulerPhase α

theorem lemma4_3 (W : Matrix Bool Bool ℂ) (hW : W ∈ Matrix.unitaryGroup Bool ℂ)
    (hdet : W.det = 1) :
    ∃ A B C : Matrix Bool Bool ℂ,
      A ∈ Matrix.unitaryGroup Bool ℂ ∧ B ∈ Matrix.unitaryGroup Bool ℂ ∧
      C ∈ Matrix.unitaryGroup Bool ℂ ∧
      A.det = 1 ∧ B.det = 1 ∧ C.det = 1 ∧
      A * B * C = 1 ∧ A * PauliX * B * PauliX * C = W := by
  obtain ⟨hrec, -⟩ :=
    knownQubitEuler_explicit_angles_cover_unitaries W hW
  let p := knownQubitAnglesOfUnitary W
  have hdelta : p.delta = 0 := by
    simp [p, knownQubitAnglesOfUnitary, hdet]
  let A : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlA p)
  let B : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlB p)
  let C : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlC p)
  obtain ⟨hABC, hphase, -⟩ := knownQubitControl_ABC_phase_factorization p
  have hW : knownQubitUnitary p = W := hrec
  have hprod : A * PauliX * B * PauliX * C = W := by
    have h := hphase
    rw [hdelta] at h
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at h
    rw [h, hW]
  refine ⟨A, B, C, ?_, ?_, ?_, ?_, ?_, ?_, hABC, hprod⟩
  · exact knownQubitUnitary_unitary (knownControlA p)
  · exact knownQubitUnitary_unitary (knownControlB p)
  · exact knownQubitUnitary_unitary (knownControlC p)
  · have hA : A = paperRz p.alpha * paperRy (p.theta / 2) :=
      knownQubitUnitary_controlA p
    rw [hA]
    exact det_paperRz_mul_paperRy p.alpha (p.theta / 2)
  · have hB : B = paperRy (-p.theta / 2) * paperRz (-(p.alpha + p.beta) / 2) :=
      knownQubitUnitary_controlB p
    rw [hB]
    exact det_paperRy_mul_paperRz (-p.theta / 2) (-(p.alpha + p.beta) / 2)
  · have hC : C = paperRz ((p.beta - p.alpha) / 2) :=
      knownQubitUnitary_controlC p
    rw [hC]
    exact det_paperRz ((p.beta - p.alpha) / 2)

end Qatlib.Papers.ElemGates95.QubitControl.Section4
