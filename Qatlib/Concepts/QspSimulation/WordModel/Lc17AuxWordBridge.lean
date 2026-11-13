/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeStat
import Qatlib.Concepts.QspSimulation.WordModel.Lc17AuxWord

/-!
# Telescoping phase rotations in QSP words

This module factors axis rotations into phase rotations around a signal step and telescopes
their products. `lcWordTilde` isolates the alternating signal-phase product used in the bridge
to `lcQspTilde`. Background and related constructions are discussed in [LowChuang2017].

## Main statements

* `lcAxisRotation_factor`: factors an axis rotation using endpoint phases.
* `lcWordTilde_eq_lcQspTilde`: identifies the alternating product with the QSP convention.
* `lcFold_telescope`: rewrites a nonempty product using phase half-differences.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix

namespace Qatlib.Concepts.QspSimulation.WordModel

/-- Multiplying phase rotations adds their real angles. -/
theorem lcPhaseRotation_mul (α β : ℝ) :
    Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation α * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation β =
      Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation, Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.mul_one, Matrix.one_mul, mul_ite, mul_zero]
  all_goals norm_num
  all_goals rw [← Complex.exp_add]
  all_goals congr 1
  all_goals ring

/-- The ordered product of factors consisting of the matrix `S` followed by a phase rotation at
each angle in `qs`. -/
noncomputable def lcWordTilde (S : Matrix (Fin 2) (Fin 2) ℂ) (qs : List ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (qs.map (fun q => S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q)).prod

/-- The alternating word with an empty phase list is the identity. -/
theorem lcWordTilde_nil (S : Matrix (Fin 2) (Fin 2) ℂ) : lcWordTilde S [] = 1 := rfl

/-- The alternating word for `q :: qs` factors as `S * PhaseRotation q` times the word for `qs`. -/
theorem lcWordTilde_cons (S : Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ) (qs : List ℝ) :
    lcWordTilde S (q :: qs) =
      (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q) * lcWordTilde S qs := by
  simp [lcWordTilde]

/-- When `S` is the conjugate transpose of `SignalMatrix x`, the alternating product
`lcWordTilde S qs` equals `lcQspTilde qs x`. -/
theorem lcWordTilde_eq_lcQspTilde {S : Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ}
    (hS : S = (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose) (qs : List ℝ) :
    lcWordTilde S qs = lcQspTilde qs x := by
  have h1 : qs.map (fun q => S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q)
      = qs.map (fun q => (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q) :=
    List.map_congr_left (fun q _ => by rw [hS])
  have h2 : ((qs.map (fun q =>
        (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q))).prod
      = ((qs.map (fun q =>
        (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q))).foldl (· * ·) 1 :=
    List.prod_eq_foldl
  calc lcWordTilde S qs
      = (qs.map (fun q => S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q)).prod := rfl
    _ = (qs.map (fun q => (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q)).prod := by rw [h1]
    _ = ((qs.map (fun q => (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q)).foldl (· * ·) 1) := h2
    _ = lcQspTilde qs x := rfl

/-- An axis rotation factors as a phase rotation by −φ/2, the signal step, and a phase rotation
by φ/2. -/
theorem lcAxisRotation_factor (φ θ : ℝ) :
    lcAxisRotation φ θ =
      Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(φ/2)) * (lcSignalStep θ *
        Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (φ/2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [lcSignalStep, lcAxisRotation, Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation,
      Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
  all_goals norm_num
  · have hz : Complex.exp (-(↑φ/2 * Complex.I)) * Complex.exp (↑φ/2 * Complex.I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination -(1 : ℂ) * Complex.cos (↑θ/2) * hz
  · have h2 : Complex.exp (-(↑φ/2 * Complex.I)) * Complex.exp (-(↑φ/2 * Complex.I))
        = Complex.exp (-(Complex.I * ↑φ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination -((1 : ℂ) * Complex.I * Complex.sin (↑θ/2)) * h2
  · have h2 : Complex.exp (↑φ/2 * Complex.I) * Complex.exp (↑φ/2 * Complex.I)
        = Complex.exp (Complex.I * ↑φ) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination -((1 : ℂ) * Complex.I * Complex.sin (↑θ/2)) * h2
  · have hz : Complex.exp (↑φ/2 * Complex.I) * Complex.exp (-(↑φ/2 * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    linear_combination -(1 : ℂ) * Complex.cos (↑θ/2) * hz

/-- Combines adjacent endpoint phase rotations into a rotation by `(a - c)/2` inside a product
of two conjugated signal factors. -/
private theorem lcTeleStep (S X : Matrix (Fin 2) (Fin 2) ℂ) (a c : ℝ) :
    (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) * (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2))) *
        (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(c/2)) * X) =
      Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
        ((S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2)) * X) := by
  have h : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2) * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(c/2)) =
      Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2) := by
    rw [lcPhaseRotation_mul]
    congr 1
    ring
  calc (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
          (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2))) *
          (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(c/2)) * X)
      = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
          (S * (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2) *
            (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(c/2)) * X))) := by
          simp only [Matrix.mul_assoc]
    _ = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
          (S * ((Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2) *
            Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(c/2))) * X)) := by
          rw [show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2) *
              (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(c/2)) * X) =
              (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2) *
                Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(c/2))) * X from
              (Matrix.mul_assoc _ _ _).symm]
    _ = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
          (S * (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2) * X)) := by rw [h]
    _ = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
          ((S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2)) * X) := by
          rw [show S * (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2) * X) =
              (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2)) * X from
              (Matrix.mul_assoc _ _ _).symm]

/-- A nonempty product of phase-conjugated copies of `S` telescopes into endpoint phase
rotations and `lcWordTilde` evaluated at the consecutive half-differences. -/
theorem lcFold_telescope (S : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ (rest : List ℝ) (a z : ℝ), (a :: rest).getLast (List.cons_ne_nil a rest) = z →
      ((a :: rest).map (fun φ =>
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(φ/2)) * (S *
            Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (φ/2)))).prod =
        Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
          (lcWordTilde S (lcHalfDiffs (a :: rest)) *
            (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (z/2))) := by
  intro rest
  induction rest with
  | nil =>
      intro a z hz
      simp only [List.getLast_singleton] at hz
      subst z
      simp only [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one,
        lcHalfDiffs, lcWordTilde_nil, one_mul]
  | cons c t' ih =>
      intro a z hz
      have hz' : (c :: t').getLast (List.cons_ne_nil c t') = z := by
        simpa [List.getLast_cons] using! hz
      have hd : lcHalfDiffs (a :: c :: t') = (a - c)/2 :: lcHalfDiffs (c :: t') := rfl
      change (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(a/2)) *
          (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (a/2))) *
        (((c :: t').map (fun φ =>
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(φ/2)) * (S *
            Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (φ/2)))).prod) = _
      rw [ih c z hz', hd, lcWordTilde_cons,
        show ((S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2)) *
              lcWordTilde S (lcHalfDiffs (c :: t'))) *
            (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (z/2)) =
            (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation ((a - c)/2)) *
              (lcWordTilde S (lcHalfDiffs (c :: t')) *
                (S * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (z/2))) from
            Matrix.mul_assoc _ _ _]
      exact lcTeleStep S _ a c
end Qatlib.Concepts.QspSimulation.WordModel
