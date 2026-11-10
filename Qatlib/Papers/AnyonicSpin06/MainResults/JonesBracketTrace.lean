/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AnyonicSpin06.MainResults.JonesBracketTrace

open Matrix

def phiMatrix (A : ℂ) (Iexp : ℕ) (Pi : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  A ^ Iexp • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Pi

def bracketFromLoops (A : ℂ) (d : ℂ) (Iexp : ℕ)
    (Pi : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  A ^ Iexp * d ^ 2 + Matrix.trace Pi

theorem bracket_eq_trace_add (A d : ℂ) (Iexp : ℕ)
    (Pi : Matrix (Fin 2) (Fin 2) ℂ) :
    bracketFromLoops A d Iexp Pi
      = Matrix.trace (phiMatrix A Iexp Pi) + A ^ Iexp * (d ^ 2 - 2) := by
  unfold bracketFromLoops phiMatrix
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  simp [Fintype.card_fin]
  ring

theorem trace_eq_bracket_sub (A d : ℂ) (Iexp : ℕ)
    (Pi : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (phiMatrix A Iexp Pi)
      = bracketFromLoops A d Iexp Pi - A ^ Iexp * (d ^ 2 - 2) := by
  rw [bracket_eq_trace_add]
  ring

def U1 (d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d, 0; 0, 0]

def vvec (d : ℝ) : Fin 2 → ℝ :=
  ![d⁻¹, Real.sqrt (1 - (d⁻¹) ^ 2)]

def U2 (d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => d * vvec d i * vvec d j

theorem vvec_normSq {d : ℝ} (h : 0 ≤ 1 - (d⁻¹) ^ 2) :
    vvec d 0 * vvec d 0 + vvec d 1 * vvec d 1 = 1 := by
  simp only [vvec, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hs : Real.sqrt (1 - (d⁻¹) ^ 2) * Real.sqrt (1 - (d⁻¹) ^ 2)
      = 1 - (d⁻¹) ^ 2 := by
    rw [← pow_two, Real.sq_sqrt h]
  rw [hs]
  ring

theorem trace_U1 (d : ℝ) : Matrix.trace (U1 d) = d := by
  simp [U1, Matrix.trace, Fin.sum_univ_two]

theorem trace_U2 {d : ℝ} (hd : d ≠ 0) (h : 0 ≤ 1 - (d⁻¹) ^ 2) :
    Matrix.trace (U2 d) = d := by
  have hv := vvec_normSq (d := d) h
  simp only [U2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rw [show d * vvec d 0 * vvec d 0 + d * vvec d 1 * vvec d 1
        = d * (vvec d 0 * vvec d 0 + vvec d 1 * vvec d 1) by ring]
  rw [hv, mul_one]

theorem trace_U1_mul_U2 {d : ℝ} (hd : d ≠ 0) :
    Matrix.trace (U1 d * U2 d) = 1 := by
  rw [Matrix.trace_mul_comm]
  simp [U1, U2, vvec, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

end Qatlib.Papers.AnyonicSpin06.MainResults.JonesBracketTrace
