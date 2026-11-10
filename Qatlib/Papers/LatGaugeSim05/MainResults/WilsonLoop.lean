/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.LatGaugeSim05.MainResults

theorem u6_wilson_transcription {β : Type} [Fintype β] [DecidableEq β]
    (V0 V1 : Matrix β β ℂ) :
    (V0 * V1).trace = ∑ m1, ∑ m2, V0 m1 m2 * V1 m2 m1 := by

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem u6_wilson_transcription_three {β : Type} [Fintype β] [DecidableEq β]
    (V0 V1 V2 : Matrix β β ℂ) :
    (V0 * V1 * V2).trace =
      ∑ m1, ∑ m2, ∑ m3, V0 m1 m2 * V1 m2 m3 * V2 m3 m1 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]

def u6Eigenphase (θ : ℝ) : ℂ := Complex.exp ((-(θ : ℂ)) * Complex.I)

theorem u6Eigenphase_unit (θ : ℝ) : star (u6Eigenphase θ) * u6Eigenphase θ = 1 := by
  unfold u6Eigenphase
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) ((-(θ : ℂ)) * Complex.I) + (-(θ : ℂ)) * Complex.I = 0 := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [h, Complex.exp_zero]

theorem u6_diagonal_phase_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : ι → ℝ) :
    (Matrix.diagonal (fun i => u6Eigenphase (W i)))ᴴ *
      Matrix.diagonal (fun i => u6Eigenphase (W i)) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  funext i
  exact u6Eigenphase_unit (W i)

end Qatlib.Papers.LatGaugeSim05.MainResults
