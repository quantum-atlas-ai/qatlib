/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5AltAux
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable def scalarKernelMatrix (m k p : ℕ) (z : ℂ) :
    Matrix (Fin (m * (k + 1) + p + 1)) (Fin (m * (k + 1) + p + 1)) ℂ :=
  fun r c => scalarKernelEntry m k z r.val c.val

noncomputable def scalarInverseMatrix (m k p : ℕ) (z : ℂ) :
    Matrix (Fin (m * (k + 1) + p + 1)) (Fin (m * (k + 1) + p + 1)) ℂ :=
  fun r c => scalarSolve m k p z (Pi.single c.val 1) r.val

theorem scalarKernelMatrix_mul_inverse (m k p : ℕ) (z : ℂ) (hm : 0 < m) :
    scalarKernelMatrix m k p z * scalarInverseMatrix m k p z = 1 := by
  classical
  ext r c
  have hs := scalarSolve_correct m k p z (Pi.single c.val 1) hm r.val r.isLt
  change (∑ l : Fin (m * (k + 1) + p + 1),
    scalarKernelEntry m k z r.val l.val *
      scalarSolve m k p z (Pi.single c.val 1) l.val) = _
  rw [show (∑ l : Fin (m * (k + 1) + p + 1),
      scalarKernelEntry m k z r.val l.val * scalarSolve m k p z (Pi.single c.val 1) l.val) =
      ∑ l ∈ Finset.range (m * (k + 1) + p + 1),
      scalarKernelEntry m k z r.val l * scalarSolve m k p z (Pi.single c.val 1) l from
      Fin.sum_univ_eq_sum_range (fun l => scalarKernelEntry m k z r.val l *
        scalarSolve m k p z (Pi.single c.val 1) l) (m * (k + 1) + p + 1)]
  rw [hs]
  simp [Matrix.one_apply, Pi.single_apply, Fin.ext_iff]

theorem scalarInverseMatrix_eq_inv (m k p : ℕ) (z : ℂ) (hm : 0 < m) :
    scalarInverseMatrix m k p z = (scalarKernelMatrix m k p z)⁻¹ :=
  (Matrix.inv_eq_right_inv (scalarKernelMatrix_mul_inverse m k p z hm)).symm

variable {N : Type} [Fintype N] [DecidableEq N]

omit [Fintype N] in

theorem taylorStepMatrixV2_diag_entry (m k p : ℕ) (D : Matrix N N ℂ)
    (hd : ∀ i j : N, i ≠ j → D i j = 0)
    (r c : Fin (m * (k + 1) + p + 1) × N) :
    taylorStepMatrixV2 m k p D r c =
      if r.2 = c.2 then scalarKernelEntry m k (D r.2 r.2) r.1.val c.1.val else 0 := by
  classical
  rcases r with ⟨rl, rn⟩
  rcases c with ⟨cl, cn⟩
  by_cases he : rn = cn
  · subst cn
    simp [taylorStepMatrixV2, scalarKernelEntry, Prod.ext_iff, Fin.ext_iff]
  · simp [taylorStepMatrixV2, he, hd rn cn he, Prod.ext_iff]

noncomputable def taylorV2InvDiag (m k p : ℕ) (D : Matrix N N ℂ) :
    Matrix (Fin (m * (k + 1) + p + 1) × N) (Fin (m * (k + 1) + p + 1) × N) ℂ :=
  Matrix.blockDiagonal (fun n : N => scalarInverseMatrix m k p (D n n))

omit [Fintype N] in

theorem taylorStepMatrixV2_blockDiagonal (m k p : ℕ) (D : Matrix N N ℂ)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) :
    taylorStepMatrixV2 m k p D =
      Matrix.blockDiagonal (fun n : N => scalarKernelMatrix m k p (D n n)) := by
  ext r c
  rw [taylorStepMatrixV2_diag_entry m k p D hd, Matrix.blockDiagonal_apply]
  rfl

theorem taylorV2_diag_mul_inv (m k p : ℕ) (D : Matrix N N ℂ) (hm : 0 < m)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) :
    taylorStepMatrixV2 m k p D * taylorV2InvDiag m k p D = 1 := by
  rw [taylorStepMatrixV2_blockDiagonal m k p D hd, taylorV2InvDiag,
    ← Matrix.blockDiagonal_mul]
  simp only [scalarKernelMatrix_mul_inverse m k p _ hm]
  ext r c
  simp only [Matrix.blockDiagonal_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem taylorV2InvDiag_eq_inv (m k p : ℕ) (D : Matrix N N ℂ) (hm : 0 < m)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) :
    taylorV2InvDiag m k p D = (taylorStepMatrixV2 m k p D)⁻¹ :=
  (Matrix.inv_eq_right_inv (taylorV2_diag_mul_inv m k p D hm hd)).symm

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
