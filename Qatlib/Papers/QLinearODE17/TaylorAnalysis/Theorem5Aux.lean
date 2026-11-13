/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.TaylorODESystem
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Triangular structure of the Taylor step matrix

This module proves the label-triangular structure and identity diagonal blocks of
`taylorStepMatrix`. These give determinant one and a two-sided inverse through
`taylorStepMatrix_det` and `taylorStepMatrix_inverse`. See [BerryEtAl2017ODE] for the paper's
setting.

## Main statements

* `taylorStepMatrix_above`: Entries of `taylorStepMatrix` vanish when the row label is smaller
  than the column label.
* `taylorStepMatrix_inverse`: The matrix inverse of `taylorStepMatrix` is a two-sided inverse.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix

variable {N : Type} [Fintype N] [DecidableEq N]

omit [Fintype N] in

/-- Entries of `taylorStepMatrix` vanish when the row label is smaller than the column label. -/
theorem taylorStepMatrix_above (m k p : ℕ) (M : Matrix N N ℂ)
    (r c : Fin (m * (k + 1) + p + 1) × N) (h : r.1 < c.1) :
    taylorStepMatrix m k p M r c = 0 := by
  have hne : r ≠ c := by intro he; subst c; exact lt_irrefl _ h
  have hprev : ¬ c.1.val + 1 = r.1.val := by omega
  have hclt : ¬ c.1.val < r.1.val := by omega
  simp [taylorStepMatrix, hne, hprev, hclt]

omit [Fintype N] in

/-- Each diagonal label block of `taylorStepMatrix` is the identity matrix on the state index. -/
theorem taylorStepMatrix_same_label (m k p : ℕ) (M : Matrix N N ℂ)
    (r c : Fin (m * (k + 1) + p + 1) × N) (h : r.1 = c.1) :
    taylorStepMatrix m k p M r c = if r.2 = c.2 then 1 else 0 := by
  simp [taylorStepMatrix, Prod.ext_iff, h]

/-- The determinant of `taylorStepMatrix` is one. -/
theorem taylorStepMatrix_det (m k p : ℕ) (M : Matrix N N ℂ) :
    (taylorStepMatrix m k p M).det = 1 := by
  let b : (Fin (m * (k + 1) + p + 1) × N) → OrderDual (Fin (m * (k + 1) + p + 1)) :=
    fun r => OrderDual.toDual r.1
  have htri : (taylorStepMatrix m k p M).BlockTriangular b := by
    intro r c hrc
    exact taylorStepMatrix_above m k p M r c hrc
  have hblock (l : OrderDual (Fin (m * (k + 1) + p + 1))) :
      (taylorStepMatrix m k p M).toSquareBlock b l = 1 := by
    ext r c
    have hlabel : r.val.1 = c.val.1 := r.property.trans c.property.symm
    have heq : r.val.2 = c.val.2 ↔ r = c := by
      constructor
      · intro hdata
        apply Subtype.ext
        exact Prod.ext hlabel hdata
      · intro he
        rw [he]
    change taylorStepMatrix m k p M r.val c.val = if r = c then 1 else 0
    rw [taylorStepMatrix_same_label m k p M r.val c.val hlabel]
    simp only [heq]
  rw [htri.det_fintype]
  apply Finset.prod_eq_one
  intro l _hl
  rw [hblock, Matrix.det_one]

/-- The matrix inverse of `taylorStepMatrix` is a two-sided inverse. -/
theorem taylorStepMatrix_inverse (m k p : ℕ) (M : Matrix N N ℂ) :
    taylorStepMatrix m k p M * (taylorStepMatrix m k p M)⁻¹ = 1 ∧
      (taylorStepMatrix m k p M)⁻¹ * taylorStepMatrix m k p M = 1 := by
  have hdet : IsUnit (taylorStepMatrix m k p M).det := by
    rw [taylorStepMatrix_det]
    exact isUnit_one
  exact ⟨Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
