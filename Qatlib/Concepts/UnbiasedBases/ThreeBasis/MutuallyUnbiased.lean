/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open scoped Matrix

variable {d k : ℕ}

def OrthonormalColumns (B : Fin d → QState (Fin d)) : Prop :=
  ∀ i j, Qatlib.Foundations.PureStateMath.Inner (B i) (B j) = if i = j then 1 else 0

def IsFamily (B : Fin k → Fin d → QState (Fin d)) : Prop :=
  (∀ r, OrthonormalColumns (B r)) ∧
  ∀ r s, r ≠ s → ∀ i j,
    Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B r i) (B s j)) = (1 : ℝ) / d

noncomputable def applyCommonUnitary (U : Matrix (Fin d) (Fin d) ℂ)
    (B : Fin k → Fin d → QState (Fin d)) : Fin k → Fin d → QState (Fin d) :=
  fun r i => ApplyGate U (B r i)

theorem isFamily_applyCommonUnitary_iff
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (B : Fin k → Fin d → QState (Fin d)) :
    IsFamily (applyCommonUnitary U B) ↔ IsFamily B := by
  unfold IsFamily OrthonormalColumns applyCommonUnitary
  simp only [inner_applyGate hU]

theorem inner_ket_eq_coordinate (i : Fin d) (ψ : QState (Fin d)) :
    Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i) ψ = ψ i := by
  rw [inner_apply, Finset.sum_eq_single i]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro j _ hj
    simp [Qatlib.Foundations.PureStateMath.Ket, hj]
  · simp

theorem coordinate_normSq_of_ket_basis
    (B : Fin k → Fin d → QState (Fin d))
    (hB : IsFamily B) (r s : Fin k)
    (hr : ∀ i, B r i = Qatlib.Foundations.PureStateMath.Ket i) (hrs : r ≠ s)
    (i j : Fin d) :
    Complex.normSq (B s j i) = (1 : ℝ) / d := by
  have h := hB.2 r s hrs i j
  rw [hr i, inner_ket_eq_coordinate] at h
  exact h

theorem normalized_column {B : Fin d → QState (Fin d)}
    (hB : OrthonormalColumns B) (i : Fin d) : Normalized (B i) := by
  apply (normalized_iff_inner_self (B i)).mpr
  simpa using hB i i

theorem orthonormalColumns_ket : OrthonormalColumns (Qatlib.Foundations.PureStateMath.Ket : Fin d → QState (Fin d)) := by
  intro i j
  exact inner_ket_ket i j

noncomputable def columnMatrix (B : Fin d → QState (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ := fun i j => B j i

theorem columnMatrix_mem_unitary (B : Fin d → QState (Fin d))
    (hB : OrthonormalColumns B) :
    columnMatrix B ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  rw [Matrix.mul_apply]
  have h := hB i j
  rw [inner_apply] at h
  simpa only [Matrix.conjTranspose_apply, columnMatrix, Matrix.one_apply,
    RCLike.star_def] using h

theorem applyGate_columnMatrix_ket (B : Fin d → QState (Fin d)) (i : Fin d) :
    ApplyGate (columnMatrix B) (Qatlib.Foundations.PureStateMath.Ket i) = B i := by
  funext j
  simp [ApplyGate, Matrix.mulVec, dotProduct, columnMatrix,
      Qatlib.Foundations.PureStateMath.Ket]

theorem normalize_selected_basis (B : Fin k → Fin d → QState (Fin d))
    (hB : IsFamily B) (r : Fin k) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      IsFamily (applyCommonUnitary U B) ∧
      ∀ i, applyCommonUnitary U B r i = Qatlib.Foundations.PureStateMath.Ket i := by
  let A := columnMatrix (B r)
  have hA : (A)ᴴ * A = 1 := by
    have h := columnMatrix_mem_unitary (B r) (hB.1 r)
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hAdj : (A)ᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin d))).mp hA
  refine ⟨(A)ᴴ, hAdj, (isFamily_applyCommonUnitary_iff hAdj B).mpr hB, ?_⟩
  intro i
  change ApplyGate (A)ᴴ (B r i) = Qatlib.Foundations.PureStateMath.Ket i
  rw [← applyGate_columnMatrix_ket (B r) i]
  change ApplyGate (A)ᴴ
      (ApplyGate A (Qatlib.Foundations.PureStateMath.Ket i)) = Qatlib.Foundations.PureStateMath.Ket i
  rw [← applyGate_mul, hA, applyGate_one]

theorem columnMatrix_conjTranspose_mul_apply
    (B C : Fin d → QState (Fin d)) (i j : Fin d) :
    (((columnMatrix B)ᴴ * columnMatrix C) i j) = Qatlib.Foundations.PureStateMath.Inner (B i) (C j) := by
  rw [Matrix.mul_apply, inner_apply]
  simp only [Matrix.conjTranspose_apply, columnMatrix, RCLike.star_def]

theorem orthonormalColumns_of_unitary
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    OrthonormalColumns (fun j i => A i j) := by
  intro i j
  have hunit : Aᴴ * A = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff').mp hA
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) hunit
  change (Aᴴ * A) i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j at h
  rw [Matrix.one_apply] at h
  rw [inner_apply]
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def] using h

theorem normSq_inner_comm (ψ φ : QState (Fin d)) :
    Complex.normSq (Qatlib.Foundations.PureStateMath.Inner ψ φ) = Complex.normSq (Qatlib.Foundations.PureStateMath.Inner φ ψ) := by
  have hs : (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner ψ φ) = Qatlib.Foundations.PureStateMath.Inner φ ψ := by
    simp only [inner_apply, map_sum, map_mul, Complex.conj_conj]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    Complex.normSq (Qatlib.Foundations.PureStateMath.Inner ψ φ)
        = Complex.normSq ((starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner ψ φ)) := by
            rw [Complex.normSq_conj]
    _ = _ := congrArg Complex.normSq hs

theorem inner_matrixColumns (A C : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    Qatlib.Foundations.PureStateMath.Inner (fun t => A t i) (fun t => C t j) = (Aᴴ * C) i j := by
  simpa only [columnMatrix] using!
    (columnMatrix_conjTranspose_mul_apply
      (fun j t => A t j) (fun j t => C t j) i j).symm

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
