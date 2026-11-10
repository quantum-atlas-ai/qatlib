/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.ActualCollision
import Qatlib.Papers.QMechSim97.MainResults.QLGAContinuum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.DDimCollision

open Matrix
open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
open Qatlib.Papers.QMechSim97.MainResults.ActualCollision
open Complex

def dDimCollision (d : ℕ) (μ ν lam : ℂ) : Matrix (Fin (2 * d)) (Fin (2 * d)) ℂ :=
  Matrix.diagonal (fun i =>
    if (i : ℕ) = 0 then μ else if (i : ℕ) ≤ d then ν else lam)

theorem dDimCollision_apply (d : ℕ) (μ ν lam : ℂ) (i j : Fin (2 * d)) :
    dDimCollision d μ ν lam i j =
      if i = j then (if (i : ℕ) = 0 then μ else if (i : ℕ) ≤ d then ν else lam) else 0 := by
  simp [dDimCollision, Matrix.diagonal_apply]

theorem dDimCollision_unitary (d : ℕ) (μ ν lam : ℂ)
    (hμ : Complex.normSq μ = 1) (hν : Complex.normSq ν = 1) (hlam : Complex.normSq lam = 1) :
    dDimCollision d μ ν lam ∈ Matrix.unitaryGroup (Fin (2 * d)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  unfold dDimCollision
  apply diagonal_phase_unitary
  intro i
  by_cases h0 : (i : ℕ) = 0
  · simp [h0, hμ]
  · by_cases hd : (i : ℕ) ≤ d
    · simp [h0, hd, hν]
    · simp [h0, hd, hlam]

theorem massFromPhases_spec (d : ℕ) (μ ν : ℂ)
    (hm : massFromPhases d μ ν ≠ 0) :
    I / (2 * massFromPhases d μ ν) = (ν / (μ - ν) + 1 / 2) / (d : ℂ) := by
  set X : ℂ := (ν / (μ - ν) + 1 / 2) / (d : ℂ) with hXdef
  have hX : X ≠ 0 := by
    intro hx
    apply hm
    rw [massFromPhases, hXdef] at *
    rw [hx]
    simp
  rw [massFromPhases]
  rw [hXdef] at hX ⊢
  field_simp [hX]

def exchangeMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

def permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if σ j = i then 1 else 0

theorem exchangeMatrix_eq_perm :
    exchangeMatrix = permMatrix (Equiv.swap (1 : Fin 4) 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchangeMatrix, permMatrix, Equiv.swap_apply_def]

theorem exchangeMatrix_unitary :
    exchangeMatrix ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchangeMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem exchangeMatrix_mul_self : exchangeMatrix * exchangeMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchangeMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem exchangeMatrix_mulVec (v : Fin 4 → ℂ) :
    exchangeMatrix.mulVec v = fun i => v (Equiv.swap (1 : Fin 4) 2 i) := by
  ext i
  fin_cases i <;>
    simp [exchangeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Equiv.swap_apply_def]

theorem pairOccupation_swap (i : Fin 4) :
    pairOccupation (Equiv.swap (1 : Fin 4) 2 i) = pairOccupation i := by
  fin_cases i <;> simp [pairOccupation, Equiv.swap_apply_def]

theorem exchangeMatrix_off_sector (i j : Fin 4)
    (h : pairOccupation i ≠ pairOccupation j) : exchangeMatrix i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [exchangeMatrix, pairOccupation]

theorem exchangeMatrix_preserves_sector (n : ℕ) (v : Fin 4 → ℂ)
    (hv : ∀ j, pairOccupation j ≠ n → v j = 0) :
    ∀ i, pairOccupation i ≠ n → exchangeMatrix.mulVec v i = 0 := by
  intro i hi
  rw [exchangeMatrix_mulVec]
  exact hv _ (by rw [pairOccupation_swap]; exact hi)

theorem dDim_free_step_fragments (d : ℕ) (μ ν lam : ℂ)
    (hμ : Complex.normSq μ = 1) (hν : Complex.normSq ν = 1) (hlam : Complex.normSq lam = 1)
    (hm : massFromPhases d μ ν ≠ 0) :
    dDimCollision d μ ν lam ∈ Matrix.unitaryGroup (Fin (2 * d)) ℂ ∧
    I / (2 * massFromPhases d μ ν) = (ν / (μ - ν) + 1 / 2) / (d : ℂ) ∧
    exchangeMatrix ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    exchangeMatrix * exchangeMatrix = 1 ∧
    (∀ v : Fin 4 → ℂ,
      exchangeMatrix.mulVec v = fun i => v (Equiv.swap (1 : Fin 4) 2 i)) :=
  ⟨dDimCollision_unitary d μ ν lam hμ hν hlam, massFromPhases_spec d μ ν hm,
    exchangeMatrix_unitary, exchangeMatrix_mul_self, exchangeMatrix_mulVec⟩

end Qatlib.Papers.QMechSim97.MainResults.DDimCollision
