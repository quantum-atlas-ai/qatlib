/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegistersDefs
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel

namespace Qatlib.Papers.LatGaugeSim05.MainResults

def u1lmax (D : ℕ) : ℕ := (2 ^ D - 1) / 2

abbrev U1Register (lmax : ℕ) := Fin (2 * lmax + 1)

def u1Value {lmax : ℕ} (i : U1Register lmax) : ℤ := (i : ℕ) - (lmax : ℤ)

def u1E2 (lmax : ℕ) : Matrix (U1Register lmax) (U1Register lmax) ℂ :=
  Matrix.diagonal (fun i => (((u1Value i : ℝ)) : ℂ) ^ 2)

def u1Lplus (lmax : ℕ) : Matrix (U1Register lmax) (U1Register lmax) ℂ :=
  Matrix.of (fun row col => if (row : ℕ) = (col : ℕ) + 1 then 1 else 0)

def u1Lminus (lmax : ℕ) : Matrix (U1Register lmax) (U1Register lmax) ℂ :=
  Matrix.of (fun row col => if (col : ℕ) = (row : ℕ) + 1 then 1 else 0)

theorem u1E2_eigen (lmax : ℕ) (i : U1Register lmax) :
    u1E2 lmax *ᵥ Pi.single i 1
      = ((((u1Value i : ℝ)) : ℂ) ^ 2) • Pi.single i 1 := by
  rw [u1E2, Matrix.diagonal_mulVec_single]
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem u1Lplus_apply (lmax : ℕ) (c : U1Register lmax) :
    u1Lplus lmax *ᵥ Pi.single c 1
      = fun (row : U1Register lmax) =>
          if (row : ℕ) = (c : ℕ) + 1 then (1 : ℂ) else 0 := by
  rw [Matrix.mulVec_single_one]
  funext row
  simp only [Matrix.col_apply, Matrix.of_apply, u1Lplus]

theorem u1Lminus_apply (lmax : ℕ) (c : U1Register lmax) :
    u1Lminus lmax *ᵥ Pi.single c 1
      = fun (row : U1Register lmax) =>
          if (c : ℕ) = (row : ℕ) + 1 then (1 : ℂ) else 0 := by
  rw [Matrix.mulVec_single_one]
  funext row
  simp only [Matrix.col_apply, Matrix.of_apply, u1Lminus]

theorem u1Lplus_apply_top (lmax : ℕ) (c : U1Register lmax)
    (h : (c : ℕ) + 1 = 2 * lmax + 1) :
    u1Lplus lmax *ᵥ Pi.single c 1 = 0 := by
  rw [u1Lplus_apply]
  funext row
  simp only [Pi.zero_apply]
  have hne : (row : ℕ) ≠ (c : ℕ) + 1 := by
    have := row.isLt
    omega
  simp [hne]

theorem u1Lminus_apply_bottom (lmax : ℕ) (c : U1Register lmax)
    (h : (c : ℕ) = 0) :
    u1Lminus lmax *ᵥ Pi.single c 1 = 0 := by
  rw [u1Lminus_apply]
  funext row
  simp only [Pi.zero_apply]
  have hne : (c : ℕ) ≠ (row : ℕ) + 1 := by omega
  simp [hne]

theorem u1Lplus_adjoint (lmax : ℕ) : (u1Lplus lmax)ᴴ = u1Lminus lmax := by
  ext row col
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, u1Lplus, u1Lminus]
  by_cases h : (col : ℕ) = (row : ℕ) + 1 <;> simp [h]

theorem u1E2_hermitian (lmax : ℕ) : (u1E2 lmax)ᴴ = u1E2 lmax := by
  ext i j
  simp only [u1E2, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

theorem u1Lminus_adjoint (lmax : ℕ) : (u1Lminus lmax)ᴴ = u1Lplus lmax := by
  rw [← u1Lplus_adjoint lmax, Matrix.conjTranspose_conjTranspose]

abbrev PlaquetteLink (lmax : ℕ) := ∀ _ : Fin 4, U1Register lmax

def u1ZFactor (lmax : ℕ) (i : Fin 4) :
    Matrix (U1Register lmax) (U1Register lmax) ℂ :=
  if i = 0 ∨ i = 1 then u1Lplus lmax else u1Lminus lmax

def u1ZdaggerFactor (lmax : ℕ) (i : Fin 4) :
    Matrix (U1Register lmax) (U1Register lmax) ℂ :=
  if i = 0 ∨ i = 1 then u1Lminus lmax else u1Lplus lmax

def u1PlaquetteZ (lmax : ℕ) :
    Matrix (PlaquetteLink lmax) (PlaquetteLink lmax) ℂ :=
  productMatrix (u1ZFactor lmax)

def u1PlaquetteZdaga (lmax : ℕ) :
    Matrix (PlaquetteLink lmax) (PlaquetteLink lmax) ℂ :=
  productMatrix (u1ZdaggerFactor lmax)

theorem u1PlaquetteZ_adjoint (lmax : ℕ) :
    (u1PlaquetteZ lmax)ᴴ = u1PlaquetteZdaga lmax := by
  rw [u1PlaquetteZ, u1PlaquetteZdaga, productMatrix_adjoint]
  congr 1
  funext i
  simp only [u1ZFactor, u1ZdaggerFactor]
  by_cases h : i = 0 ∨ i = 1
  · simp [h, u1Lplus_adjoint]
  · simp [h, u1Lminus_adjoint]

theorem u1PlaquetteZdaga_adjoint (lmax : ℕ) :
    (u1PlaquetteZdaga lmax)ᴴ = u1PlaquetteZ lmax := by
  rw [u1PlaquetteZdaga, u1PlaquetteZ, productMatrix_adjoint]
  congr 1
  funext i
  simp only [u1ZFactor, u1ZdaggerFactor]
  by_cases h : i = 0 ∨ i = 1
  · simp [h, u1Lminus_adjoint]
  · simp [h, u1Lplus_adjoint]

private theorem u1_hermitian_sum {H ι : Type*} [Fintype ι]
    (A : ι → Matrix H H ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    (∑ i, A i)ᴴ = ∑ i, A i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => hA i)

theorem u1_hamiltonian_hermitian {H : Type*} {Link Plaq : Type*}
    [Fintype Link] [Fintype Plaq]
    (E : Link → Matrix H H ℂ) (Z Zd : Plaq → Matrix H H ℂ) (x : ℝ)
    (hE : ∀ l, (E l)ᴴ = E l)
    (hZ : ∀ p, (Z p)ᴴ = Zd p) (hZd : ∀ p, (Zd p)ᴴ = Z p) :
    (((∑ l, E l) - (x : ℂ) • ((∑ p, Z p) + (∑ p, Zd p)))ᴴ)
      = (∑ l, E l) - (x : ℂ) • ((∑ p, Z p) + (∑ p, Zd p)) := by
  have hsumZ : (∑ p, Z p)ᴴ = ∑ p, Zd p := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun p _ => hZ p)
  have hsumZd : (∑ p, Zd p)ᴴ = ∑ p, Z p := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun p _ => hZd p)
  have hA : ((∑ p, Z p) + (∑ p, Zd p))ᴴ = (∑ p, Z p) + (∑ p, Zd p) := by
    rw [Matrix.conjTranspose_add, hsumZ, hsumZd]
    exact add_comm _ _
  have hx : star (x : ℂ) = (x : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    u1_hermitian_sum E hE, hA, hx]

def u1QubitCount (M d D : ℕ) : ℕ := M * d * D

def u1LocalOpCount (M d c : ℕ) : ℕ := c * (M * d)

def u1WorstOpCount (M d D c : ℕ) : ℕ := c * (M * d) * (M * d * D)

theorem u1_qubit_count_linear (d D : ℕ) (M : ℕ) :
    u1QubitCount (M + 1) d D = u1QubitCount M d D + d * D := by
  simp only [u1QubitCount]; ring

theorem u1_local_op_count_linear (d c : ℕ) (M : ℕ) :
    u1LocalOpCount (M + 1) d c = u1LocalOpCount M d c + c * d := by
  simp only [u1LocalOpCount]; ring

theorem u1_worst_op_count_quadratic (M d D c : ℕ) :
    u1WorstOpCount M d D c = c * M ^ 2 * d ^ 2 * D := by
  simp only [u1WorstOpCount]; ring

end Qatlib.Papers.LatGaugeSim05.MainResults
