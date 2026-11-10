/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.LatGaugeSim05.MainResults

def uNQubitCount (N M d D : ℕ) : ℕ := N * M * d * D

theorem uN_qubit_count_linear (N d D M : ℕ) :
    uNQubitCount N (M + 1) d D = uNQubitCount N M d D + N * (d * D) := by
  simp only [uNQubitCount]; ring

theorem uN_qubit_count_eq (N M d D : ℕ) :
    uNQubitCount N M d D = N * M * d * D := rfl

theorem uN_qubit_count_linear_in_M (N d D : ℕ) :
    ∀ M, uNQubitCount N (M + 1) d D = uNQubitCount N M d D + N * (d * D) :=
  fun M => uN_qubit_count_linear N d D M

def uNLocalOpCount (M d c : ℕ) : ℕ := c * (M * d)

def uNWorstOpCount (M d D c : ℕ) : ℕ := c * (M * d) * (M * d * D)

theorem uN_worst_op_count_quadratic (M d D c : ℕ) :
    uNWorstOpCount M d D c = c * M ^ 2 * d ^ 2 * D := by
  simp only [uNWorstOpCount]; ring

theorem uN_local_op_count_linear (d c : ℕ) (M : ℕ) :
    uNLocalOpCount (M + 1) d c = uNLocalOpCount M d c + c * d := by
  simp only [uNLocalOpCount]; ring

theorem uN_worst_is_terms_times_swaps (M d D c : ℕ) :
    uNWorstOpCount M d D c = (c * (M * d)) * (M * d * D) := by
  simp only [uNWorstOpCount]

theorem uNQubitCount_one (M d D : ℕ) :
    uNQubitCount 1 M d D = M * d * D := by
  simp only [uNQubitCount]; ring

theorem uNQubitCount_three (M d D : ℕ) :
    uNQubitCount 3 M d D = 3 * M * d * D := by
  simp only [uNQubitCount]

theorem uNQubitCount_eight (M d D : ℕ) :
    uNQubitCount 8 M d D = 8 * M * d * D := by
  simp only [uNQubitCount]

private theorem uN_hermitian_sum {H ι : Type*} [Fintype ι]
    (A : ι → Matrix H H ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    (∑ i, A i)ᴴ = ∑ i, A i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => hA i)

theorem uN_hamiltonian_form_hermitian {H : Type*} {Link Plaq : Type*}
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
    uN_hermitian_sum E hE, hA, hx]

end Qatlib.Papers.LatGaugeSim05.MainResults
