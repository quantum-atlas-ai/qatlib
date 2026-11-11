/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# General lattice gauge resource identities

`uNQubitCount` uses a supplied model coefficient `N` to express a qubit count linear in lattice
size, with coefficients one, three, and eight recovered as special cases. The module also proves
the local and worst-case operation-count identities and Hermiticity of the general
electric-plus-plaquette Hamiltonian form. See [ByrnesYamamoto2006] for the paper context.

## Main statements

* `uN_qubit_count_linear`: Increasing `M` by one increases the general qubit count by `N * (d *
  D)`.
* `uN_worst_op_count_quadratic`: The general worst-case operation count equals `c * M ^ 2 * d ^
  2 * D`.
* `uN_hamiltonian_form_hermitian`: A Hermitian electric sum minus a real multiple of mutually
  adjoint plaquette sums is Hermitian.

## References

* [Byrnes and Yamamoto, 2006][ByrnesYamamoto2006]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.LatGaugeSim05.MainResults

/-- The general qubit-count formula `N * M * d * D` with supplied coefficient `N`. -/
def uNQubitCount (N M d D : ℕ) : ℕ := N * M * d * D

/-- Increasing `M` by one increases the general qubit count by `N * (d * D)`
[ByrnesYamamoto2006]. -/
theorem uN_qubit_count_linear (N d D M : ℕ) :
    uNQubitCount N (M + 1) d D = uNQubitCount N M d D + N * (d * D) := by
  simp only [uNQubitCount]; ring

/-- The general qubit count equals the product `N * M * d * D` [ByrnesYamamoto2006]. -/
theorem uN_qubit_count_eq (N M d D : ℕ) :
    uNQubitCount N M d D = N * M * d * D := rfl

/-- For every lattice size, the increment in the general qubit count is `N * (d * D)`
[ByrnesYamamoto2006]. -/
theorem uN_qubit_count_linear_in_M (N d D : ℕ) :
    ∀ M, uNQubitCount N (M + 1) d D = uNQubitCount N M d D + N * (d * D) :=
  fun M => uN_qubit_count_linear N d D M

/-- The general local-operation count `c * (M * d)`. -/
def uNLocalOpCount (M d c : ℕ) : ℕ := c * (M * d)

/-- The general worst-case operation count `c * (M * d) * (M * d * D)`. -/
def uNWorstOpCount (M d D c : ℕ) : ℕ := c * (M * d) * (M * d * D)

/-- The general worst-case operation count equals `c * M ^ 2 * d ^ 2 * D` [ByrnesYamamoto2006]. -/
theorem uN_worst_op_count_quadratic (M d D c : ℕ) :
    uNWorstOpCount M d D c = c * M ^ 2 * d ^ 2 * D := by
  simp only [uNWorstOpCount]; ring

/-- Increasing `M` by one increases the general local-operation count by `c * d`
[ByrnesYamamoto2006]. -/
theorem uN_local_op_count_linear (d c : ℕ) (M : ℕ) :
    uNLocalOpCount (M + 1) d c = uNLocalOpCount M d c + c * d := by
  simp only [uNLocalOpCount]; ring

/-- The general worst-case count factors into the term count `c * (M * d)` and the factor `M * d
* D` [ByrnesYamamoto2006]. -/
theorem uN_worst_is_terms_times_swaps (M d D c : ℕ) :
    uNWorstOpCount M d D c = (c * (M * d)) * (M * d * D) := by
  simp only [uNWorstOpCount]

/-- Coefficient one gives the qubit count `M * d * D` [ByrnesYamamoto2006]. -/
theorem uNQubitCount_one (M d D : ℕ) :
    uNQubitCount 1 M d D = M * d * D := by
  simp only [uNQubitCount]; ring

/-- Coefficient three gives the qubit count `3 * M * d * D` [ByrnesYamamoto2006]. -/
theorem uNQubitCount_three (M d D : ℕ) :
    uNQubitCount 3 M d D = 3 * M * d * D := by
  simp only [uNQubitCount]

/-- Coefficient eight gives the qubit count `8 * M * d * D` [ByrnesYamamoto2006]. -/
theorem uNQubitCount_eight (M d D : ℕ) :
    uNQubitCount 8 M d D = 8 * M * d * D := by
  simp only [uNQubitCount]

/-- A finite sum of Hermitian matrices is Hermitian. -/
private theorem uN_hermitian_sum {H ι : Type*} [Fintype ι]
    (A : ι → Matrix H H ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    (∑ i, A i)ᴴ = ∑ i, A i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => hA i)

/-- A Hermitian electric sum minus a real multiple of mutually adjoint plaquette sums is
Hermitian [ByrnesYamamoto2006]. -/
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
