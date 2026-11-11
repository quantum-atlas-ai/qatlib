/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.ActualCollision
import Qatlib.Papers.QMechSim97.MainResults.QLGAContinuum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# Diagonal collision modes and occupation exchange

This module verifies a diagonal collision representation on `2 * d` modes and the mass relation
used in the higher-dimensional discussion of [BoghosianTaylor1998]. Unit-modulus parameters
ensure unitarity of `dDimCollision`.

The explicit matrix `exchangeMatrix` swaps the two singly occupied basis labels. It is a unitary
involution and preserves particle-number sectors. The theorem `dDim_free_step_fragments`
packages the collision, mass, and exchange identities.

## Main statements

* `dDimCollision_unitary`: unitarity of the diagonal mode matrix.
* `massFromPhases_spec`: the coefficient identity for a nonzero defined mass.
* `exchangeMatrix_preserves_sector`: the exchange action preserves particle-number support.
* `dDim_free_step_fragments`: the combined collision, mass, and exchange identities.

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.DDimCollision

open Matrix
open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
open Qatlib.Papers.QMechSim97.MainResults.ActualCollision
open Complex

/-- The diagonal matrix on `2 * d` modes with entry `μ` at index zero, `ν` at indices from one
through `d`, and `lam` at larger indices. -/
def dDimCollision (d : ℕ) (μ ν lam : ℂ) : Matrix (Fin (2 * d)) (Fin (2 * d)) ℂ :=
  Matrix.diagonal (fun i =>
    if (i : ℕ) = 0 then μ else if (i : ℕ) ≤ d then ν else lam)

/-- An entry of `dDimCollision` is zero off the diagonal and equals the indicated mode parameter
on the diagonal. -/
theorem dDimCollision_apply (d : ℕ) (μ ν lam : ℂ) (i j : Fin (2 * d)) :
    dDimCollision d μ ν lam i j =
      if i = j then (if (i : ℕ) = 0 then μ else if (i : ℕ) ≤ d then ν else lam) else 0 := by
  simp [dDimCollision, Matrix.diagonal_apply]

/-- If `μ`, `ν`, and `lam` each have squared norm one, then `dDimCollision d μ ν lam` is
unitary. See [BoghosianTaylor1998]. -/
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

/-- If the defined mass is nonzero, its Schrödinger coefficient is `(ν / (μ - ν) + 1 / 2) / d`.
See [BoghosianTaylor1998]. -/
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

/-- The four-by-four matrix exchanging basis labels one and two and fixing labels zero and
three. -/
def exchangeMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

/-- The permutation matrix whose entry at `(i, j)` is one exactly when `σ j = i`. -/
def permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if σ j = i then 1 else 0

/-- The exchange matrix is the permutation matrix for the transposition of labels one and two.
See [BoghosianTaylor1998]. -/
theorem exchangeMatrix_eq_perm :
    exchangeMatrix = permMatrix (Equiv.swap (1 : Fin 4) 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchangeMatrix, permMatrix, Equiv.swap_apply_def]

/-- The exchange matrix is unitary. See [BoghosianTaylor1998]. -/
theorem exchangeMatrix_unitary :
    exchangeMatrix ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchangeMatrix, Matrix.mul_apply, Fin.sum_univ_four]

/-- The square of the exchange matrix is the identity. See [BoghosianTaylor1998]. -/
theorem exchangeMatrix_mul_self : exchangeMatrix * exchangeMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchangeMatrix, Matrix.mul_apply, Fin.sum_univ_four]

/-- The exchange matrix acts on vectors by swapping coordinates one and two. See
[BoghosianTaylor1998]. -/
theorem exchangeMatrix_mulVec (v : Fin 4 → ℂ) :
    exchangeMatrix.mulVec v = fun i => v (Equiv.swap (1 : Fin 4) 2 i) := by
  ext i
  fin_cases i <;>
    simp [exchangeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Equiv.swap_apply_def]

/-- Swapping basis labels one and two preserves `pairOccupation`. -/
theorem pairOccupation_swap (i : Fin 4) :
    pairOccupation (Equiv.swap (1 : Fin 4) 2 i) = pairOccupation i := by
  fin_cases i <;> simp [pairOccupation, Equiv.swap_apply_def]

/-- The exchange matrix has zero entries between labels of different particle counts. -/
theorem exchangeMatrix_off_sector (i j : Fin 4)
    (h : pairOccupation i ≠ pairOccupation j) : exchangeMatrix i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [exchangeMatrix, pairOccupation]

/-- If a vector vanishes outside particle-number sector `n`, then its image under the exchange
matrix also vanishes outside that sector. See [BoghosianTaylor1998]. -/
theorem exchangeMatrix_preserves_sector (n : ℕ) (v : Fin 4 → ℂ)
    (hv : ∀ j, pairOccupation j ≠ n → v j = 0) :
    ∀ i, pairOccupation i ≠ n → exchangeMatrix.mulVec v i = 0 := by
  intro i hi
  rw [exchangeMatrix_mulVec]
  exact hv _ (by rw [pairOccupation_swap]; exact hi)

/-- Under the unit-modulus and nonzero-mass hypotheses, the diagonal collision is unitary, the
mass coefficient identity holds, and the exchange matrix is a unitary involution with the
stated coordinate action. See [BoghosianTaylor1998]. -/
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
