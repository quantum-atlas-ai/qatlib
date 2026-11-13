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

/-!
# SU(3) electric and plaquette operators

`u3dim` and `u3E2val` encode the SU(3) representation-dimension and electric-eigenvalue
formulas, and `u3E2` realizes the latter diagonally on a bounded label register. The
constructions `u3PlaquetteZ` and `u3PlaquetteZdag` have the stated adjoint relation under local
adjoint hypotheses; Hamiltonian Hermiticity and resource identities are also proved. See
[ByrnesYamamoto2006] for the paper context.

## Main statements

* `u3E2_eigen`: Every coordinate basis vector of the SU(3) register has electric eigenvalue
  given by `u3E2val` at its labels.
* `u3_plaquetteZ_adjoint`: With conjugation-invariant phases and mutually adjoint local
  matrices, the adjoint of `u3PlaquetteZ` is `u3PlaquetteZdag`.
* `u3_hamiltonian_explicit_hermitian`: The electric sum minus a real multiple of an explicit
  plaquette matrix plus its adjoint is Hermitian.

## References

* [Byrnes and Yamamoto, 2006][ByrnesYamamoto2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel

namespace Qatlib.Papers.LatGaugeSim05.MainResults

/-- The rational SU(3) dimension formula `(1 + p) * (1 + q) * (1 + (p + q) / 2)`. -/
def u3dim (p q : ℕ) : ℚ := (1 + p) * (1 + q) * (1 + ((p : ℚ) + q) / 2)

/-- The SU(3) dimension formula is strictly positive for natural labels `p` and `q`
[ByrnesYamamoto2006]. -/
theorem u3_dim_pos (p q : ℕ) : 0 < u3dim p q := by
  unfold u3dim
  positivity

/-- The real electric-eigenvalue formula `(p ^ 2 + q ^ 2 + p * q + 3 * (p + q)) / 3`. -/
def u3E2val (p q : ℕ) : ℝ :=
  (1 / 3) * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2 + (p : ℝ) * (q : ℝ)
    + 3 * ((p : ℝ) + (q : ℝ)))

/-- The product of the bounded natural-label registers `Fin (pmax + 1)` and `Fin (qmax + 1)`. -/
abbrev U3Register (pmax qmax : ℕ) := Fin (pmax + 1) × Fin (qmax + 1)

/-- The diagonal electric operator whose entry at a label pair is `u3E2val` embedded in the
complex numbers. -/
def u3E2 (pmax qmax : ℕ) :
    Matrix (U3Register pmax qmax) (U3Register pmax qmax) ℂ :=
  Matrix.diagonal (fun idx => ((u3E2val (idx.1 : ℕ) (idx.2 : ℕ) : ℝ) : ℂ))

/-- Every coordinate basis vector of the SU(3) register has electric eigenvalue given by
`u3E2val` at its labels [ByrnesYamamoto2006]. -/
theorem u3E2_eigen (pmax qmax : ℕ) (idx : U3Register pmax qmax) :
    u3E2 pmax qmax *ᵥ Pi.single idx 1
      = (((u3E2val (idx.1 : ℕ) (idx.2 : ℕ) : ℝ)) : ℂ) • Pi.single idx 1 := by
  rw [u3E2, Matrix.diagonal_mulVec_single]
  ext j
  by_cases h : j = idx
  · subst h; simp
  · simp [h]

/-- The SU(3) diagonal electric operator is Hermitian [ByrnesYamamoto2006]. -/
theorem u3E2_hermitian (pmax qmax : ℕ) : (u3E2 pmax qmax)ᴴ = u3E2 pmax qmax := by
  ext i j
  simp only [u3E2, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp [Complex.conj_ofReal]
  · simp [hij, Ne.symm hij]

/-- A finite sum of Hermitian matrices is Hermitian. -/
private theorem u3_hermitian_sum {H ι : Type*} [Fintype ι]
    (A : ι → Matrix H H ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    (∑ i, A i)ᴴ = ∑ i, A i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => hA i)

/-- A Hermitian electric sum minus a real multiple of paired mutually adjoint plaquette sums is
Hermitian. -/
theorem u3_hamiltonian_hermitian {H : Type*} {Link Plaq : Type*}
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
    u3_hermitian_sum E hE, hA, hx]

/-- The four-link plaquette factors using `V` on the first two links and `Vd` on the last two. -/
def u3Fac {Li β : Type} (Vd V : Li → Li → Matrix β β ℂ) (t : Fin 4 → Li) :
    Fin 4 → Matrix β β ℂ :=
  ![V (t 0) (t 1), V (t 1) (t 2), Vd (t 2) (t 3), Vd (t 3) (t 0)]

/-- The four-link plaquette factors using `Vd` on the first two links and `V` on the last two. -/
def u3FacD {Li β : Type} (Vd V : Li → Li → Matrix β β ℂ) (t : Fin 4 → Li) :
    Fin 4 → Matrix β β ℂ :=
  ![Vd (t 0) (t 1), Vd (t 1) (t 2), V (t 2) (t 3), V (t 3) (t 0)]

/-- The phase-weighted sum over label assignments of the four-link product matrices built from
`u3Fac`. -/
def u3PlaquetteZ {Li β : Type} [Fintype Li]
    (phase : Li → Li → Li → Li → ℂ)
    (Vd : Li → Li → Matrix β β ℂ) (V : Li → Li → Matrix β β ℂ) :
    Matrix (∀ _ : Fin 4, β) (∀ _ : Fin 4, β) ℂ :=
  ∑ t : Fin 4 → Li,
    phase (t 0) (t 1) (t 2) (t 3) • productMatrix (u3Fac Vd V t)

/-- The phase-weighted sum over label assignments of the four-link product matrices built from
`u3FacD`. -/
def u3PlaquetteZdag {Li β : Type} [Fintype Li]
    (phase : Li → Li → Li → Li → ℂ)
    (Vd : Li → Li → Matrix β β ℂ) (V : Li → Li → Matrix β β ℂ) :
    Matrix (∀ _ : Fin 4, β) (∀ _ : Fin 4, β) ℂ :=
  ∑ t : Fin 4 → Li,
    phase (t 0) (t 1) (t 2) (t 3) • productMatrix (u3FacD Vd V t)

/-- With conjugation-invariant phases and mutually adjoint local matrices, the adjoint of
`u3PlaquetteZ` is `u3PlaquetteZdag` [ByrnesYamamoto2006]. -/
theorem u3_plaquetteZ_adjoint {Li β : Type} [Fintype Li] [Fintype β]
    [DecidableEq β]
    (phase : Li → Li → Li → Li → ℂ)
    (hphasestar : ∀ a b c d, star (phase a b c d) = phase a b c d)
    (Vd : Li → Li → Matrix β β ℂ) (V : Li → Li → Matrix β β ℂ)
    (hV : ∀ m n, (V m n)ᴴ = Vd m n)
    (hVd : ∀ m n, (Vd m n)ᴴ = V m n) :
    (u3PlaquetteZ phase Vd V)ᴴ = u3PlaquetteZdag phase Vd V := by
  rw [u3PlaquetteZ, u3PlaquetteZdag, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Matrix.conjTranspose_smul, hphasestar, productMatrix_adjoint]
  have hfac : (fun i : Fin 4 => (u3Fac Vd V t i)ᴴ) = u3FacD Vd V t := by
    funext k
    fin_cases k <;> simp [u3Fac, u3FacD, hV, hVd]
  rw [hfac]

/-- The electric sum minus a real multiple of an explicit plaquette matrix plus its adjoint is
Hermitian [ByrnesYamamoto2006]. -/
theorem u3_hamiltonian_explicit_hermitian {Li β Link : Type}
    [Fintype Li] [Fintype Link]
    (phase : Li → Li → Li → Li → ℂ)
    (Vd : Li → Li → Matrix β β ℂ) (V : Li → Li → Matrix β β ℂ)
    (E : Link → Matrix (∀ _ : Fin 4, β) (∀ _ : Fin 4, β) ℂ) (x : ℝ)
    (hE : ∀ l, (E l)ᴴ = E l) :
    (((∑ l, E l) - (x : ℂ) •
        (u3PlaquetteZ phase Vd V + (u3PlaquetteZ phase Vd V)ᴴ))ᴴ)
      = (∑ l, E l) - (x : ℂ) •
        (u3PlaquetteZ phase Vd V + (u3PlaquetteZ phase Vd V)ᴴ) := by
  have hZ : (u3PlaquetteZ phase Vd V + (u3PlaquetteZ phase Vd V)ᴴ)ᴴ
      = u3PlaquetteZ phase Vd V + (u3PlaquetteZ phase Vd V)ᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  have hx : star (x : ℂ) = (x : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    u3_hermitian_sum E hE, hZ, hx]

/-- The SU(3) qubit-count formula `8 * M * d * D`. -/
def u3QubitCount (M d D : ℕ) : ℕ := 8 * M * d * D

/-- The SU(3) local-operation count `c * (M * d)`. -/
def u3LocalOpCount (M d c : ℕ) : ℕ := c * (M * d)

/-- The SU(3) worst-case operation count `c * (M * d) * (M * d * D)`. -/
def u3WorstOpCount (M d D c : ℕ) : ℕ := c * (M * d) * (M * d * D)

/-- Increasing `M` by one increases the SU(3) qubit count by `8 * (d * D)` [ByrnesYamamoto2006]. -/
theorem u3_qubit_count_linear (d D : ℕ) (M : ℕ) :
    u3QubitCount (M + 1) d D = u3QubitCount M d D + 8 * (d * D) := by
  simp only [u3QubitCount]; ring

/-- Increasing `M` by one increases the SU(3) local-operation count by `c * d`
[ByrnesYamamoto2006]. -/
theorem u3_local_op_count_linear (d c : ℕ) (M : ℕ) :
    u3LocalOpCount (M + 1) d c = u3LocalOpCount M d c + c * d := by
  simp only [u3LocalOpCount]; ring

/-- The SU(3) worst-case operation count equals `c * M ^ 2 * d ^ 2 * D` [ByrnesYamamoto2006]. -/
theorem u3_worst_op_count_quadratic (M d D c : ℕ) :
    u3WorstOpCount M d D c = c * M ^ 2 * d ^ 2 * D := by
  simp only [u3WorstOpCount]; ring

end Qatlib.Papers.LatGaugeSim05.MainResults
