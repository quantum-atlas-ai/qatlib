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
# SU(2) electric and plaquette operators

`u2E2` is the diagonal electric operator with eigenvalues `j * (j + 1)` for half-integer labels
`u2jR`. The four-factor construction `u2PlaquetteZ` is Hermitian under the stated involution and
sign identities, and the module verifies Hamiltonian Hermiticity and explicit resource-count
formulas. See [ByrnesYamamoto2006] for the paper context.

## Main statements

* `u2E2_eigen`: Each coordinate basis vector is an eigenvector of `u2E2` with eigenvalue `j * (j
  + 1)`.
* `u2_plaquetteZ_hermitian`: The SU(2) plaquette sum is Hermitian when label negation is
  involutive and the real signs and local matrices satisfy the stated identities.
* `u2_worst_op_count_quadratic`: The SU(2) worst-case operation count equals `c * M ^ 2 * d ^ 2
  * D`.

## References

* [Byrnes and Yamamoto, 2006][ByrnesYamamoto2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel

namespace Qatlib.Papers.LatGaugeSim05.MainResults

/-- The half-integer spin label obtained by dividing the register index by two. -/
def u2jR {jmax : ℕ} (i : Fin (jmax + 1)) : ℝ := (i : ℝ) / 2

/-- The diagonal SU(2) electric operator with entries `j * (j + 1)` at spin `j = u2jR i`. -/
def u2E2 (jmax : ℕ) : Matrix (Fin (jmax + 1)) (Fin (jmax + 1)) ℂ :=
  Matrix.diagonal (fun i => (u2jR i : ℂ) * ((u2jR i + 1 : ℝ) : ℂ))

/-- Each coordinate basis vector is an eigenvector of `u2E2` with eigenvalue `j * (j + 1)`
[ByrnesYamamoto2006]. -/
theorem u2E2_eigen (jmax : ℕ) (i : Fin (jmax + 1)) :
    u2E2 jmax *ᵥ Pi.single i 1
      = ((u2jR i : ℂ) * ((u2jR i + 1 : ℝ) : ℂ)) • Pi.single i 1 := by
  rw [u2E2, Matrix.diagonal_mulVec_single]
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- The diagonal SU(2) electric operator is Hermitian. -/
theorem u2E2_hermitian (jmax : ℕ) : (u2E2 jmax)ᴴ = u2E2 jmax := by
  ext i j
  simp only [u2E2, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp [Complex.conj_ofReal]
  · simp [hij, Ne.symm hij]

/-- A finite sum of Hermitian matrices is Hermitian. -/
private theorem u2_hermitian_sum {H ι : Type*} [Fintype ι]
    (A : ι → Matrix H H ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    (∑ i, A i)ᴴ = ∑ i, A i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => hA i)

/-- The sum of Hermitian electric terms minus `2 * x` times the sum of Hermitian plaquette terms
is Hermitian for real `x` [ByrnesYamamoto2006]. -/
theorem u2_hamiltonian_hermitian {H : Type*} {Link Plaq : Type*}
    [Fintype Link] [Fintype Plaq]
    (E : Link → Matrix H H ℂ) (Z : Plaq → Matrix H H ℂ) (x : ℝ)
    (hE : ∀ l, (E l)ᴴ = E l) (hZ : ∀ p, (Z p)ᴴ = Z p) :
    (((∑ l, E l) - (2 * x : ℝ) • (∑ p, Z p))ᴴ)
      = (∑ l, E l) - (2 * x : ℝ) • (∑ p, Z p) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    u2_hermitian_sum E hE, u2_hermitian_sum Z hZ]

  rw [star_trivial]

/-- Scaling each factor of a product matrix scales the resulting matrix by the product of the
scalars. -/
private theorem productMatrix_smul {ι : Type*} [Fintype ι] {S : ι → Type*}
    (c : ι → ℂ) (A : ∀ i, Matrix (S i) (S i) ℂ) :
    productMatrix (fun i => c i • A i) = (∏ i, c i) • productMatrix A := by
  ext x y
  simp only [productMatrix, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- The four local matrix factors of an SU(2) plaquette, with the label involution applied on
the last two links. -/
def u2Fac {Mag β : Type} (neg : Mag → Mag) (V : Mag → Mag → Matrix β β ℂ)
    (t : Fin 4 → Mag) : Fin 4 → Matrix β β ℂ :=
  ![V (t 0) (t 1), V (t 1) (t 2), V (neg (t 2)) (neg (t 3)), V (neg (t 3)) (neg (t 0))]

/-- The four products of label signs associated with the SU(2) plaquette factors. -/
def u2Sign {Mag : Type} (neg : Mag → Mag) (chi : Mag → ℂ) (t : Fin 4 → Mag) :
    Fin 4 → ℂ :=
  ![chi (t 0) * chi (t 1), chi (t 1) * chi (t 2),
    chi (neg (t 2)) * chi (neg (t 3)), chi (neg (t 3)) * chi (neg (t 0))]

/-- The sum of four-link product matrices weighted by the signs of the first and third labels. -/
def u2PlaquetteZ {Mag β : Type} [Fintype Mag]
    (neg : Mag → Mag) (chi : Mag → ℂ) (V : Mag → Mag → Matrix β β ℂ) :
    Matrix (∀ _ : Fin 4, β) (∀ _ : Fin 4, β) ℂ :=
  ∑ t : Fin 4 → Mag, (chi (t 0) * chi (t 2)) • productMatrix (u2Fac neg V t)

/-- Under the local adjoint and sign-invariance identities, taking the adjoint of a plaquette
factor negates its labels and multiplies it by the corresponding sign. -/
private theorem u2Fac_adjoint {Mag β : Type} [Fintype Mag]
    (neg : Mag → Mag)
    (chi : Mag → ℂ) (hchineg : ∀ m, chi (neg m) = chi m)
    (V : Mag → Mag → Matrix β β ℂ)
    (hV : ∀ m n, (V m n)ᴴ = (chi m * chi n) • V (neg m) (neg n))
    (t : Fin 4 → Mag) (i : Fin 4) :
    (u2Fac neg V t i)ᴴ = u2Sign neg chi t i • u2Fac neg V (fun k => neg (t k)) i := by
  fin_cases i <;> simp [u2Fac, u2Sign, hV, hchineg]

/-- If each sign squares to one and is invariant under label negation, the product of the four
plaquette signs is one. -/
private theorem u2Sign_prod {Mag : Type}
    (neg : Mag → Mag) (chi : Mag → ℂ)
    (hchi : ∀ m, chi m * chi m = 1)
    (hchineg : ∀ m, chi (neg m) = chi m)
    (t : Fin 4 → Mag) :
    (∏ i : Fin 4, u2Sign neg chi t i) = 1 := by
  have hv0 : u2Sign neg chi t 0 = chi (t 0) * chi (t 1) := by simp [u2Sign]
  have hv1 : u2Sign neg chi t 1 = chi (t 1) * chi (t 2) := by simp [u2Sign]
  have hv2 : u2Sign neg chi t 2 = chi (neg (t 2)) * chi (neg (t 3)) := by simp [u2Sign]
  have hv3 : u2Sign neg chi t 3 = chi (neg (t 3)) * chi (neg (t 0)) := by simp [u2Sign]
  rw [Fin.prod_univ_four, hv0, hv1, hv2, hv3]
  rw [hchineg (t 2), hchineg (t 3), hchineg (t 0)]
  have h0 := hchi (t 0)
  have h1 := hchi (t 1)
  have h2 := hchi (t 2)
  have h3 := hchi (t 3)
  calc chi (t 0) * chi (t 1) * (chi (t 1) * chi (t 2)) * (chi (t 2) * chi (t 3)) *
        (chi (t 3) * chi (t 0))
      = (chi (t 0) * chi (t 0)) * (chi (t 1) * chi (t 1)) *
        (chi (t 2) * chi (t 2)) * (chi (t 3) * chi (t 3)) := by ring
    _ = 1 := by rw [h0, h1, h2, h3]; ring

/-- The SU(2) plaquette sum is Hermitian when label negation is involutive and the real signs
and local matrices satisfy the stated identities [ByrnesYamamoto2006]. -/
theorem u2_plaquetteZ_hermitian {Mag β : Type} [Fintype Mag] [Fintype β]
    [DecidableEq β]
    (neg : Mag → Mag) (hneg : Function.Involutive neg)
    (chi : Mag → ℂ) (hchi : ∀ m, chi m * chi m = 1)
    (hchistar : ∀ m, star (chi m) = chi m)
    (hchineg : ∀ m, chi (neg m) = chi m)
    (V : Mag → Mag → Matrix β β ℂ)
    (hV : ∀ m n, (V m n)ᴴ = (chi m * chi n) • V (neg m) (neg n)) :
    (u2PlaquetteZ neg chi V)ᴴ = u2PlaquetteZ neg chi V := by

  have hflip_bij : Function.Bijective (fun t : Fin 4 → Mag => fun k => neg (t k)) := by
    refine ⟨fun a b h => ?_, fun b => ?_⟩
    · funext k
      exact hneg.injective (congrFun h k)
    · exact ⟨fun k => neg (b k), by funext k; exact hneg (b k)⟩

  have hstep : (u2PlaquetteZ neg chi V)ᴴ
      = ∑ t : Fin 4 → Mag,
          (chi (t 0) * chi (t 2)) •
            productMatrix (u2Fac neg V (fun k => neg (t k))) := by
    rw [u2PlaquetteZ, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Matrix.conjTranspose_smul]
    have hstar : star (chi (t 0) * chi (t 2)) = chi (t 0) * chi (t 2) := by
      rw [star_mul, hchistar (t 2), hchistar (t 0), mul_comm]
    rw [hstar, productMatrix_adjoint]
    have hfac : (fun i : Fin 4 => (u2Fac neg V t i)ᴴ)
        = fun i => u2Sign neg chi t i • u2Fac neg V (fun k => neg (t k)) i := by
      funext i
      exact u2Fac_adjoint neg chi hchineg V hV t i
    rw [hfac, productMatrix_smul, u2Sign_prod neg chi hchi hchineg t, one_smul]

  rw [hstep]
  refine (Fintype.sum_bijective (fun t : Fin 4 → Mag => fun k => neg (t k)) hflip_bij
    (fun t => (chi (t 0) * chi (t 2)) •
      productMatrix (u2Fac neg V (fun k => neg (t k))))
    (fun s => (chi (s 0) * chi (s 2)) • productMatrix (u2Fac neg V s)) ?_).trans ?_
  · intro t
    simp only [hchineg]
  · rw [u2PlaquetteZ]

/-- The SU(2) qubit-count formula `3 * M * d * D`. -/
def u2QubitCount (M d D : ℕ) : ℕ := 3 * M * d * D

/-- The SU(2) local-operation count `c * (M * d)`. -/
def u2LocalOpCount (M d c : ℕ) : ℕ := c * (M * d)

/-- The SU(2) worst-case operation count `c * (M * d) * (M * d * D)`. -/
def u2WorstOpCount (M d D c : ℕ) : ℕ := c * (M * d) * (M * d * D)

/-- Increasing `M` by one increases the SU(2) qubit count by `3 * (d * D)` [ByrnesYamamoto2006]. -/
theorem u2_qubit_count_linear (d D : ℕ) (M : ℕ) :
    u2QubitCount (M + 1) d D = u2QubitCount M d D + 3 * (d * D) := by
  simp only [u2QubitCount]; ring

/-- Increasing `M` by one increases the SU(2) local-operation count by `c * d`
[ByrnesYamamoto2006]. -/
theorem u2_local_op_count_linear (d c : ℕ) (M : ℕ) :
    u2LocalOpCount (M + 1) d c = u2LocalOpCount M d c + c * d := by
  simp only [u2LocalOpCount]; ring

/-- The SU(2) worst-case operation count equals `c * M ^ 2 * d ^ 2 * D` [ByrnesYamamoto2006]. -/
theorem u2_worst_op_count_quadratic (M d D c : ℕ) :
    u2WorstOpCount M d D c = c * M ^ 2 * d ^ 2 * D := by
  simp only [u2WorstOpCount]; ring

end Qatlib.Papers.LatGaugeSim05.MainResults
