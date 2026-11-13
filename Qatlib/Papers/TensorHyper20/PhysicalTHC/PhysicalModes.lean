/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.WeightedModes
import Qatlib.Papers.TensorHyper20.MainResults.DiagonalCoulomb

/-!
# Physical fermionic modes for tensor hypercontraction

Embeds real orbital vectors into a selected spin sector using `spinVector` and realizes their
lowering, raising, occupation, and reflection operators in the Jordan–Wigner representation.
Normalized orbital vectors yield positive idempotent occupations and unitary involutive
reflections.

The identity `physical_coulomb_eq` relates the occupation-product expression `diagonalCoulomb`
to the creation-annihilation expansion `factorizedCoulomb` for the tensor hypercontraction
formulation of [LeeEtAl2021].

## Main statements

* `physical_number`: proves positivity and idempotence of normalized occupations.
* `physical_reflection`: proves unitarity and involutivity of normalized reflections.
* `physical_coulomb_eq`: identifies the two physical Coulomb expressions.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
namespace Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalModes
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner.WeightedModes

/-- The orbital vector embedded into the selected spin sector of `Fin (N * 2)`, with zero
coefficients in the other sector. -/
def spinVector {N : ℕ} (v : Fin N → ℝ) (spin : Fin 2) : Fin (N*2) → ℝ :=
  fun j => if (finProdFinEquiv.symm j).2=spin then v (finProdFinEquiv.symm j).1 else 0

/-- Embedding a vector into a spin sector preserves the sum of its squared real coefficients. -/
theorem spinVector_energy {N : ℕ} (v : Fin N → ℝ) (spin : Fin 2) :
    ∑ j, spinVector v spin j^2 = ∑ p, v p^2 := by
  rw [← Equiv.sum_comp (finProdFinEquiv : (Fin N×Fin 2) ≃ Fin (N*2))]
  simp [spinVector,Fintype.sum_prod_type]

/-- The lowering operator of a spin-embedded vector is the weighted sum of annihilation
operators in that spin sector. -/
theorem lower_spinVector {N : ℕ} (v : Fin N → ℝ) (spin : Fin 2) :
    lower (spinVector v spin) = ∑ p, v p • annihilation (finProdFinEquiv (p,spin)) := by
  unfold lower
  rw [← Equiv.sum_comp (finProdFinEquiv : (Fin N×Fin 2) ≃ Fin (N*2))]
  simp [spinVector,Fintype.sum_prod_type]

/-- The raising operator of a spin-embedded vector is the weighted sum of creation operators in
that spin sector. -/
theorem raise_spinVector {N : ℕ} (v : Fin N → ℝ) (spin : Fin 2) :
    raise (spinVector v spin) = ∑ p, v p • creation (finProdFinEquiv (p,spin)) := by
  unfold raise
  rw [← Equiv.sum_comp (finProdFinEquiv : (Fin N×Fin 2) ≃ Fin (N*2))]
  simp [spinVector,Fintype.sum_prod_type]

/-- For an orbital vector with squared coefficients summing to one, its spin-sector occupation
operator is positive semidefinite and idempotent. -/
theorem physical_number {N : ℕ} (v : Fin N → ℝ) (spin : Fin 2) (hv : ∑ p, v p^2=1) :
    (occupation (spinVector v spin)).PosSemidef ∧
      occupation (spinVector v spin)*occupation (spinVector v spin)=occupation (spinVector v spin) := by
  exact ⟨occupation_positive _,occupation_idempotent _ ((spinVector_energy v spin).trans hv)⟩

/-- For a normalized orbital vector, the associated spin-sector reflection is unitary and
squares to the identity. -/
theorem physical_reflection {N : ℕ} (v : Fin N → ℝ) (spin : Fin 2) (hv : ∑ p, v p^2=1) :
    reflection (spinVector v spin) ∈ Matrix.unitaryGroup (Reg (N*2)) ℂ ∧
      reflection (spinVector v spin)*reflection (spinVector v spin)=1 := by
  have h := (spinVector_energy v spin).trans hv
  exact ⟨reflection_unitary _ h,reflection_square _ h⟩

/-- The half-weighted sum of products of spin-sector occupation operators with coefficients
`zeta`. -/
def diagonalCoulomb {N M : ℕ} (chi : Fin M → Fin N → ℝ) (zeta : Fin M → Fin M → ℝ) :
    Matrix (Reg (N*2)) (Reg (N*2)) ℂ :=
  (1/2 : ℝ) • ∑ spin : Fin 2, ∑ spin' : Fin 2, ∑ mu : Fin M, ∑ nu : Fin M,
    zeta mu nu • (occupation (spinVector (chi mu) spin)*occupation (spinVector (chi nu) spin'))

/-- The four-orbital-index creation-annihilation expansion with tensor hypercontraction
coefficients formed from `chi` and `zeta`. -/
def factorizedCoulomb {N M : ℕ} (chi : Fin M → Fin N → ℝ) (zeta : Fin M → Fin M → ℝ) :
    Matrix (Reg (N*2)) (Reg (N*2)) ℂ :=
  (1/2 : ℝ) • ∑ spin : Fin 2, ∑ spin' : Fin 2, ∑ mu : Fin M, ∑ nu : Fin M,
    ∑ p : Fin N, ∑ q : Fin N, ∑ r : Fin N, ∑ s : Fin N,
      (chi mu p*chi mu q*chi nu r*chi nu s*zeta mu nu) •
        (creation (finProdFinEquiv (p,spin))*annihilation (finProdFinEquiv (q,spin))*
          creation (finProdFinEquiv (r,spin'))*annihilation (finProdFinEquiv (s,spin')))

/-- The diagonal occupation-product Coulomb expression equals its factorized
creation-annihilation expansion. See [LeeEtAl2021]. -/
theorem physical_coulomb_eq {N M : ℕ} (chi : Fin M → Fin N → ℝ) (zeta : Fin M → Fin M → ℝ) :
    diagonalCoulomb chi zeta = factorizedCoulomb chi zeta := by
  unfold diagonalCoulomb factorizedCoulomb occupation
  simp_rw [raise_spinVector,lower_spinVector]
  exact Qatlib.Papers.TensorHyper20.MainResults.DiagonalCoulomb.eq12_diagonal_coulomb N M chi zeta
    (fun p spin => creation (finProdFinEquiv (p,spin)))
    (fun p spin => annihilation (finProdFinEquiv (p,spin)))

end Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalModes
