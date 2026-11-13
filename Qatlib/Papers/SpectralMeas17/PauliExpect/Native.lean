/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
import Qatlib.Foundations.MatrixGeometry.LcuFrame.Moments

/-!
# Pauli expectations in walk eigenstates

This module encodes Pauli commutation signs using the binary symplectic form and proves
conjugation identities for signed Pauli terms. It specializes the walk-state expectation formula
of [PoulinEtAl2018] to Pauli observables.

## Main statements

* `signedTerm_conjugation`: conjugation multiplies a Pauli observable by its commutation sign.
* `gamma`: squared-amplitude average of the commutation signs.
* `native_expectation`: the expectation formula for both paired walk states at an interior
  energy.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralMeas17.PauliExpect
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.MatrixGeometry.LcuFrame
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

/-- The real sign obtained from the binary symplectic pairing of two Pauli words, equal to one
for commuting words and minus one for anticommuting words. -/
def commutationSign (w q : PauliWord n) : ℝ :=
  (-1 : ℝ) ^ (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val

/-- The Pauli word operator negated precisely when the Boolean `negative` is true. -/
def signedTerm (negative : Bool) (w : PauliWord n) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  if negative then -pauliWordOp n w else pauliWordOp n w

/-- Every Pauli word operator squares to the identity matrix. -/
theorem word_square (w : PauliWord n) : pauliWordOp n w * pauliWordOp n w=1 := by
  have h := (Matrix.mem_unitaryGroup_iff').1 (pauliWordOp_unitary n w)
  simpa only [Matrix.star_eq_conjTranspose,pauliWordOp_herm] using h

/-- Every signed Pauli term equals its conjugate transpose. -/
theorem signedTerm_adjoint (b : Bool) (w : PauliWord n) : (signedTerm b w)ᴴ=signedTerm b w := by
  cases b <;> simp [signedTerm,pauliWordOp_herm]

/-- Every signed Pauli term squares to the identity matrix. -/
theorem signedTerm_square (b : Bool) (w : PauliWord n) : signedTerm b w*signedTerm b w=1 := by
  cases b <;> simp [signedTerm,word_square]

/-- The commutation sign of two Pauli words is either one or minus one. -/
theorem commutationSign_values (w q : PauliWord n) :
    commutationSign w q=1 ∨ commutationSign w q = -1 := by
  unfold commutationSign
  have h := (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val_lt
  have hh : (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val=0 ∨
      (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val=1 := by omega
  rcases hh with h0|h1
  · simp [h0]
  · simp [h1]

/-- Conjugating a Pauli word operator by a signed Pauli term multiplies it by their commutation
sign. -/
theorem signedTerm_conjugation (b : Bool) (w q : PauliWord n) :
    signedTerm b w * pauliWordOp n q * signedTerm b w =
      (commutationSign w q : ℂ) • pauliWordOp n q := by
  have hc := pauliWordOp_symplectic n w q
  have hword : pauliWordOp n w * pauliWordOp n q * pauliWordOp n w =
      (commutationSign w q : ℂ) • pauliWordOp n q := by
    rw [hc,smul_mul_assoc,Matrix.mul_assoc,word_square,Matrix.mul_one]
    congr 1
    simp [commutationSign]
  cases b <;> simpa [signedTerm] using hword

/-- The Hamiltonian formed from the signed Pauli terms with weights equal to the squared real
preparation amplitudes. -/
def hamiltonian (β : J → ℝ) (negative : J → Bool) (words : J → PauliWord n) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ := ham β (fun j => signedTerm (negative j) (words j))

/-- The sum of the Pauli commutation signs with the observable word, weighted by the squared
preparation amplitudes. -/
def gamma (β : J → ℝ) (words : J → PauliWord n) (q : PauliWord n) : ℝ :=
  ∑ j, β j^2 * commutationSign (words j) q

/-- For normalized preparation amplitudes and a normalized Hamiltonian eigenvector with `E ^ 2 <
1`, both paired walk states have Pauli expectation equal to `1 / 2 * (1 + (gamma β words q -
E ^ 2) / (1 - E ^ 2))` times the original eigenvector's expectation [Poulin et al., Equation
(8)][PoulinEtAl2018]. -/
theorem native_expectation (β : J → ℝ) (negative : J → Bool) (words : J → PauliWord n)
    (q : PauliWord n) (φ : State (Fin n → Bool)) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hφ : Normalized φ)
    (heig : hamiltonian β negative words *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    Inner (phiP β (fun j => signedTerm (negative j) (words j)) φ E)
      (applySys (pauliWordOp n q) (phiP β (fun j => signedTerm (negative j) (words j)) φ E)) =
      (((1/2 : ℝ)*(1+(gamma β words q-E^2)/(1-E^2)) : ℝ) : ℂ) * Inner φ (pauliWordOp n q *ᵥ φ) ∧
    Inner (phiM β (fun j => signedTerm (negative j) (words j)) φ E)
      (applySys (pauliWordOp n q) (phiM β (fun j => signedTerm (negative j) (words j)) φ E)) =
      (((1/2 : ℝ)*(1+(gamma β words q-E^2)/(1-E^2)) : ℝ) : ℂ) * Inner φ (pauliWordOp n q *ᵥ φ) := by
  exact expectation_eq8 β (fun j => signedTerm (negative j) (words j)) (pauliWordOp n q)
    (fun j => commutationSign (words j) q) φ E hβ hφ (pauliWordOp_herm n q) (word_square q)
    (fun j => signedTerm_adjoint _ _) (fun j => signedTerm_square _ _)
    (fun j => signedTerm_conjugation _ _ _) (fun j => commutationSign_values _ _) heig hE

end
end Qatlib.Papers.SpectralMeas17.PauliExpect
