/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
import Qatlib.Foundations.MatrixGeometry.LcuFrame.Moments
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralMeas17.PauliExpect
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.MatrixGeometry.LcuFrame
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

def commutationSign (w q : PauliWord n) : ℝ :=
  (-1 : ℝ) ^ (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val

def signedTerm (negative : Bool) (w : PauliWord n) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  if negative then -pauliWordOp n w else pauliWordOp n w

theorem word_square (w : PauliWord n) : pauliWordOp n w * pauliWordOp n w=1 := by
  have h := (Matrix.mem_unitaryGroup_iff').1 (pauliWordOp_unitary n w)
  simpa only [Matrix.star_eq_conjTranspose,pauliWordOp_herm] using h

theorem signedTerm_adjoint (b : Bool) (w : PauliWord n) : (signedTerm b w)ᴴ=signedTerm b w := by
  cases b <;> simp [signedTerm,pauliWordOp_herm]

theorem signedTerm_square (b : Bool) (w : PauliWord n) : signedTerm b w*signedTerm b w=1 := by
  cases b <;> simp [signedTerm,word_square]

theorem commutationSign_values (w q : PauliWord n) :
    commutationSign w q=1 ∨ commutationSign w q = -1 := by
  unfold commutationSign
  have h := (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val_lt
  have hh : (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val=0 ∨
      (symplecticForm (symplecticX w,symplecticZ w) (symplecticX q,symplecticZ q)).val=1 := by omega
  rcases hh with h0|h1
  · simp [h0]
  · simp [h1]

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

def hamiltonian (β : J → ℝ) (negative : J → Bool) (words : J → PauliWord n) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ := ham β (fun j => signedTerm (negative j) (words j))

def gamma (β : J → ℝ) (words : J → PauliWord n) (q : PauliWord n) : ℝ :=
  ∑ j, β j^2 * commutationSign (words j) q

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
