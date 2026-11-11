/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralMeas17.PauliExpect.Coefficients
import Qatlib.Foundations.MatrixGeometry.LcuFrame.Spectrum
import Qatlib.Foundations.MatrixGeometry.LcuFrame.PlaneNorm

/-!
# Spectral walk from Pauli coefficients

This module builds the signed Pauli terms, coefficient embedding, walk operator, and paired walk
states directly from real Hamiltonian coefficients. It verifies the compression and interior
eigenphase relations of [PoulinEtAl2018] for normalized Hamiltonian eigenvectors with `E ^ 2 <
1`.

## Main statements

* `native_lcu`: the coefficient frame is isometric and compresses SELECT to the normalized
  Hamiltonian.
* `native_eigenvectors`: unitarity and normalized eigenvectors with phases `±Real.arccos E`.
* `native_plane`: normalization and orthogonality for the auxiliary walk-plane vector.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralMeas17.NativeWalk
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Papers.SpectralMeas17.PauliExpect
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

/-- The Pauli matrix terms with each real coefficient's sign incorporated into its Pauli word
operator. -/
def terms (α : J → ℝ) (words : J → PauliWord n) (j : J) :=
  signedTerm (coefficientNegative α j) (words j)

/-- The system-to-control-system embedding determined by the square-root amplitudes of the
normalized absolute coefficients. -/
def frame (α : J → ℝ) : Matrix (J × (Fin n → Bool)) (Fin n → Bool) ℂ :=
  embedding (coefficientAmplitude α)

/-- The spectral walk formed from the coefficient preparation amplitudes and the signed Pauli
terms. -/
def operator (α : J → ℝ) (words : J → PauliWord n) := walk (coefficientAmplitude α) (terms α words)

/-- The positive-phase paired walk state constructed from the coefficient amplitudes, signed
Pauli terms, input state, and energy. -/
def stateP (α : J → ℝ) (words : J → PauliWord n) (φ : State (Fin n → Bool)) (E : ℝ) :=
  phiP (coefficientAmplitude α) (terms α words) φ E

/-- The negative-phase paired walk state constructed from the coefficient amplitudes, signed
Pauli terms, input state, and energy. -/
def stateM (α : J → ℝ) (words : J → PauliWord n) (φ : State (Fin n → Bool)) (E : ℝ) :=
  phiM (coefficientAmplitude α) (terms α words) φ E

omit [DecidableEq J] in

/-- For positive coefficient scale, the Hamiltonian formed from the coefficient amplitudes and
signed Pauli terms equals the coefficient-normalized Pauli Hamiltonian. -/
theorem computed_hamiltonian (α : J → ℝ) (words : J → PauliWord n) (hα : 0<coefficientScale α) :
    ham (coefficientAmplitude α) (terms α words) = normalizedHamiltonian α words := by
  exact (normalizedHamiltonian_eq α words hα).symm

/-- For positive coefficient scale, the coefficient frame has Gram matrix one and compresses
SELECT to the normalized Pauli Hamiltonian, realizing the linear-combination construction of
[PoulinEtAl2018]. -/
theorem native_lcu (α : J → ℝ) (words : J → PauliWord n) (hα : 0<coefficientScale α) :
    (frame (n := n) α)ᴴ * frame (n := n) α=1 ∧
      (frame (n := n) α)ᴴ * select (terms α words) * frame (n := n) α = normalizedHamiltonian α words := by
  refine ⟨embedding_gram (I := Fin n → Bool) _ (coefficientAmplitude_normalized α hα), ?_⟩
  rw [frame,compression]
  exact computed_hamiltonian α words hα

/-- For a normalized Hamiltonian eigenvector at energy `E` with `E ^ 2 < 1` and positive
coefficient scale, the spectral walk is unitary and its two paired states have unit Hilbert
norm and eigenvalues `exp (±i * Real.arccos E)`. The decoded energy satisfies `Real.cos
(Real.arccos E) = E` [PoulinEtAl2018]. -/
theorem native_eigenvectors (α : J → ℝ) (words : J → PauliWord n) (φ : State (Fin n → Bool))
    (E : ℝ) (hα : 0<coefficientScale α) (hφ : Normalized φ)
    (heig : normalizedHamiltonian α words *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    operator α words ∈ Matrix.unitaryGroup (J × (Fin n → Bool)) ℂ ∧
      ‖toHilbert (stateP α words φ E)‖=1 ∧ ‖toHilbert (stateM α words φ E)‖=1 ∧
      operator α words *ᵥ stateP α words φ E =
        Complex.exp ((Real.arccos E : ℂ)*Complex.I) • stateP α words φ E ∧
      operator α words *ᵥ stateM α words φ E =
        Complex.exp (-(Real.arccos E : ℂ)*Complex.I) • stateM α words φ E ∧
      Real.cos (Real.arccos E)=E := by
  have he : ham (coefficientAmplitude α) (terms α words) *ᵥ φ=(E : ℂ) • φ := by
    rw [computed_hamiltonian α words hα]
    exact heig
  exact full_walk_eigenvectors _ _ φ E (coefficientAmplitude_normalized α hα) hφ
    (fun j => signedTerm_adjoint _ _) (fun j => signedTerm_square _ _) he hE

/-- For a normalized Hamiltonian eigenvector with `E ^ 2 < 1` and positive coefficient scale,
the auxiliary vector `phi1` has unit Hilbert norm and is orthogonal to the embedded vector
`phi0` [PoulinEtAl2018]. -/
theorem native_plane (α : J → ℝ) (words : J → PauliWord n) (φ : State (Fin n → Bool))
    (E : ℝ) (hα : 0<coefficientScale α) (hφ : Normalized φ)
    (heig : normalizedHamiltonian α words *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    ‖toHilbert (phi1 (coefficientAmplitude α) (terms α words) φ E)‖=1 ∧
      inner ℂ (toHilbert (phi0 (coefficientAmplitude α) φ))
        (toHilbert (phi1 (coefficientAmplitude α) (terms α words) φ E))=0 := by
  have he : ham (coefficientAmplitude α) (terms α words) *ᵥ φ=(E : ℂ) • φ := by
    rw [computed_hamiltonian α words hα]
    exact heig
  have h := phi1_orthonormal _ _ φ E (coefficientAmplitude_normalized α hα) hφ
    (fun j => signedTerm_adjoint _ _) (fun j => signedTerm_square _ _) he hE
  exact ⟨(normalized_iff_hilbert _).1 h.1, (inner_toHilbert _ _).trans h.2⟩

end
end Qatlib.Papers.SpectralMeas17.NativeWalk
