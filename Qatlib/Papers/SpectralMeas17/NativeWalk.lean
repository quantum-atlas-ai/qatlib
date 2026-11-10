/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralMeas17.PauliExpect.Coefficients
import Qatlib.Foundations.MatrixGeometry.LcuFrame.Spectrum
import Qatlib.Foundations.MatrixGeometry.LcuFrame.PlaneNorm
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

def terms (α : J → ℝ) (words : J → PauliWord n) (j : J) :=
  signedTerm (coefficientNegative α j) (words j)

def frame (α : J → ℝ) : Matrix (J × (Fin n → Bool)) (Fin n → Bool) ℂ :=
  embedding (coefficientAmplitude α)

def operator (α : J → ℝ) (words : J → PauliWord n) := walk (coefficientAmplitude α) (terms α words)

def stateP (α : J → ℝ) (words : J → PauliWord n) (φ : State (Fin n → Bool)) (E : ℝ) :=
  phiP (coefficientAmplitude α) (terms α words) φ E

def stateM (α : J → ℝ) (words : J → PauliWord n) (φ : State (Fin n → Bool)) (E : ℝ) :=
  phiM (coefficientAmplitude α) (terms α words) φ E

omit [DecidableEq J] in

theorem computed_hamiltonian (α : J → ℝ) (words : J → PauliWord n) (hα : 0<coefficientScale α) :
    ham (coefficientAmplitude α) (terms α words) = normalizedHamiltonian α words := by
  exact (normalizedHamiltonian_eq α words hα).symm

theorem native_lcu (α : J → ℝ) (words : J → PauliWord n) (hα : 0<coefficientScale α) :
    (frame (n := n) α)ᴴ * frame (n := n) α=1 ∧
      (frame (n := n) α)ᴴ * select (terms α words) * frame (n := n) α = normalizedHamiltonian α words := by
  refine ⟨embedding_gram (I := Fin n → Bool) _ (coefficientAmplitude_normalized α hα), ?_⟩
  rw [frame,compression]
  exact computed_hamiltonian α words hα

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
