/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralMeas17.NativeWalk
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralMeas17.PauliExpect
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Papers.SpectralMeas17.NativeWalk
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

theorem physical_expectation (α : J → ℝ) (words : J → PauliWord n) (q : PauliWord n)
    (φ : State (Fin n → Bool)) (E : ℝ) (hα : 0<coefficientScale α) (hφ : Normalized φ)
    (heig : normalizedHamiltonian α words *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    inner ℂ (toHilbert (stateP α words φ E))
      (toHilbert (applySys (pauliWordOp n q) (stateP α words φ E))) =
      (((1/2 : ℝ)*(1+(gamma (coefficientAmplitude α) words q-E^2)/(1-E^2)) : ℝ) : ℂ) *
        inner ℂ (toHilbert φ) (toHilbert (pauliWordOp n q *ᵥ φ)) ∧
    inner ℂ (toHilbert (stateM α words φ E))
      (toHilbert (applySys (pauliWordOp n q) (stateM α words φ E))) =
      (((1/2 : ℝ)*(1+(gamma (coefficientAmplitude α) words q-E^2)/(1-E^2)) : ℝ) : ℂ) *
        inner ℂ (toHilbert φ) (toHilbert (pauliWordOp n q *ᵥ φ)) := by
  have he : hamiltonian (coefficientAmplitude α) (coefficientNegative α) words *ᵥ φ=(E : ℂ) • φ := by
    rw [← normalizedHamiltonian_eq α words hα]
    exact heig
  simpa only [inner_toHilbert,stateP,stateM,terms] using!
    native_expectation (coefficientAmplitude α) (coefficientNegative α) words q φ E
      (coefficientAmplitude_normalized α hα) hφ he hE

end
end Qatlib.Papers.SpectralMeas17.PauliExpect
