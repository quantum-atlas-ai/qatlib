/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralMeas17.NativeWalk
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralMeas17.SignalReadout
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Papers.SpectralMeas17.NativeWalk
open Qatlib.Papers.SpectralMeas17.PauliExpect
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

theorem physical_signal_probability (α : J → ℝ) (words : J → PauliWord n)
    (φ : State (Fin n → Bool)) (E : ℝ) (hα : 0<coefficientScale α) (hφ : Normalized φ)
    (heig : normalizedHamiltonian α words *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    ‖toHilbert (stateP α words φ E)‖=1 ∧ ‖toHilbert (stateM α words φ E)‖=1 ∧
      ‖toHilbert (signalProjector (coefficientAmplitude α) *ᵥ stateP α words φ E)‖^2=(1/2 : ℝ) ∧
      ‖toHilbert (signalProjector (coefficientAmplitude α) *ᵥ stateM α words φ E)‖^2=(1/2 : ℝ) := by
  have he : ham (coefficientAmplitude α) (terms α words) *ᵥ φ=(E : ℂ) • φ := by
    rw [computed_hamiltonian α words hα]
    exact heig
  have hn := native_eigenvectors α words φ E hα hφ heig hE
  exact ⟨hn.2.1,hn.2.2.1,signal_probability _ _ φ E
    (coefficientAmplitude_normalized α hα) hφ he⟩

theorem physical_signal_branch (α : J → ℝ) (words : J → PauliWord n)
    (φ : State (Fin n → Bool)) (E : ℝ) (hα : 0<coefficientScale α)
    (heig : normalizedHamiltonian α words *ᵥ φ=(E : ℂ) • φ) :
    (Real.sqrt 2 : ℂ) • ((frame (n := n) α)ᴴ *ᵥ stateP α words φ E) = φ ∧
      (Real.sqrt 2 : ℂ) • ((frame (n := n) α)ᴴ *ᵥ stateM α words φ E) = φ := by
  have he : ham (coefficientAmplitude α) (terms α words) *ᵥ φ=(E : ℂ) • φ := by
    rw [computed_hamiltonian α words hα]
    exact heig
  have hs := signal_amplitudes (coefficientAmplitude α) (terms α words) φ E
    (coefficientAmplitude_normalized α hα) he
  have hz : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
  change (Real.sqrt 2 : ℂ) • ((embedding (coefficientAmplitude α))ᴴ *ᵥ _)=_ ∧
    (Real.sqrt 2 : ℂ) • ((embedding (coefficientAmplitude α))ᴴ *ᵥ _)=_
  simp only [stateP,stateM]
  rw [hs.1,hs.2]
  simp [invSqrt2,smul_smul,hz]

end
end Qatlib.Papers.SpectralMeas17.SignalReadout
