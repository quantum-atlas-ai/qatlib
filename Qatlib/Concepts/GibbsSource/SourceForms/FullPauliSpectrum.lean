/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliFamily
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentBridge

@[expose] public section


/-!
# Automatic physical-Hamiltonian spectrum for the complete Pauli family

An arbitrary Hermitian matrix `H` determines the energy levels and unitary
used here. They are exactly mathlib's existing automatic spectral data;
the coerced unitary is the frozen `hermUnitary H hH`, and the Gibbs state
is the existing `hermGibbs H hH beta`. The reconstruction and diagonalization
theorems connect these data to the actual input matrix `H`.

The energy-basis proposals are the original `3n` local Paulis transformed
by this selected unitary. Interacting Hamiltonians, degeneracies, and
repeated Bohr frequencies are all allowed. No parent-kernel, positivity,
or spectral-gap statement is a hypothesis of this bridge.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.QuantumGibbs.FormAlgebra



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix

variable {n : ℕ}
variable {H : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ}

/-- The automatic real spectrum, directly reusing the existing spectral
choice rather than introducing independently chosen energy data. -/
noncomputable def fullPauliHamiltonianEigenvalues (hH : H.IsHermitian) :
    Fin (fullPauliDim n) → ℝ := hH.eigenvalues

/-- The same automatically selected eigenvector unitary used by
`hermUnitary` and `hermGibbs`. -/
noncomputable def fullPauliHamiltonianUnitary (hH : H.IsHermitian) :
    Matrix.unitaryGroup (Fin (fullPauliDim n)) ℂ := hH.eigenvectorUnitary

/-- The chosen spectral unitary has the same matrix as the Hermitian spectral API. -/
@[simp] theorem fullPauliHamiltonianUnitary_coe (hH : H.IsHermitian) :
    (fullPauliHamiltonianUnitary hH :
      Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) =
      hermUnitary H hH := rfl

/-- Exact reconstruction of the original arbitrary Hermitian physical
Hamiltonian from the selected real spectrum and unitary. -/
theorem fullPauliHamiltonian_reconstruct (hH : H.IsHermitian) :
    H = (fullPauliHamiltonianUnitary hH :
        Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) *
      Matrix.diagonal (fun i => (fullPauliHamiltonianEigenvalues hH i : ℂ)) *
      (fullPauliHamiltonianUnitary hH :
        Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ := by
  simpa [fullPauliHamiltonianUnitary, fullPauliHamiltonianEigenvalues,
    Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]
    using! hH.spectral_theorem

/-- In the selected energy basis the actual input Hamiltonian is diagonal. -/
theorem fullPauliHamiltonian_diagonalize (hH : H.IsHermitian) :
    (fullPauliHamiltonianUnitary hH :
        Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ * H *
      (fullPauliHamiltonianUnitary hH :
        Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) =
      Matrix.diagonal (fun i => (fullPauliHamiltonianEigenvalues hH i : ℂ)) := by
  simpa [fullPauliHamiltonianUnitary, fullPauliHamiltonianEigenvalues,
    Unitary.conjStarAlgAut_star_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using!
      hH.conjStarAlgAut_star_eigenvectorUnitary

/-- The physical Gibbs state is exactly the existing frozen `hermGibbs`
under the same automatic spectral choice. -/
theorem fullPauliHamiltonian_gibbs_eq (hH : H.IsHermitian) (β : ℝ) :
    hermGibbs H hH β =
      (fullPauliHamiltonianUnitary hH :
        Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) *
        gibbsDiag (fullPauliHamiltonianEigenvalues hH) β *
      (fullPauliHamiltonianUnitary hH :
        Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ := rfl

/-- The actual complete fixed Pauli family expressed in the energy basis
selected from the physical Hamiltonian `H`. -/
noncomputable def fullPauliHamiltonianFamily (hH : H.IsHermitian)
    (a : FullPauliLabel n) :
    Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ :=
  fullPauliEnergyFamily n (fullPauliHamiltonianUnitary hH) a

/-- Full Pauli Hamiltonian Family eq for the stated finite source data. -/
theorem fullPauliHamiltonianFamily_eq (hH : H.IsHermitian)
    (a : FullPauliLabel n) :
    fullPauliHamiltonianFamily hH a =
      (hermUnitary H hH)ᴴ * fullPauliFamily n a * hermUnitary H hH := by
  exact fullPauliEnergyFamily_eq n (fullPauliHamiltonianUnitary hH) a

/-- Full Pauli Hamiltonian Family reconstruct for the stated finite source data. -/
theorem fullPauliHamiltonianFamily_reconstruct (hH : H.IsHermitian)
    (a : FullPauliLabel n) :
    hermUnitary H hH * fullPauliHamiltonianFamily hH a * (hermUnitary H hH)ᴴ =
      fullPauliFamily n a := by
  exact fullPauliEnergyFamily_reconstruct n (fullPauliHamiltonianUnitary hH) a

/-- Full Pauli Hamiltonian Family is Hermitian for the stated finite source data. -/
theorem fullPauliHamiltonianFamily_isHermitian (hH : H.IsHermitian)
    (a : FullPauliLabel n) :
    (fullPauliHamiltonianFamily hH a).IsHermitian :=
  fullPauliEnergyFamily_isHermitian n (fullPauliHamiltonianUnitary hH) a

/-- The concrete Hamiltonian-selected complete local Pauli proposals have
scalar joint commutant. No nondegeneracy assumption on `H` is needed. -/
theorem fullPauliHamiltonianFamily_commutant_scalar (hH : H.IsHermitian)
    (Z : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)
    (hZ : ∀ a, Z * fullPauliHamiltonianFamily hH a =
      fullPauliHamiltonianFamily hH a * Z) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin (fullPauliDim n))
      (Fin (fullPauliDim n)) ℂ) :=
  fullPauliEnergyFamily_commutant_scalar n (fullPauliHamiltonianUnitary hH) Z hZ

end Qatlib.Concepts.GibbsSource.SourceForms
