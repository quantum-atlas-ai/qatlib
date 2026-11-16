/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliSpectrum
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSourceGapForm

@[expose] public section


/-! # Complete local-Pauli source parents for arbitrary Hermitian Hamiltonians

The input is an actual Hermitian Hamiltonian on `n` qubits. Its automatic
spectral data reconstruct that same input, and the proposals are the same
`3n` local unit Pauli matrices expressed in that energy basis. Every one of
the `D^2` transition labels and complex operator coordinates is retained.

The exact Gibbs kernel, attained positive gaps, and lower gap comparison
are unconditional on spectral degeneracy or locality of the Hamiltonian.
They do not supply a size-independent positive gap, an upper comparison,
or an identification with a continuous-time physical KMS generator.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {n : ℕ}
variable {H : Operator (fullPauliDim n)}

/-- The complete source-weighted Gram in the automatically selected energy
basis of the actual input Hamiltonian. -/
noncomputable def fullPauliSourceMatrix (hH : H.IsHermitian) (β : ℝ)
    (kern : ℝ → ℝ) : Matrix (FullCoord (fullPauliDim n)) (FullCoord (fullPauliDim n)) ℂ :=
  fullGramMatrix (fullPauliHamiltonianEigenvalues hH) β kern
    (fullPauliHamiltonianFamily hH)

noncomputable def fullPauliSourceGibbsVector (hH : H.IsHermitian) (β : ℝ) :
    FullCoord (fullPauliDim n) → ℂ :=
  fullGibbsVector (fullPauliHamiltonianEigenvalues hH) β

noncomputable def fullPauliSourcePlainGap (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  fullSourcePlainGap (fullPauliHamiltonianEigenvalues hH) β
    (fullPauliHamiltonianFamily hH)

noncomputable def fullPauliSourceDampedGap (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  fullSourceDampedGap (fullPauliHamiltonianEigenvalues hH) β
    (fullPauliHamiltonianFamily hH)

/-- This is the literal full `W/2` assembly over all `3n` actual proposals,
not a compression to a selected invariant subspace. -/
theorem fullPauliSourceMatrix_eq (hH : H.IsHermitian) (β : ℝ) (kern : ℝ → ℝ) :
    fullPauliSourceMatrix hH β kern =
      ∑ P : FullPauliLabel n, ∑ a : FullCoord (fullPauliDim n),
        ∑ b : FullCoord (fullPauliDim n),
          ((ckgSourceWeight β
            (fullNu (fullPauliHamiltonianEigenvalues hH) a)
            (fullNu (fullPauliHamiltonianEigenvalues hH) b) *
              kern (fullNu (fullPauliHamiltonianEigenvalues hH) a -
                fullNu (fullPauliHamiltonianEigenvalues hH) b) / 2 : ℝ) : ℂ) •
            ((fullFactorMatrix (fullPauliHamiltonianEigenvalues hH) β
              (fullPauliHamiltonianFamily hH P) a)ᴴ *
              fullFactorMatrix (fullPauliHamiltonianEigenvalues hH) β
                (fullPauliHamiltonianFamily hH P) b) := rfl

/-- Full Pauli Source pos Semidef for the stated finite source data. -/
theorem fullPauliSource_posSemidef (hH : H.IsHermitian) {β : ℝ} (hβ : 0 < β) :
    (fullPauliSourceMatrix hH β (fun _ => 1)).PosSemidef ∧
      (fullPauliSourceMatrix hH β (fun ω => 2 * phaseKernel β ω)).PosSemidef :=
  ⟨fullGramMatrix_plain_posSemidef hβ _ _, fullGramMatrix_damped_posSemidef hβ _ _⟩

/-- The actual full plain source parent has exactly one complex Gibbs
direction, for every Hermitian Hamiltonian, including fully degenerate spectra. -/
theorem fullPauliSource_plain_kernel (hH : H.IsHermitian) {β : ℝ}
    (hβ : 0 < β) (z : FullCoord (fullPauliDim n) → ℂ) :
    fullPauliSourceMatrix hH β (fun _ => 1) *ᵥ z = 0 ↔
      ∃ c : ℂ, z = c • fullPauliSourceGibbsVector hH β :=
  fullGramMatrix_plain_kernel (fullPauliHamiltonianEigenvalues hH) hβ
    (fullPauliHamiltonianFamily hH) (fullPauliHamiltonianFamily_commutant_scalar hH) z

/-- Full Pauli Source damped kernel for the stated finite source data. -/
theorem fullPauliSource_damped_kernel (hn : 0 < n) (hH : H.IsHermitian) {β : ℝ}
    (hβ : 0 < β) (z : FullCoord (fullPauliDim n) → ℂ) :
    fullPauliSourceMatrix hH β (fun ω => 2 * phaseKernel β ω) *ᵥ z = 0 ↔
      ∃ c : ℂ, z = c • fullPauliSourceGibbsVector hH β :=
  fullGramMatrix_damped_kernel (fullPauliDim_ge_two n hn)
    (fullPauliHamiltonianEigenvalues hH) hβ (fullPauliHamiltonianFamily hH)
    (fullPauliHamiltonianFamily_commutant_scalar hH) z

/-- Actual positive attained gaps and their lower comparison for arbitrary
system size. This is not a quantitative size-uniform lower bound. -/
theorem fullPauliSource_gap_comparison (hn : 0 < n) (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) :
    0 < fullPauliSourcePlainGap hH β ∧
      fullPauliSourcePlainGap hH β ≤ fullPauliSourceDampedGap hH β :=
  ⟨fullSourcePlainGap_pos (fullPauliDim_ge_two n hn)
    (fullPauliHamiltonianEigenvalues hH) hβ (fullPauliHamiltonianFamily hH)
    (fullPauliHamiltonianFamily_commutant_scalar hH),
    fullSourceGap_lower (fullPauliDim_ge_two n hn)
      (fullPauliHamiltonianEigenvalues hH) hβ (fullPauliHamiltonianFamily hH)⟩

/-- Full Pauli Source damped Gap pos for the stated finite source data. -/
theorem fullPauliSource_dampedGap_pos (hn : 0 < n) (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) : 0 < fullPauliSourceDampedGap hH β := by
  have h := fullPauliSource_gap_comparison hn hH hβ
  exact lt_of_lt_of_le h.1 h.2

/-- Both gaps have genuine full complex eigenvectors in the same Gibbs
orthogonal unit sphere. -/
theorem fullPauliSource_gap_eigenvectors (hn : 0 < n) (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) :
    (∃ z ∈ fullUnitOrthogonal (fullPauliSourceGibbsVector hH β),
      fullPauliSourceMatrix hH β (fun _ => 1) *ᵥ z =
        (fullPauliSourcePlainGap hH β : ℂ) • z) ∧
    (∃ z ∈ fullUnitOrthogonal (fullPauliSourceGibbsVector hH β),
      fullPauliSourceMatrix hH β (fun ω => 2 * phaseKernel β ω) *ᵥ z =
        (fullPauliSourceDampedGap hH β : ℂ) • z) :=
  ⟨fullSourcePlainGap_eigenvector (fullPauliDim_ge_two n hn)
    (fullPauliHamiltonianEigenvalues hH) hβ (fullPauliHamiltonianFamily hH),
    fullSourceDampedGap_eigenvector (fullPauliDim_ge_two n hn)
      (fullPauliHamiltonianEigenvalues hH) hβ (fullPauliHamiltonianFamily hH)⟩

/-- Full Pauli Source plain Gap le eigenvalue for the stated finite source data. -/
theorem fullPauliSource_plainGap_le_eigenvalue (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) (z : FullCoord (fullPauliDim n) → ℂ) (hz : z ≠ 0)
    (r : ℝ) (hr : r ≠ 0)
    (he : fullPauliSourceMatrix hH β (fun _ => 1) *ᵥ z = (r : ℂ) • z) :
    fullPauliSourcePlainGap hH β ≤ r :=
  fullSourcePlainGap_le_eigenvalue (fullPauliHamiltonianEigenvalues hH) hβ
    (fullPauliHamiltonianFamily hH) z hz r hr he

/-- Full Pauli Source damped Gap le eigenvalue for the stated finite source data. -/
theorem fullPauliSource_dampedGap_le_eigenvalue (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) (z : FullCoord (fullPauliDim n) → ℂ) (hz : z ≠ 0)
    (r : ℝ) (hr : r ≠ 0)
    (he : fullPauliSourceMatrix hH β (fun ω => 2 * phaseKernel β ω) *ᵥ z =
      (r : ℂ) • z) : fullPauliSourceDampedGap hH β ≤ r :=
  fullSourceDampedGap_le_eigenvalue (fullPauliHamiltonianEigenvalues hH) hβ
    (fullPauliHamiltonianFamily hH) z hz r hr he

/-- The same exact plain gap bounds the complete source form with the
normalized Gibbs square root. The proposals keep their original unit scale. -/
theorem fullPauliSource_plainGap_form (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) :
    FormGapAtLeast
      (fun X => ∑ P : FullPauliLabel n,
        (ckgSourcePlainForm β (gibbsDiag (fullPauliHamiltonianEigenvalues hH) β)
          (fullNu (fullPauliHamiltonianEigenvalues hH))
          (fullTransition (fullPauliHamiltonianFamily hH P)) X).re)
      (CFC.sqrt (gibbsDiag (fullPauliHamiltonianEigenvalues hH) β))
      (fullPauliSourcePlainGap hH β) :=
  fullSourcePlainGap_sourceForm (fullPauliHamiltonianEigenvalues hH) hβ
    (fullPauliHamiltonianFamily hH)

/-- Full Pauli Source damped Gap form for the stated finite source data. -/
theorem fullPauliSource_dampedGap_form (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) :
    FormGapAtLeast
      (fun X => ∑ P : FullPauliLabel n,
        (ckgSourceDampedForm β (gibbsDiag (fullPauliHamiltonianEigenvalues hH) β)
          (fullNu (fullPauliHamiltonianEigenvalues hH))
          (fullTransition (fullPauliHamiltonianFamily hH P)) X).re)
      (CFC.sqrt (gibbsDiag (fullPauliHamiltonianEigenvalues hH) β))
      (fullPauliSourceDampedGap hH β) :=
  fullSourceDampedGap_sourceForm (fullPauliHamiltonianEigenvalues hH) hβ
    (fullPauliHamiltonianFamily hH)

end Qatlib.Concepts.GibbsSource.SourceForms
