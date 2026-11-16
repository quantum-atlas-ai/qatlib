/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceRayleighGap

@[expose] public section


/-! # Least positive eigenvalue interpretation of the exact gap

Hermitian symmetry and Gibbs annihilation force every nonzero-eigenvalue
eigenvector into the Gibbs-orthogonal space. Together with the attained
minimizing eigenvector, this identifies a positive exact Rayleigh gap as
the least positive real eigenvalue, without an eigenvalue indexing convention.
-/



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- Full Hermitian eigenvector orthogonal for the stated finite source data. -/
theorem fullHermitian_eigenvector_orthogonal {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (g z : ι → ℂ) (hMg : M *ᵥ g = 0)
    (c : ℂ) (hc : c ≠ 0) (he : M *ᵥ z = c • z) : star g ⬝ᵥ z = 0 := by
  have ho : star g ⬝ᵥ (M *ᵥ z) = 0 := by
    rw [fullHermitian_starDot hM g z, hMg]
    simp
  rw [he, dotProduct_smul, smul_eq_mul] at ho
  exact (mul_eq_zero.mp ho).resolve_left hc

/-- Full Rayleigh Gap le nonzero eigenvalue for the stated finite source data. -/
theorem fullRayleighGap_le_nonzero_eigenvalue {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (g z : ι → ℂ) (hMg : M *ᵥ g = 0) (hz : z ≠ 0)
    (r : ℝ) (hr : r ≠ 0) (he : M *ᵥ z = (r : ℂ) • z) :
    fullRayleighGap M g ≤ r := by
  classical
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  exact fullRayleighGap_le_eigenvalue g z hz
    (fullHermitian_eigenvector_orthogonal hM g z hMg r hrc he) r he

end Qatlib.Concepts.GibbsSource.SourceForms
