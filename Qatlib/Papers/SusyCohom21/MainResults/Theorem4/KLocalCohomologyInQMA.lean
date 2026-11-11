/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4 — k-local Cohomology is in QMA for cochain complexes

Cade--Crichigno, fixed arXiv:2107.00011v2, Theorem 4 (page 5): `k`-local
Cohomology is contained in QMA for cochain complexes `(V[m], d[k])`.

Boundary: QMA containment is not formalised. This file states the concrete
mathematical interface used by the QMA protocol: on a graded cochain complex
the Laplacian `Δ = dd† + d†d` is Hermitian positive semidefinite, its energy is
the squared norm of `(d + d†)ψ` (Eq. (5.6)), and zero energy is equivalent to
lying in the kernel of `Δ` (Eq. (4.15)).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Theorem4

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Theorem 4 (Eqs. (4.15), (5.6)): the cohomology
Laplacian is Hermitian PSD, has energy `‖(d + d†)ψ‖²`, and has zero energy
exactly on its kernel. -/
theorem klocal_cohomology_in_qma (C : GradedComplex ι) :
    (laplacian C.d).IsHermitian ∧
    (laplacian C.d).PosSemidef ∧
    (∀ ψ : State ι, energy (laplacian C.d) ψ = normSqVec ((C.d + C.dᴴ) *ᵥ ψ)) ∧
    (∀ ψ : State ι, energy (laplacian C.d) ψ = 0 ↔ laplacian C.d *ᵥ ψ = 0) := by
  refine ⟨laplacian_isHermitian C.sq_zero, laplacian_posSemidef_of_sq_zero C.sq_zero,
    energy_laplacian_eq_normSq C.sq_zero, laplacian_energy_eq_zero_iff C.sq_zero⟩

end Qatlib.Papers.SusyCohom21.MainResults.Theorem4
