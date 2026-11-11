/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 — SUSY k-local Hamiltonian is in QMA; sparse `Q` suffices

Cade--Crichigno, fixed arXiv:2107.00011v2, Proposition 1 (page 5): the SUSY
`k`-local Hamiltonian problem is in QMA for any constant `k`, and remains in QMA
when the `k`-local restriction is dropped and only sparsity of `Q` is required.

Boundary: the complexity-class membership (QMA) is not formalised. This file
states the concrete mathematical interface used by the QMA protocol: the
Hamiltonian is Hermitian PSD, its zero-energy condition is exactly the
kernel condition on `Q + Q†`, and the energy is the squared norm of
`(Q + Q†)ψ`, for any row-sparse supercharge `Q` (the sparse-access hypothesis).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Proposition1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Proposition 1 (Eq. (3.1)): the SUSY Hamiltonian of
a row-sparse supercharge `Q` is Hermitian PSD, has zero energy exactly on
`ker (Q + Q†)`, and its energy is `‖(Q + Q†)ψ‖²`. -/
theorem susy_klocal_hamiltonian_in_qma
    (k : ℕ) (S : Supercharge ι) (s : ℕ) (_hsparse : RowSparse s S.Q) :
    S.hamiltonian.IsHermitian ∧
    S.hamiltonian.PosSemidef ∧
    (∀ ψ : State ι, energy S.hamiltonian ψ = 0 ↔ S.shift *ᵥ ψ = 0) ∧
    (∀ ψ : State ι, energy S.hamiltonian ψ = normSqVec (S.shift *ᵥ ψ)) := by
  refine ⟨S.hamiltonian_isHermitian, S.hamiltonian_posSemidef, ?_,
    S.energy_hamiltonian_eq_normSq⟩
  intro ψ
  rw [energy_hamiltonian_eq_zero_iff, S.hamiltonian_mulVec_eq_zero_iff]

end Qatlib.Papers.SusyCohom21.MainResults.Proposition1
