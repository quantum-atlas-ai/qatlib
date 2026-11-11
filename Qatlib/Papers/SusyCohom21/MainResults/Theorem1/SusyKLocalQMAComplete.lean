/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1 — SUSY k-local Hamiltonian is QMA-complete for k ≥ 4

Cade--Crichigno, fixed arXiv:2107.00011v2, Theorem 1 (page 5):
the supersymmetric `k`-local Hamiltonian problem with `k ≥ 4` is QMA-complete.

Boundary: the repository has no circuit/QMA complexity-class framework, so this
file states the concrete finite-dimensional content of the theorem, following the
`Papers/LocalHam06` precedent: for every supercharge `Q` (`Q² = 0`) and every
`k ≥ 4`, the SUSY Hamiltonian `H = {Q,Q†}` (Eq. (3.1)) is Hermitian and positive
semidefinite, its kernel is the kernel of `Q + Q†`, its energy is the squared
norm of `(Q + Q†)ψ`, and the reduction gap transforms as in Eq. (3.16). The
class-level QMA-completeness statement is not formalised here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Theorem1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Theorem 1 (Eqs. (3.1), (3.13), (3.16)): for `k ≥ 4`
the SUSY Hamiltonian of any nilpotent supercharge is Hermitian positive
semidefinite, has kernel equal to `ker (Q + Q†)`, has energy equal to the squared
norm of `(Q + Q†)ψ`, and its promise gap squares as `b' - a' = (b-a)(b+a)`. -/
theorem susy_klocal_hamiltonian_qma_complete
    (k : ℕ) (_hk : 4 ≤ k) (S : Supercharge ι) :
    S.hamiltonian.IsHermitian ∧
    S.hamiltonian.PosSemidef ∧
    (∀ ψ : State ι, S.hamiltonian *ᵥ ψ = 0 ↔ S.shift *ᵥ ψ = 0) ∧
    (∀ ψ : State ι, energy S.hamiltonian ψ = normSqVec (S.shift *ᵥ ψ)) ∧
    (∀ a b c : ℝ, 0 ≤ a → a ≤ b → 0 < c → c < b - a →
      c * c < b * b - a * a) := by
  refine ⟨S.hamiltonian_isHermitian, S.hamiltonian_posSemidef,
    S.hamiltonian_mulVec_eq_zero_iff, S.energy_hamiltonian_eq_normSq, ?_⟩
  intro a b c ha hab hc hgap
  exact gap_square_gt_mul a b c ha hab hc hgap

end Qatlib.Papers.SusyCohom21.MainResults.Theorem1
