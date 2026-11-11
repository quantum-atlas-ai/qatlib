/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2 — SUSY 4-local Hamiltonian is QMA-hard

Cade--Crichigno, fixed arXiv:2107.00011v2, Theorem 2 (page 5): the SUSY
`4`-local Hamiltonian problem is QMA-hard.

Boundary: the QMA-hardness reduction is not formalised. This file states the
concrete spectral content used by the reduction for an arbitrary Hermitian
operator `A` playing the role of the local gadget (`Q + Q†`): the squared
operator `A²` is Hermitian positive semidefinite, has the same kernel as `A`
(so `β = #zero eigenvalues`), has characteristic polynomial equal to the product
of `X - λᵢ²`, and the promise gap squares per Eq. (3.16).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Theorem2

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Theorem 2 (Eqs. (3.13), (3.16)): for Hermitian `A`,
the squared operator `A²` is Hermitian PSD, preserves the kernel dimension,
has eigenvalues `λᵢ²` (via its characteristic polynomial), and the promise gap
squares as in Eq. (3.16). -/
theorem susy_four_local_hamiltonian_qma_hard
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A * A).IsHermitian ∧
    (A * A).PosSemidef ∧
    kernelDim (A * A) = kernelDim A ∧
    (A * A).charpoly = ∏ i, (Polynomial.X - Polynomial.C
        ((hA.eigenvalues i : ℂ) * (hA.eigenvalues i : ℂ))) ∧
    (∀ a b c : ℝ, 0 ≤ a → a ≤ b → 0 < c → c < b - a →
      c * c < b * b - a * a) := by
  refine ⟨mul_self_isHermitian hA, ?_, kernelDim_mul_self_of_isHermitian A hA,
    charpoly_mul_self_of_isHermitian A hA, ?_⟩
  · have hsquare : A * A = A * Aᴴ := by rw [hA.eq]
    rw [hsquare]
    exact Matrix.posSemidef_self_mul_conjTranspose A
  · intro a b c ha hab hc hgap
    exact gap_square_gt_mul a b c ha hab hc hgap

end Qatlib.Papers.SusyCohom21.MainResults.Theorem2
