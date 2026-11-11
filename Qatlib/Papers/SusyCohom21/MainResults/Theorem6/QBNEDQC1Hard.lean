/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 6 — QBNE is DQC1-hard, even for efficiently sample-able `V[m]`

Cade--Crichigno, fixed arXiv:2107.00011v2, Theorem 6 (page 13): Quantum Betti
Number Evaluation (QBNE) is DQC1-hard for `d = O(log m)`, `l = Θ(m)`, even when
`V[m]` is efficiently sample-able.

Boundary: DQC1-hardness and the sampling model are not formalised. This file
states the concrete spectral mechanism of the reduction: because `H = (Q + Q†)²`
(Eq. (5.6)), the energies of `H` are the squares of the eigenvalues of the
Hermitian `Q + Q†` with the same eigenvectors; the characteristic polynomial is
`∏ (X - λᵢ²)`; and the promise gap squares per Eq. (3.16).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Theorem6

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Theorem 6 (Eqs. (5.6), (3.16)): the SUSY
Hamiltonian `H = (Q + Q†)²` has the squared spectrum of `Q + Q†` with the same
eigenvectors, characteristic polynomial `∏ (X - λᵢ²)`, and the promise gap
squares as in Eq. (3.16). -/
theorem qbne_dqc1_hard (S : Supercharge ι) :
    (∀ i, S.hamiltonian *ᵥ ⇑(S.shift_isHermitian.eigenvectorBasis i)
        = ((S.shift_isHermitian.eigenvalues i) *
            (S.shift_isHermitian.eigenvalues i) : ℝ) •
            ⇑(S.shift_isHermitian.eigenvectorBasis i)) ∧
    S.hamiltonian.charpoly = ∏ i, (Polynomial.X - Polynomial.C
        ((S.shift_isHermitian.eigenvalues i : ℂ) *
          (S.shift_isHermitian.eigenvalues i : ℂ))) ∧
    (∀ a b c : ℝ, 0 ≤ a → a ≤ b → 0 < c → c < b - a →
      c * c < b * b - a * a) := by
  obtain ⟨hspec, hchar⟩ := hamiltonian_spectrum_square S
  refine ⟨hspec, hchar, ?_⟩
  intro a b c ha hab hc hgap
  exact gap_square_gt_mul a b c ha hab hc hgap

end Qatlib.Papers.SusyCohom21.MainResults.Theorem6
