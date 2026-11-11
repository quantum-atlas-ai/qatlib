/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3 — 4-local Cohomology is QMA₁-hard

Cade--Crichigno, fixed arXiv:2107.00011v2, Theorem 3 (page 5): the `4`-local
Cohomology problem is QMA₁-hard.

Boundary: QMA₁-hardness is not formalised. This file states the concrete Hodge
content of the reduction on a graded cochain complex `(V, d)` with `d² = 0`:
the Laplacian is the square `Δ = (d + d†)²`, its kernel is the simultaneous
kernel of `d` and `d†` (Eq. (4.15)), the Betti number `β = dim ker Δ` equals
`dim ker (d + d†)`, and the promise gap squares per Eq. (3.16).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Theorem3

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Theorem 3 (Eqs. (4.15), (5.6)): on a graded
cochain complex, `Δ = (d + d†)²`, `ker Δ = ker d ∩ ker d†`, the Betti number
equals `dim ker (d + d†)`, and the promise gap squares as in Eq. (3.16). -/
theorem four_local_cohomology_qma1_hard (C : GradedComplex ι) :
    laplacian C.d = (C.d + C.dᴴ) * (C.d + C.dᴴ) ∧
    (∀ ψ : State ι, laplacian C.d *ᵥ ψ = 0 ↔ C.d *ᵥ ψ = 0 ∧ C.dᴴ *ᵥ ψ = 0) ∧
    bettiNumber C = kernelDim (C.d + C.dᴴ) ∧
    (∀ a b c : ℝ, 0 ≤ a → a ≤ b → 0 < c → c < b - a →
      c * c < b * b - a * a) := by
  refine ⟨laplacian_eq_shift_sq C.sq_zero, hodge_kernel_characterization C,
    bettiNumber_eq_kernelDim_shift C, ?_⟩
  intro a b c ha hab hc hgap
  exact gap_square_gt_mul a b c ha hab hc hgap

end Qatlib.Papers.SusyCohom21.MainResults.Theorem3
