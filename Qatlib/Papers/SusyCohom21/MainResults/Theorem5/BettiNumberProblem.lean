/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 5 — hardness of the Betti number problem

Cade--Crichigno, fixed arXiv:2107.00011v2, Theorem 5 (page 9): computing the
Betti number `β_l` is #P-hard for `l = Ω(n)`, and #P-complete with an
inverse-polynomial gap above the zero ground space.

Boundary: #P-hardness/#P-completeness are not formalised. This file states the
concrete spectral content: `β = dim ker Δ` equals `dim ker (d + d†)`, the Hodge
kernel is `ker d ∩ ker d†` (Eq. (4.15)), the Laplacian energy is nonnegative,
and under an inverse-polynomial spectral gap every state below the threshold has
exactly zero energy (`spectralGap_energy_zero`), the promise needed for the
completeness direction.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Theorem5

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fixed arXiv:2107.00011v2, Theorem 5 (Eqs. (4.15), (5.2)): `β = dim ker (d+d†)`,
the Hodge kernel characterisation holds, the Laplacian energy is nonnegative, and
an inverse-polynomial gap makes every sub-threshold energy exactly zero. -/
theorem betti_number_problem (C : GradedComplex ι) (q : ℕ)
    (hgap : SpectralGap (laplacian C.d) q) :
    bettiNumber C = kernelDim (C.d + C.dᴴ) ∧
    (∀ ψ : State ι, laplacian C.d *ᵥ ψ = 0 ↔ C.d *ᵥ ψ = 0 ∧ C.dᴴ *ᵥ ψ = 0) ∧
    (∀ ψ : State ι, 0 ≤ energy (laplacian C.d) ψ) ∧
    (∀ ψ : State ι, Normalized ψ → energy (laplacian C.d) ψ < 1 / (q : ℝ) →
      energy (laplacian C.d) ψ = 0) := by
  refine ⟨bettiNumber_eq_kernelDim_shift C, hodge_kernel_characterization C, ?_, ?_⟩
  · intro ψ
    exact energy_nonneg_of_posSemidef (laplacian_posSemidef_of_sq_zero C.sq_zero) ψ
  · intro ψ hψ hlt
    exact spectralGap_energy_zero (laplacian C.d) hgap hψ hlt

end Qatlib.Papers.SusyCohom21.MainResults.Theorem5
