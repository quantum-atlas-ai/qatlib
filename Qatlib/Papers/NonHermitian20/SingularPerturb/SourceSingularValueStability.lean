/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2.3 — stability of singular value spectra (Non-Hermitian Physics)

Fixed arXiv:2006.01837v3 (Adv. Phys. review, 2020). Theorem 2.3, Eq. (45), p.14.

For arbitrary `n × n` complex matrices `M` and `E`, the `j`-th largest singular value
`σ_j` of `M` and `σ'_j` of `M + E` satisfy `|σ'_j - σ_j| ≤ ‖E‖`.

The paper derives this by Hermitianising (Eq. (42)) and applying Weyl's perturbation
theorem. The library already contains the rectangular Weyl/Mirsky theorem for the ordered
standard singular-value sequence; the paper's square statement is the special case with
`B = M + E`, using `M - (M + E) = -E` and `‖-E‖ = ‖E‖`.

The rectangular theorem is
`Qatlib.Concepts.SpectralSketch.SpectrumPerturb.rectangular_singular_weyl_and_mirsky`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.NonHermitian20.SingularPerturb

/-- Fixed arXiv:2006.01837v3, Theorem 2.3, Eq. (45), p.14.

For arbitrary `n × n` complex matrices `M`, `E`, every ordered singular value of `M + E`
differs from the corresponding singular value of `M` by at most the operator norm `‖E‖`.
`matrixSingularValues` is `ℕ`-indexed; for `j ≥ n` both sides are the zero tail
(`matrixSingularValues_of_card_le`), which is a harmless extension of the paper's
`j = 1, …, n`. -/
theorem theorem_2_3_singular_value_stability (ι : Type) [Fintype ι] [DecidableEq ι]
    (M E : Matrix ι ι ℂ) :
    ∀ j : ℕ, |matrixSingularValues M j - matrixSingularValues (M + E) j| ≤ ‖E‖ := by
  intro j
  have h := (rectangular_singular_weyl_and_mirsky ι ι M (M + E)).1 j
  have hsub : M - (M + E) = -E := by abel
  rwa [hsub, norm_neg] at h

end Qatlib.Papers.NonHermitian20.SingularPerturb
