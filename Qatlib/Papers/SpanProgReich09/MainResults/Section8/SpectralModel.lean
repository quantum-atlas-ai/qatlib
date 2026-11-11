/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral helpers for Section 8

Paper: Ben W. Reichardt, arXiv:0904.2759v1, Section 8 (Definition 8.1,
Eqs. (8.1)-(8.4)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.SpanProgReich09.MainResults.Section8

/-- An eigenvector of a complex matrix with real eigenvalue `ρ`. -/
def IsEigenvector {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) (ρ : ℝ) (ψ : ι → ℂ) : Prop :=
  ψ ≠ 0 ∧ A *ᵥ ψ = fun i => (ρ : ℂ) * ψ i

/-- The squared norm `∑ ‖ψ_i‖²` of a complex vector. -/
def normSq {ι : Type} [Fintype ι] (ψ : ι → ℂ) : ℝ := ∑ i, ‖ψ i‖ ^ 2

/-- The squared length of the projection of the basis vector at `o` onto the
eigenvectors with `|ρ| ≤ threshold`, for a complete orthonormal eigenframe `V`. -/
def spectralMass {ι : Type} [Fintype ι] {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (ρ : Fin k → ℝ) (threshold : ℝ) (o : ι) : ℝ :=
  ∑ i : Fin k, if |ρ i| ≤ threshold then ‖V o i‖ ^ 2 else 0

/-- The entrywise absolute value `abs(A)` of a complex matrix (paper §9,
`abs(A_G)`). -/
def absMatrix {ι κ : Type} (A : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  fun i j => ((‖A i j‖ : ℝ) : ℂ)

end Qatlib.Papers.SpanProgReich09.MainResults.Section8
