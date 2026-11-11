/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs

set_option backward.isDefEq.respectTransparency false

/-!
# `SourceSlater` — Theorem 1 (Slater's theorem), claim c002

Watrous, *Simpler semidefinite programs for completely bounded norms*,
fixed arXiv:1207.5726v2 (2012), Theorem 1, p.4.

The paper uses the equality-form semidefinite program `(Ξ, C, D)` with
`Ξ : L(X) → L(Y)` Hermiticity preserving, `C ∈ Herm(X)`, `D ∈ Herm(Y)` and the
primal/dual pair

* primal: maximize `⟨C, X⟩` subject to `Ξ(X) = D`, `X ⪰ 0`;
* dual:   minimize `⟨D, Y⟩` subject to `Ξ*(Y) ⪰ C`, `Y ∈ Herm(Y)`.

Frozen's `Program I F` is exactly this equality-form program: `constraint = Ξ`,
`rhs = D`, `objective = C`, `PrimalFeasible X = (0 ≤ X ∧ Ξ X = D)`, and
`DualFeasible y = (0 ≤ Ξ*(y) - C)`.

Both implications of Theorem 1 are restated here as a single paper-shaped
theorem and discharged by the Frozen strong-duality results.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceSlater

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding

variable {I F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Fixed arXiv:1207.5726v2 Theorem 1, p.4 (both implications), for the
equality-form program `P` with `constraint = Ξ`, `rhs = D`, `objective = C`.

1. If `P ≠ ∅` (there is a primal feasible `X`) and there is a Hermitian `Y` with
   `Ξ*(Y) > C` (`P.DualSlater`), then `α = β` and some primal feasible `X`
   attains `α`.
2. If `D ≠ ∅` (there is a dual feasible `y`) and there is a positive definite `X`
   with `Ξ(X) = D` (`P.PrimalSlater`), then `α = β` and some dual feasible `y`
   attains `β`.

Reuses `Program.dualSlater_strong_duality` for branch 1 and
`Program.primalSlater_strong_duality` for branch 2. -/
theorem slater_two_branches (P : Program I F) :
    ((∃ X : HermitianMat I ℂ, P.PrimalFeasible X) → P.DualSlater →
        ∃ α : ℝ, IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
          ∃ X : HermitianMat I ℂ, P.PrimalFeasible X ∧ P.primalScore X = α) ∧
    ((∃ y : F, P.DualFeasible y) → P.PrimalSlater →
        ∃ α : ℝ, IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
          ∃ y : F, P.DualFeasible y ∧ P.dualScore y = α) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨X₀, hX₀⟩ hslater
    exact Program.dualSlater_strong_duality P hslater hX₀
  · rintro ⟨y₀, hy₀⟩ hslater
    exact Program.primalSlater_strong_duality P hslater hy₀

end Qatlib.Papers.BddNormSDP12.MainResults.SourceSlater
