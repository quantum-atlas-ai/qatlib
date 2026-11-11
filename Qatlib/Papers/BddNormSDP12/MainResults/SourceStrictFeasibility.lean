/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs

set_option backward.isDefEq.respectTransparency false

/-!
# `SourceStrictFeasibility` — §3.2 strict primal/dual feasibility (claim c008)

Watrous, *Simpler semidefinite programs for completely bounded norms*,
fixed arXiv:1207.5726v2 (2012), §3.2 "Strong duality", p.11.

For the Choi–Jamiołkowski semidefinite program of §3, the paper shows that strict
primal and strict dual feasibility hold for every mapping `Φ`; consequently, in
addition to strong duality, both the primal and the dual optima are achieved by
feasible solutions.

The explicit strict points in the paper are

* primal `X = (1_X / dim X) ⊕ (1_X / dim X) ⊕ (1_Y ⊗ 1_X / dim X) ⊕ (1_Y ⊗ 1_X / dim X)`
  (a uniform positive diagonal block with zero cross block);
* dual `Y = Y₀ = Y₁ = (‖J(Φ)‖∞/2 + 1) • 1_{Y⊗X}`, `λ = 1 + (‖J(Φ)‖∞/2 + 1) dim(Y)`.

Frozen realizes these as `diamondProgram_primal_strict` (positive input
dimension), `diamondProgram_dual_strict` (all maps), and combines them with
`diamondProgram_both_optimizers`.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceStrictFeasibility

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

/-- Fixed arXiv:1207.5726v2 §3.2, p.11. For positive input dimension, the
Choi-representation program satisfies strict primal feasibility and strict dual
feasibility simultaneously, and the common optimal value `α` is attained by an
actual primal feasible `M` and an actual dual feasible `y`. This is the paper's
"strict primal and strict dual feasibility hold ... the primal and dual optima are
achieved". Reuses `diamondProgram_primal_strict`, `diamondProgram_dual_strict`
and `diamondProgram_both_optimizers`.

The zero input dimension is not covered by the primal strict point (the uniform
density `(1/D) • 1` is undefined), matching the paper's implicit `X = ℂ^n`,
`n ≥ 1`. -/
theorem choi_program_strict_feasibility {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    (diamondProgram T).PrimalSlater ∧ (diamondProgram T).DualSlater ∧
      ∃ (α : ℝ) (M : HermitianMat (DiamondRegister D E) ℂ)
        (y : DiamondConstraints D E),
        (diamondProgram T).PrimalFeasible M ∧
          (diamondProgram T).DualFeasible y ∧
          IsLUB (diamondProgram T).primalValues α ∧
          IsGLB (diamondProgram T).dualValues α ∧
          (diamondProgram T).primalScore M = α ∧
          (diamondProgram T).dualScore y = α := by
  refine ⟨diamondProgram_primal_strict hD T, diamondProgram_dual_strict T, ?_⟩
  obtain ⟨α, M, y, hM, hy, hp, hd, hsM, hsy⟩ := diamondProgram_both_optimizers hD T
  exact ⟨α, M, y, hM, hy, hp, hd, hsM, hsy⟩

end Qatlib.Papers.BddNormSDP12.MainResults.SourceStrictFeasibility
