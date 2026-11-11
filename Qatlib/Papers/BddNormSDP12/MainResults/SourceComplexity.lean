/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm

open Qatlib.Concepts.SchattenDiamond.DiamondNorm

set_option backward.isDefEq.respectTransparency false

/-!
# `SourceComplexity` — §4 explicit interior radii, dual size bounds and near-optimal witnesses (claim c006)

Watrous, *Simpler semidefinite programs for completely bounded norms*,
fixed arXiv:1207.5726v2 (2012), §4 "Remarks on the complexity of approximating
optimal solutions to the semidefinite programs", pp.13–14.

The paper's formalizable content in §4 is:

* a polynomial, efficiently computable lower bound on the interior parameter `ε`
  for which `D^∘_ε` (the strict dual interior ball) is nonempty. For the
  maximum-output-fidelity program this is
  `ε = 1 / (4 (1 + ‖Ψ₀*(1)‖∞ + ‖Ψ₁*(1)‖∞))` (p.13);
* a dual trace (hence Frobenius) size bound, which for the Choi-representation
  program is `R = 2 ‖J(Φ)‖∞ dim(X) dim(Y)` (p.14);
* the resulting δ-near-optimal dual witness with explicit polynomial size.

The final sentence — that the cited [GLS93]/[Lov03] ellipsoid framework turns
these bounds into a polynomial-time algorithm in the input size and `log(1/δ)` —
is an *external* citation: Frozen has no model of a numerical SDP solver or of
runtime. That sentence is *not* formalized here; see the module docstring of the
claim table. The three quantitative statements the paper itself establishes are
proved below.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceComplexity

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace.CompletelyPositive
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.RandCompile.ChannelBudget

/-- Fixed arXiv:1207.5726v2 §4, p.13. The certified Stinespring interior radius
is exactly `1 / (4 (1 + ‖Ψ₀*(1)‖∞ + ‖Ψ₁*(1)‖∞))` (with
`Ψᵢ* = stinespringComplementLinear ⋯ .adjoint`, so `Ψᵢ*(1)` is the adjoint of the
identity), and the perturbation scale times this radius is `1/4`. Reuses
`stinespringInteriorRadius_scale`. -/
theorem stinespring_interior_radius {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    stinespringInteriorRadius A B =
        (4 * (1 + ‖((stinespringComplementLinear A).adjoint 1).mat‖ +
          ‖((stinespringComplementLinear B).adjoint 1).mat‖))⁻¹ ∧
      stinespringPerturbationScale A B * stinespringInteriorRadius A B = (1/4 : ℝ) := by
  refine ⟨?_, stinespringInteriorRadius_scale A B⟩
  unfold stinespringInteriorRadius stinespringPerturbationScale
  rfl

/-- Fixed arXiv:1207.5726v2 §4, p.14, Choi-representation size bound. At positive
input dimension the actual optimal dual variable `y` of the Choi program satisfies
the explicit polynomial bound `‖y‖ ≤ 2 ‖J(Φ)‖ dim(X) dim(Y)`, and the primal and
dual optima coincide at a finite `α` with `0 ≤ α ≤ dim(Y) ‖J(Φ)‖`. This is the
Frozen form of the paper's `R = 2‖J(Φ)‖∞ dim(X) dim(Y)` trace bound (the Hilbert
norm controls the Frobenius norm of the dual data). Reuses
`diamondProgram_bounded_optimizers`. -/
theorem choi_dual_size_bound {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ (α : ℝ) (y : DiamondConstraints D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
        (diamondProgram T).DualFeasible y ∧
        (diamondProgram T).dualScore y = α ∧
        0 ≤ α ∧ α ≤ E * ‖MatrixMap.choi_matrix T‖ ∧
        ‖y‖ ≤ 2 * ‖MatrixMap.choi_matrix T‖ * D * E := by
  obtain ⟨α, M, y, hnorm, hM, hy, hp, hd, hsM, hsy, hlo, hu, hsize⟩ :=
    diamondProgram_bounded_optimizers hD T
  exact ⟨α, y, hnorm, hy, hsy, hlo, hu, hsize⟩

/-- Fixed arXiv:1207.5726v2 §4, p.14 (with p.13). For every accuracy `δ > 0`
there is an actual dual feasible `δ`-near-optimal witness for the Choi program
with explicit polynomial size bound `‖z‖ ≤ (dim X + 1) (dim Y ‖J(Φ)‖ + δ)`; the
primal optimum is `α`, the witness score lies in `[α, α + δ)`, and the dual stays
feasible. This is the mathematical content from which the paper's cited
[GLS93]/[Lov03] runtime conclusion follows. Reuses
`diamondProgram_near_optimal_ball` and `diamondRoundingRadius_pos`. -/
theorem delta_near_optimal_witness {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (α : ℝ) (z : DiamondConstraints D E),
      finiteDiamondNorm T = ENNReal.ofReal α ∧
        (diamondProgram T).DualFeasible z ∧
        α ≤ (diamondProgram T).dualScore z ∧
        (diamondProgram T).dualScore z < α + δ ∧
        ‖z‖ ≤ (D + 1 : ℝ) * (E * ‖MatrixMap.choi_matrix T‖ + δ) := by
  obtain ⟨α, M, z, hnorm, hM, hsM, hlo, hu, hp, hd, hball⟩ :=
    diamondProgram_near_optimal_ball hD T hδ
  obtain ⟨-, hpd, hlower, hupper, hsize⟩ := hball 0 (by
    rw [norm_zero]
    exact (diamondRoundingRadius_pos T hδ).le)
  refine ⟨α, z, hnorm, ?_, ?_, ?_, ?_⟩
  · have hfeas : (diamondProgram T).DualFeasible (z + 0) :=
      HermitianMat.zero_le_iff.mpr hpd.posSemidef
    simpa using hfeas
  · simpa using hlower
  · simpa using hupper
  · simpa using hsize

end Qatlib.Papers.BddNormSDP12.MainResults.SourceComplexity
