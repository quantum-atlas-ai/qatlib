/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm

open Qatlib.Concepts.SchattenDiamond.DiamondNorm

set_option backward.isDefEq.respectTransparency false

/-!
# `SourceMaxOutputFidelity` — §2.3 maximum-output-fidelity SDP (claim c004)

Watrous, *Simpler semidefinite programs for completely bounded norms*,
fixed arXiv:1207.5726v2 (2012), §2.3 "Optimal value", p.9 (with Theorem 5 on
pp.7–8).

With a Stinespring representation `Φ(X) = Tr_Z(A₀ X A₁*)` and complementary
outputs `Ψ₀(X) = Tr_Y(A₀ X A₀*)`, `Ψ₁(X) = Tr_Y(A₁ X A₁*)`, the §2.3 program has
primal objective `½Tr(X) + ½Tr(X*) = Re Tr X` subject to
`[[Ψ₀(ρ₀), X], [X*, Ψ₁(ρ₁)]] ⪰ 0`, `ρ₀, ρ₁ ∈ D(X)`.

The paper proves:

* for each fixed `ρ₀, ρ₁` the primal optimum equals `F(Ψ₀(ρ₀), Ψ₁(ρ₁))`;
* maximizing over densities gives `F_max(Ψ₀, Ψ₁) = |||Φ|||₁` (Theorem 5).

Both facts are stated below. The fixed-pair statement is the literal fidelity
SDP of §2.1 with `P = Ψ₀(ρ₀)`, `Q = Ψ₁(ρ₁)`, discharged by
`fidelity_source_rootFidelity`. The global statement reuses
`stinespringSource_norm_primal_attained` (primal LUB of the actual Stinespring
program equals `finiteDiamondNorm`) and `finiteDiamondNorm_stinespring`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ENNReal ComplexOrder

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceMaxOutputFidelity

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.RandCompile.ChannelBudget

/-- Fixed arXiv:1207.5726v2 §2.3 "Optimal value", p.9, fixed-density half. For a
Stinespring factor `A` and density `ρ`, `Ψ₀(ρ) = stinespringComplement A ρ`.
For every pair of densities `ρ, σ`, the fixed-diagonal fidelity SDP over
`[[Ψ₀(ρ), X], [X*, Ψ₁(σ)]] ⪰ 0` with objective `Re Tr X` has primal optimum
`F(Ψ₀(ρ), Ψ₁(σ)) = rootFidelity (Ψ₀ ρ) (Ψ₁ σ)`, the dual infimum equal to the
same value, and the primal optimum attained. Reuses `fidelity_source_rootFidelity`
with the actual complementary outputs supplied by `stinespringComplement_nonneg`. -/
theorem fixed_density_primal_value {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (ρ σ : DensityInput D) :
    IsLUB (fidelityPrimalValues (stinespringComplement A ρ.val)
          (stinespringComplement B σ.val))
        (rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val)) ∧
      IsGLB (fidelityDualValues (stinespringComplement A ρ.val)
          (stinespringComplement B σ.val))
        (rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val)) ∧
      ∃ X : Matrix Z Z ℂ,
        (Matrix.fromBlocks (stinespringComplement A ρ.val).mat X Xᴴ
          (stinespringComplement B σ.val).mat).PosSemidef ∧
        (Matrix.trace X).re =
          rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val) :=
  fidelity_source_rootFidelity (stinespringComplement_nonneg A ρ.property.1)
    (stinespringComplement_nonneg B σ.property.1)

/-- Fixed arXiv:1207.5726v2 §2.3 p.9 and Theorem 5 pp.7–8, global half. For
positive input dimension, maximizing the fixed-density primal value over all
density pairs gives `F_max(Ψ₀, Ψ₁) = maxOutputRootFidelity A B = |||Φ|||₁`, and an
actual density pair together with an actual cross block attains the optimal
value of the literal Stinespring program. Reuses
`stinespringSource_norm_primal_attained` and `finiteDiamondNorm_stinespring`. -/
theorem max_output_fidelity_norm {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hD : 0 < D) (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    maxOutputRootFidelity A B = finiteDiamondNorm (stinespringCross A B) ∧
      ∃ (α : ℝ) (ρ σ : DensityInput D) (X : Matrix Z Z ℂ),
        finiteDiamondNorm (stinespringCross A B) = ENNReal.ofReal α ∧
        (fidelityPrimalBlock (stinespringComplement A ρ.val)
          (stinespringComplement B σ.val) X).mat.PosSemidef ∧
        IsLUB (stinespringSourcePrimalValues A B) α ∧
        IsGLB (stinespringProgram A B).dualValues α ∧
        (Matrix.trace X).re = α := by
  refine ⟨(finiteDiamondNorm_stinespring A B).symm, ?_⟩
  obtain ⟨α, ρ, σ, X, hnorm, hX, hlub, hglb, htr⟩ :=
    stinespringSource_norm_primal_attained hD A B
  exact ⟨α, ρ, σ, X, hnorm, hX, hlub, hglb, htr⟩

end Qatlib.Papers.BddNormSDP12.MainResults.SourceMaxOutputFidelity
