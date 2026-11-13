/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Weak entropy factorization (claim c007)

Lemma 2.5 of arXiv:2412.01732v1 (p.5, eq. (5)):

`D_ABC(ρ‖σ) ≤ D_AB(ρ‖σ) + D_BC(ρ‖σ) + ‖H_σ(A:C|D)‖∞`

for `ρ, σ` states on `H_A ⊗ H_B ⊗ H_C ⊗ H_D` with `σ > 0`, where `D_X` is
the conditional relative entropy of Definition 2.4, eq. (4), and
`‖H_σ(A:C|D)‖∞` is the operator norm of the MCMI of Definition 2.2, eq. (2).

The marginal maps (`mABC` marginalises onto `A ⊗ B ⊗ C`, `mAB` onto
`A ⊗ B`, `mBC` onto `B ⊗ C`) are explicit data whose intended instances are
the partial traces of the source model; `mcmiNorm` is the value
`‖H_σ(A:C|D)‖∞` for the fixed state `σ`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.Entropy

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

variable {I JABC JAB JBC : Type} [Fintype I] [DecidableEq I]
  [Fintype JABC] [DecidableEq JABC] [Fintype JAB] [DecidableEq JAB]
  [Fintype JBC] [DecidableEq JBC]

/-- **Lemma 2.5 (Weak entropy factorization)**, arXiv:2412.01732v1 p.5,
eq. (5). For states `ρ, σ` on a four-partite system `H_A ⊗ H_B ⊗ H_C ⊗ H_D`
with `σ > 0`:

`D_ABC(ρ‖σ) ≤ D_AB(ρ‖σ) + D_BC(ρ‖σ) + ‖H_σ(A:C|D)‖∞`.

The three conditional relative entropies are `condRelEnt` with the
corresponding partial-trace maps; `mcmiNorm` is `‖H_σ(A:C|D)‖∞` and
`hσ` records the positivity hypothesis `σ > 0`. -/
def weak_entropy_factorization (mABC : Density I → Density JABC)
    (mAB : Density I → Density JAB) (mBC : Density I → Density JBC)
    (ρ σ : Density I) (hσ : σ.val.PosDef) (mcmiNorm : ℝ)  : Prop :=
    condRelEnt mABC ρ σ ≤ condRelEnt mAB ρ σ + condRelEnt mBC ρ σ + mcmiNorm
  -- Source: arXiv:2412.01732v1, Lemma 2.5 (p.5, eq. (5)); proof in Lemma B.1
  -- (Appendix B.1).
  -- Proof route (Lemma B.1): expand the three conditional relative entropies
  -- using Definition 2.4, move `D(ρ_CD‖σ_CD) + D(ρ_AD‖σ_AD) − D(ρ_D‖σ_D)` to
  -- the left, and bound the resulting trace expression by Hoelder's inequality
  -- for Schatten norms against `‖H_σ(A:C|D)‖∞`; data processing
  -- (monotonicity of relative entropy under the partial trace onto `D`) gives
  -- the sign of the remaining term.
  -- Scope: the matrix-level MCMI (partial traces of `CFC.log` padded by
  -- Kronecker identities, Definition 2.2) is represented by the interface datum
  -- `mcmiNorm`; the marginal maps are likewise abstract rather than the concrete
  -- `ptraceD`/`ptraceL` composites of `Model`.  The analytic ingredient is
  -- Hölder's inequality for Schatten norms.  A full proof expands the concrete
  -- MCMI operator, establishes
  -- `condRelABC - condRelAB - condRelBC = ⟪σ, H_σ(A:C|D)⟫`, and applies the
  -- operator-norm/Schatten-1 duality.

end Qatlib.Papers.GibbsSampling25.MainResults.Entropy
