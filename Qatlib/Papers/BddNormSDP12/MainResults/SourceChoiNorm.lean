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
# `SourceChoiNorm` — Theorem 6 (Choi–Jamiołkowski representation), claim c005

Watrous, *Simpler semidefinite programs for completely bounded norms*,
fixed arXiv:1207.5726v2 (2012), Theorem 6, p.10.

Theorem 6: for a linear map `Φ ∈ T(X, Y)` with Choi–Jamiołkowski representation
`J(Φ) ∈ L(Y ⊗ X)`,

`|||Φ|||₁ = max { ‖(1_Y ⊗ √ρ₀) J(Φ) (1_Y ⊗ √ρ₁)‖₁ : ρ₀, ρ₁ ∈ D(X) }`.

The Frozen definition `diamondChoiValue T` is exactly the two-density Choi
supremum of `diamondChoiScore`, and `diamondChoiScore T ρ σ` is by definition the
sandwiched trace norm shown above. `finiteDiamondNorm_eq_choi` identifies the raw
finite-reference norm with this supremum; `diamondChoi_attained` upgrades it to a
maximum at positive input dimension.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ENNReal

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceChoiNorm

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace.CompletelyPositive
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.RandCompile.ChannelBudget

/-- Fixed arXiv:1207.5726v2 Theorem 6, p.10, supremum form. For every linear map
`Φ` the completely bounded trace norm equals the two-density Choi supremum
`⨆_{ρ₀,ρ₁∈D(X)} ‖(1_Y ⊗ √ρ₀) J(Φ) (1_Y ⊗ √ρ₁)‖₁`, with empty registers retained
as empty suprema. Reuses `finiteDiamondNorm_eq_choi`. -/
theorem choi_sup_norm {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondNorm T = diamondChoiValue T :=
  finiteDiamondNorm_eq_choi T

/-- Fixed arXiv:1207.5726v2 Theorem 6, p.10, maximum form. At positive input
dimension the supremum is attained: there are densities `ρ, σ` with
`|||Φ|||₁ = ‖(1_Y ⊗ √ρ) J(Φ) (1_Y ⊗ √σ)‖₁`. Reuses `diamondChoi_attained`, whose
returned score `diamondChoiScore T ρ σ` unfolds to exactly the displayed
sandwiched trace norm. -/
theorem choi_max_norm {D E : ℕ} (hD : 0 < D) (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ ρ σ : DensityInput D,
      finiteDiamondNorm T = ENNReal.ofReal
        (Matrix.traceNorm (Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat *
          MatrixMap.choi_matrix T * Matrix.kronecker (1 : Operator E) σ.val.sqrt.mat)) := by
  obtain ⟨ρ, σ, hnorm, -⟩ := diamondChoi_attained hD T
  exact ⟨ρ, σ, by rw [hnorm, diamondChoiScore]⟩

end Qatlib.Papers.BddNormSDP12.MainResults.SourceChoiNorm
