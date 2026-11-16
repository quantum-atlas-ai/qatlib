/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BddNormSDP12.MainResults.SourceChoiNorm

@[expose] public section


set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal BigOperators ComplexOrder
namespace Qatlib.Papers.BddNormSDP12.MainResults
open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace.CompletelyPositive
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

/-- A unit joint vector of `X ⊗ X` with `X = ℂ^D`: the pair `u v*` ranges over the
rank-one operators of trace norm one. Fixed arXiv:1207.5726v2 Eq. (2), p.3. -/
def UnitJoint (D : ℕ) : Type :=
  {u : Fin D × Fin D → ℂ // ∑ a, star (u a) * u a = 1}

/-- The value `‖(Φ ⊗ 1)(u v*)‖₁` attached to a pair of joint vectors, as an
extended nonnegative real (so that the supremum over an empty space is `0`).
Fixed arXiv:1207.5726v2 Eq. (2), p.3. -/
def rankOneValue {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (u v : Fin D × Fin D → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.traceNorm (tensorLeft T (fun a b => u a * star (v b))))

/-- Supremum of `rankOneValue` over unit joint vectors, i.e. the right-hand side
of Eq. (2) written as an extended-real supremum. Fixed arXiv:1207.5726v2, p.3. -/
def rankOneSup {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ u : UnitJoint D, ⨆ v : UnitJoint D, rankOneValue T u.1 v.1

/-- Fixed arXiv:1207.5726v2 §1 Eq. (2), p.3. Every trace-norm-one operator
`X ∈ X ⊗ X` is a convex combination of rank-one operators `u v*` with unit
`u, v`; by convexity of norms the completely bounded trace norm equals the
supremum of `‖(Φ ⊗ 1)(u v*)‖₁` over unit joint vectors.

Reuses `finiteDiamondNorm_eq_choi` (raw finite-reference norm = two-density Choi
supremum) and `diamond_svd_trace_decomposition` (SVD of a raw input as a
positive combination of rank-one trace-norm-one pieces). -/
theorem finiteDiamondNorm_eq_rankOneSup {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondNorm T = rankOneSup T := by
  rw [finiteDiamondNorm_eq_choi]
  unfold rankOneSup diamondChoiValue
  apply le_antisymm
  · refine iSup_le fun ρ => iSup_le fun σ => ?_
    rw [diamondChoiScore_as_raw]
    exact le_iSup_of_le ⟨densityVector ρ, densityVector_normalized ρ⟩
      (le_iSup_of_le ⟨densityVector σ, densityVector_normalized σ⟩ le_rfl)
  · refine iSup_le fun u => iSup_le fun v => ?_
    obtain ⟨ρ, σ, hρσ⟩ := raw_rankOne_as_diamondChoiScore T u.1 v.1 u.2 v.2
    rw [rankOneValue, hρσ]
    exact le_iSup_of_le ρ (le_iSup_of_le σ le_rfl)

/-- Fixed arXiv:1207.5726v2 §1 Eq. (2), p.3, maximum form: for positive input
dimension the supremum is attained at an actual pair of unit joint vectors.
Derived from `diamondChoi_attained` together with the raw rank-one reformulation
`diamondChoiScore_as_raw`. -/
theorem rankOne_max_attained {D E : ℕ} (hD : 0 < D)
    (T : Operator D →ₗ[ℂ] Operator E) :
    ∃ u v : Fin D × Fin D → ℂ,
      (∑ a, star (u a) * u a = 1) ∧ (∑ a, star (v a) * v a = 1) ∧
      finiteDiamondNorm T = rankOneValue T u v := by
  obtain ⟨ρ, σ, hnorm, -⟩ := diamondChoi_attained hD T
  refine ⟨densityVector ρ, densityVector σ, densityVector_normalized ρ,
    densityVector_normalized σ, ?_⟩
  rw [rankOneValue, ← diamondChoiScore_as_raw]
  exact hnorm

/-- The finite-reference completely bounded spectral norm `|||S|||∞`, the
analogue of `finiteDiamondNorm` with the Euclidean operator (spectral) norm in
place of the trace norm:
`⨆_{r} ⨆_{‖X‖∞ ≤ 1} ‖(S ⊗ 1_{ℂ^r})(X)‖∞`. Fixed arXiv:1207.5726v2 §1, p.3. -/
def finiteDiamondSpectralNorm {M N : ℕ} (S : Operator M →ₗ[ℂ] Operator N) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ X : Matrix (Fin M × Fin r) (Fin M × Fin r) ℂ,
    if ‖X‖ ≤ 1 then ENNReal.ofReal ‖tensorLeft S X‖ else 0


end Qatlib.Papers.BddNormSDP12.MainResults
