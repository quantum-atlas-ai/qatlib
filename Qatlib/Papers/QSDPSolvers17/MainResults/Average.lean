/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPSolvers17.MainResults.Model.SdpInstance

@[expose] public section


/-! # Hermiticity of the arithmetic average of a projection family. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QSDPSolvers17.MainResults.FastOr
open Qatlib.Foundations.PureStateMath
variable {m D : ℕ}

/-- The average `Λ = (1/m) ∑_i Λ_i` of the projections, equation (B.1). -/
noncomputable def avgOp (Λ : Fin m → Operator D) : Operator D :=
  ((m : ℝ)⁻¹) • ∑ i, Λ i

/-- The average of Hermitian matrices is Hermitian. -/
theorem avgOp_isHermitian {Λ : Fin m → Operator D} (hΛ : ∀ i, (Λ i).IsHermitian) :
    (avgOp Λ).IsHermitian := by
  unfold avgOp
  have hsum : (∑ i, Λ i).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    exact isSelfAdjoint_sum Finset.univ (fun i _ => (hΛ i).isSelfAdjoint)
  exact hsum.smul (k := (m : ℝ)⁻¹) (by simp [IsSelfAdjoint])

end Qatlib.Papers.QSDPSolvers17.MainResults.FastOr
