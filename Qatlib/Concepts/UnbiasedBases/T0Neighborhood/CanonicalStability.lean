/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUBRobustExtension
public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalUnextendibilityRestrictedOnth

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalUnextendibilityRestrictedOnth

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

/-- The common unbiasedness residual for the canonical bases has a uniform positive lower bound
on the closed unit ball. -/
theorem canonical_uniform_gap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ψ : QState (Fin 6),
      ψ ∈ Metric.closedBall (0 : QState (Fin 6)) 1 →
      ε ≤ commonResidual Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases ψ := by
  apply commonResidual_uniform_gap Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases _
    (isCompact_closedBall (0 : QState (Fin 6)) 1)
  · exact ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  · intro ψ _
    exact canonicalUnextendibilityRestricted ψ

/-- Every triple of bases in some open neighborhood of the canonical triple has no normalized
common unbiased vector. -/
theorem canonical_open_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ ∀ C : BasisArray 3 6,
      dist C Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases < δ → ∀ ψ : QState (Fin 6),
      Normalized ψ → ¬ IsCommonUnbiased C ψ := by
  obtain ⟨δ, hδ, h⟩ := no_commonUnbiased_stable_on_compact Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases
    (Metric.closedBall (0 : QState (Fin 6)) 1)
    (isCompact_closedBall (0 : QState (Fin 6)) 1)
    (fun ψ _ => canonicalUnextendibilityRestricted ψ)
  exact ⟨δ, hδ, fun C hC ψ hψ => h C hC ψ (normalized_mem_unit_closedBall ψ hψ)⟩

/-- Four mutually unbiased bases cannot have their first three bases sufficiently close to the
canonical triple. -/
theorem canonical_no_four_nearby :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : BasisArray 4 6,
      dist (fun r : Fin 3 => B r.castSucc) Qatlib.Concepts.UnbiasedBases.ThreeBasis.bases < δ → ¬ IsFamily B := by
  obtain ⟨δ, hδ, h⟩ := canonical_open_neighborhood
  refine ⟨δ, hδ, ?_⟩
  intro B hB hb
  apply h (fun r : Fin 3 => B r.castSucc) hB (B 3 0)
    (normalized_column (hb.1 3) 0)
  intro r j
  have hne : r.castSucc ≠ (3 : Fin 4) := by
    fin_cases r <;> decide
  exact hb.2 r.castSucc 3 hne j 0

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood
