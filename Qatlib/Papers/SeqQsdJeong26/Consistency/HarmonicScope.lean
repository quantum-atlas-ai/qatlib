/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DecisionRisk.HarmonicError.TrineGeometry

/-! Auxiliary risk comparisons from OQ #145@ac56ca3b5a8d35d29577588aeeafe08967be6c91.
These three-state/first-copy results are separately attributed research extensions.
They do not assert that Jeong et al. prove them, and do not certify Proposition 3.3
for every ensemble, instrument syntax, or posterior planner. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SeqQsdJeong26.Consistency
open Qatlib.Foundations.DecisionRisk.HarmonicError

/-- The stated finite risk construction satisfies `three_state_kraus_auxiliary` with all displayed hypotheses retained. -/
theorem three_state_kraus_auxiliary {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (M : KrausMeasurement H K) (ψ : Fin 3 → H) (q : Fin 3 → ℝ) {t : ℝ}
    (hq : ∀ i, 0 ≤ q i) (ht : 0 ≤ t) (hn : ∀ i, ‖ψ i‖ = 1)
    (ho : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ = t) :
    t^2*(pairWeight (q 0) (q 1)+pairWeight (q 0) (q 2)+pairWeight (q 1) (q 2)) ≤
      (1+t)*decisionError (fun k i => M.op k (ψ i)) q := by
  exact Qatlib.Foundations.DecisionRisk.HarmonicError.kraus_error_bound M ψ q hq ht hn ho

/-- The stated finite risk construction satisfies `trine_first_copy_auxiliary` with all displayed hypotheses retained. -/
theorem trine_first_copy_auxiliary {ι U V H K : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : ι → U →ₗ[ℂ] V) (hA : ∀ x, ∑ a, ‖A a x‖^2=‖x‖^2)
    (u v : U) (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : inner ℂ u v=0)
    (M : ι → KrausMeasurement H K) (ψ : Fin 3 → H) {t : ℝ}
    (ht : 0 ≤ t) (hn : ∀ i, ‖ψ i‖=1)
    (ho : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖=t) :
    letI : InnerProductSpace ℝ U := InnerProductSpace.complexToReal
    t^2/(4*(1+t)) ≤ ∑ a, decisionError (fun k i => (M a).op k (ψ i))
      (fun i => ‖A a (trineInput u v i)‖^2/3) := by
  exact Qatlib.Foundations.DecisionRisk.HarmonicError.complex_first_copy_lower A hA u v hu hv huv M ψ ht hn ho

end Qatlib.Papers.SeqQsdJeong26.Consistency
