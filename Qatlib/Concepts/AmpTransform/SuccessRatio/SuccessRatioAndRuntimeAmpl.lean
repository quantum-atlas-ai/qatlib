/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.SuccessRatio.SuccessRatioAndRuntimeStat
import Qatlib.Concepts.AmpTransform.SuccessRatio.AmplifiedPeriodRecovery
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.AmpTransform.SuccessRatio

def SuccessRatioAndRuntimeOriginal : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (s M P : ℕ) (f : Fin N → Bool),
    2 ≤ M → 0 < P → s + (M - 1) * P < N → 2 * M ≤ N → AQMarkPromise f s M P →
    let S_ALG : Finset (Fin N) := Finset.univ.filter (fun y => y.val ≠ 0)
    MeasureProb (aqState N hN M (aqProgressionSet N s M P)) S_ALG =
      aqRatio N M * MeasureProb (aqPhaseBaseline N hN (aqProgressionSet N s M P)) S_ALG ∧
    (N : ℝ) ^ 2 / (4 * (M : ℝ) * ((N - M : ℕ) : ℝ)) * (1 - 2 * (M : ℝ) / (N : ℝ)) ^ 2 ≤
      aqRatio N M ∧
    aqRatio N M ≤ (N : ℝ) ^ 2 / (4 * (M : ℝ) * ((N - M : ℕ) : ℝ))

theorem successRatioAndRuntime_original_answer : SuccessRatioAndRuntimeOriginal := by
  intro N hN s M P f hM hP hbound hhalf hmark
  (try dsimp only)
  have he := amplified_progression_success_event_probability_ratios N hN s M P f
    (Finset.univ.filter (fun y => y.val ≠ 0)) hM hP hbound hhalf hmark (by simp)
  have hg := amplified_progression_zero_mode_and_corrected_floor_bounds N hN s M P
    hM hP hbound hhalf
  have hp : 0 ≤ (N : ℝ)^2 / (4 * (M : ℝ) * ((N-M : ℕ) : ℝ)) := by positivity
  have hr : aqRatio N M =
      ((N : ℝ)^2 / (4 * (M : ℝ) * ((N-M : ℕ) : ℝ))) * aqGain N M := by
    unfold aqRatio
    ring
  refine ⟨he.1, ?_, ?_⟩
  · rw [hr]
    exact mul_le_mul_of_nonneg_left hg.2.2.1 hp
  · rw [hr]
    simpa using! mul_le_mul_of_nonneg_left hg.2.2.2.1 hp

theorem successRatio_actual_paid_budget (N : ℕ) (hN : 0 < N)
    (s M P B R : ℕ) (f : Fin N → Bool)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N)
    (hhalf : 2 * M ≤ N) (hMP : M * P ≤ N) (hPB : P ≤ B)
    (hsep : 2 * B ^ 2 < N) (hf : AQMarkPromise f s M P) :
    (∑ ω : Fin R → Fin N, aqFreshMass N hN M s P ω *
      ((aqRetry f s M B (aqRounds N M) (List.ofFn ω)).2 : ℝ)) ≤
        ((aqRounds N M + 3 : ℕ) : ℝ) / aqSuccessLower N M P :=
  (amplified_progression_actual_fresh_retry N hN s M P B R f hM hP hb
    hhalf hMP hPB hsep hf).2.2.2

theorem successRatioAndRuntime_answer : SuccessRatioAndRuntime :=
  ⟨successRatioAndRuntime_original_answer, successRatio_actual_paid_budget⟩

end Qatlib.Concepts.AmpTransform.SuccessRatio
