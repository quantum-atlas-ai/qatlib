/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.ErrorExpectationMinimizedAtMinLAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

def ExpectedNoiseEnvelopeBridge : Prop :=
  (∀ M N : ℕ, 2 ≤ M → 0 < N →
    let t : ℝ := -(M : ℝ)^2 +
      Real.sqrt ((M : ℝ)*((M : ℝ)-1)*((M : ℝ)*((M : ℝ)-1)+(N : ℝ)))
    let bound : ℝ → ℝ := fun L =>
      (L+(M : ℝ)^2)/(((N : ℝ)-L-(M : ℝ))*(L+(M : ℝ)))
    (-(M : ℝ) < t ∧ t < (N : ℝ)-(M : ℝ)) ∧
    (∀ L : ℝ, -(M : ℝ) < L → L < (N : ℝ)-(M : ℝ) → bound t ≤ bound L) ∧
    0 < bound t) ∧
  (∀ N : ℕ, 1 < N → ∀ L : ℝ, 0 ≤ L → L < (N : ℝ)-1 →
    (L+1)/(((N : ℝ)-L-1)*(L+1)) = 1/((N : ℝ)-L-1) ∧
    1/((N : ℝ)-1) ≤ (L+1)/(((N : ℝ)-L-1)*(L+1))) ∧
  (∀ (N M L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ),
    y ≠ 0 → 1 ≤ M → M+L < N → ‖c‖ ≤ (M : ℝ) →
    (((N : ℝ)^L)⁻¹ * (∑ ω : Fin L → ZMod N,
      ‖c + ∑ i, ZMod.stdAddChar (ω i*y)‖^2)) / ((M : ℝ)+L)^2 *
      (Real.tan (aqAngle N (M+L)))^2 * aqGain N (M+L) ≤
      ((L : ℝ)+(M : ℝ)^2)/(((N : ℝ)-L-M)*((L : ℝ)+M)))

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
