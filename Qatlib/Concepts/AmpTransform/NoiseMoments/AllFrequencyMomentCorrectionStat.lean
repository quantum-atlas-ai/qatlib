/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
set_option warningAsError false
set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

def AllFrequencyMomentCorrection : Prop :=
  ∀ (N L : ℕ) [NeZero N] (c : ℂ) (b : ℝ),
    ∀ y : ZMod N,
      let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i * y)
      (y = 0 →
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖S ω‖ ^ 2) = (L : ℝ) ^ 2 ∧
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖c + (b : ℂ) * S ω‖ ^ 2) = ‖c + (b : ℂ) * (L : ℂ)‖ ^ 2) ∧
      (y ≠ 0 →
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖S ω‖ ^ 2) = (L : ℝ) ∧
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖c + (b : ℂ) * S ω‖ ^ 2) = ‖c‖ ^ 2 + b ^ 2 * (L : ℝ))

end Qatlib.Concepts.AmpTransform.NoiseMoments
