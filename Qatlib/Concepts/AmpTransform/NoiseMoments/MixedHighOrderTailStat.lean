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

def MixedHighOrderTail : Prop :=
  ∀ (N L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ) (b : ℝ), y ≠ 0 →
    let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i * y)
    let μ : ℝ := ‖c‖ ^ 2 + b ^ 2 * (L : ℝ)
    let X := fun ω : Fin L → ZMod N => ‖c + (b : ℂ) * S ω‖ ^ 2 - μ
    let delta : ℝ := if 2 * y = 0 then 1 else 0
    let var : ℝ :=
      b ^ 4 * ((L : ℝ) ^ 2 - (L : ℝ) + delta * ((L : ℝ) ^ 2 - (L : ℝ))) +
      2 * b ^ 2 * (L : ℝ) * ‖c‖ ^ 2 + 2 * b ^ 2 * (L : ℝ) * (c ^ 2).re * delta
    let bound : ℝ := ((‖c‖ + |b| * (L : ℝ)) ^ 2 + |μ|) ^ 2
    (((N : ℝ) ^ L)⁻¹ * (∑ ω, (X ω) ^ 4) ≤ bound * var) ∧
    ∀ t : ℝ, 0 < t →
      ((N : ℝ) ^ L)⁻¹ * (∑ ω, if t ≤ |X ω| then (1 : ℝ) else 0) ≤ var / t ^ 2

end Qatlib.Concepts.AmpTransform.NoiseMoments
