/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
set_option warningAsError false
set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.SpectralReadout.NoiseStatistics

def NoiseSequenceSecondMoment : Prop :=
  ∀ (N L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ) (b : ℝ), y ≠ 0 →
    let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i*y)
    ((N : ℝ)^L)⁻¹ * (∑ ω, ‖S ω‖^2) = (L : ℝ) ∧
    ((N : ℝ)^L)⁻¹ * (∑ ω, ‖c+(b : ℂ)*S ω‖^2) = ‖c‖^2+b^2*(L : ℝ)
end Qatlib.Concepts.SpectralReadout.NoiseStatistics
