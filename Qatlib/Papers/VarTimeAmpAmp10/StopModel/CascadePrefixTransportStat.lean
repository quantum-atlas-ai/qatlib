/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.LiveVtProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

def CascadePrefixTransport : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C),
    GrowingVtLegal stages history →
    ∀ (j₀ : VtSpace C), j₀.1 = vtRunningFlag →
    GrowingVtSupported stages history j₀ →
    ∀ (schedule : ℕ → ℕ),
      (∀ i, i ≤ stages.length →
        DataVtWordLegal stages (cascadeWord schedule i) ∧
        Normalized (dataVtWordState stages history j₀ (cascadeWord schedule i)) ∧
        ∃ (a : ℂ) (b : QState (VtSpace C)),
          dataVtWordState stages history j₀ (cascadeWord schedule i) =
            a • Collapse (vtState stages i (Ket j₀)) (liveSet C) + b ∧
          (∀ p, b p ≠ 0 → p.1 = vtBadFlag ∧ p.2 ∈ history i) ∧
          Collapse b (liveSet C) = 0) ∧
      (∀ i, i < stages.length →
        dataVtWordTime (cascadeWord schedule (i + 1)) =
          (2 * schedule i + 1) * (dataVtWordTime (cascadeWord schedule i) + 2 ^ i)) ∧
      (∃ a : ℂ,
        Collapse (dataVtWordState stages history j₀ (cascadeWord schedule stages.length))
          (goodSet C) =
            a • Collapse (vtState stages stages.length (Ket j₀)) (goodSet C))

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
