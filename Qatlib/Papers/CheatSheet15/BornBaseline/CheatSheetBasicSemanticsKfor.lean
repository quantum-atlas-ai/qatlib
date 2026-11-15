/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetBasicSemanticsStat

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.CheatSheet15.BornBaseline

/-- If the verifier rejects every zero certificate, the cheat-sheet function rejects the
all-zero input for positive block count and accepts any input whose correctly indexed
certificates all verify. -/
theorem cheatSheetBasicSemantics : CheatSheetBasicSemantics := by
  intro c M κ g φ hblank
  constructor
  · intro hc
    simp only [cheatSheetFun, decide_eq_false_iff_not]
    intro h
    have hh := h ⟨0, hc⟩
    have hb := hblank (cheatBlock (κ := κ) (fun _ => false) ⟨0, hc⟩)
    change φ (cheatBlock (κ := κ) (fun _ => false) ⟨0, hc⟩) (fun _ => false) = true at hh
    rw [hb] at hh
    cases hh
  · intro z ℓ hℓ hvalid
    subst ℓ
    simpa only [cheatSheetFun, decide_eq_true_eq] using hvalid

end Qatlib.Papers.CheatSheet15.BornBaseline
