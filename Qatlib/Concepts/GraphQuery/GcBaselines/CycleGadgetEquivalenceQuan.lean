/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.CycleGadgetEquivalenceStat
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.FinCases

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.GraphQuery.GcBaselines

set_option maxHeartbeats 800000

/-- Establishes the cycle gadget equivalence specified by `CycleGadgetEquivalence`. -/
theorem cycleGadgetEquivalence : CycleGadgetEquivalence := by
  intro n adj x
  have hf : cycle5ThroughStation (gadgetAdjAt adj x) = true → gcOr adj x = true := by
    intro h
    rcases of_decide_eq_true h with ⟨v1, v2, v3, v4, h⟩
    cases v1 with
    | station => simp at h
    | layer l1 a =>
      cases v2 with
      | station => simp at h
      | layer l2 b =>
        cases v3 with
        | station => simp at h
        | layer l3 c =>
          cases v4 with
          | station => simp at h
          | layer l4 d =>
            fin_cases l1 <;> fin_cases l2 <;> fin_cases l3 <;> fin_cases l4 <;>
              simp_all [gadgetAdjAt]
            · apply decide_eq_true
              exact ⟨b, c, h.2.1, ⟨a, h.1⟩, ⟨d, h.2.2⟩⟩
            · apply decide_eq_true
              exact ⟨c, b, h.2.1, ⟨d, h.2.2⟩, ⟨a, h.1⟩⟩
  have hb : gcOr adj x = true → cycle5ThroughStation (gadgetAdjAt adj x) = true := by
    intro h
    rcases of_decide_eq_true h with ⟨u, v, huv, ⟨a, hua⟩, ⟨d, hvd⟩⟩
    apply decide_eq_true
    refine ⟨.layer 0 a, .layer 1 u, .layer 2 v, .layer 3 d, ?_⟩
    simp [gadgetAdjAt, huv, hua, hvd]
  cases h1 : cycle5ThroughStation (gadgetAdjAt adj x) <;> cases h2 : gcOr adj x
  · rfl
  · have h := hb h2; rw [h1] at h; cases h
  · have h := hf h1; rw [h2] at h; cases h
  · rfl

end Qatlib.Concepts.GraphQuery.GcBaselines
