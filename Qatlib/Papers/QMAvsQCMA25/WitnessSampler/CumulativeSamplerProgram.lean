/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.OracleSeparator.CumulativeSamplerProgram
public import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Theorem62CumulativeSamplerSepa

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath

open Qatlib.Papers.QMAvsQCMA25.OracleSeparator

namespace Qatlib.Papers.QMAvsQCMA25.WitnessSampler

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib

/-- Hardcoding the `S` oracle eliminates all `S` queries from a two-oracle circuit. -/
private theorem hardcodeS_countS' {I : Type} (oΔ : Matrix I I ℂ) (C : TOCircuit I) :
    TOQueryCountS (hardcodeS oΔ C) = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U' => exact ih
    | queryS => exact ih
    | queryU => exact ih

/-- Hardcoding the `S` oracle preserves the number of `U` queries. -/
private theorem hardcodeS_countU' {I : Type} (oΔ : Matrix I I ℂ) (C : TOCircuit I) :
    TOQueryCountU (hardcodeS oΔ C) = TOQueryCountU C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U' => exact ih
    | queryS => exact ih
    | queryU =>
      show TOQueryCountU (hardcodeS oΔ C) + 1 = TOQueryCountU C + 1
      rw [ih]

/-- Establishes the cumulative sampler program property `CumulativeSamplerProgram`. -/
theorem cumulativeSamplerProgram : CumulativeSamplerProgram := by
  intro n q t v S U C E hC hcountS hcountU
  have hnorm : ∀ w : Fin q → Bool, Normalized (classicalWitnessEmbed n q w) := by
    intro w
    exact normalized_ket _
  refine ⟨hnorm, ?_⟩
  intro hsmall hgood
  have hth := theorem6_2CumulativeSampler (n := n) (q := q) (t := t) (v := v)
    (W := Fin q → Bool) (S := S) (U := U) (C := C)
    (ψfam := fun w => classicalWitnessEmbed n q w) (E := E)
    hC hnorm hcountS hcountU hsmall hgood
  obtain ⟨hsucc, hhist⟩ := hth
  refine ⟨hsucc, ?_⟩
  intro hist
  obtain ⟨hS0, hUeq⟩ := hhist hist
  exact ⟨hS0, hUeq, hUeq ▸ hcountU⟩

end Qatlib.Papers.QMAvsQCMA25.WitnessSampler
