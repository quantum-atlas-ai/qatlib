/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QuerySpaceKnownPhase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib Matrix
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
noncomputable section
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def compiledStep (c : Bool) : Step (Data I W) → Circuit (Full I W)
  | .gate U => [.gate (TensorGate U (1 : Matrix I I ℂ))]
  | .query => knownOneBitCircuit c

def compileCircuit (c : Bool) (C : Circuit (Data I W)) : Circuit (Full I W) :=
    C.flatMap (compiledStep c)

theorem run_compileCircuit (c : Bool) (f : I → Bool) (r : I) (hfr : f r = c)
    (C : Circuit (Data I W)) (ψ : QState (Data I W)) :
    Run (bareOracle f) (compileCircuit c C) (referenceInput r ψ) =
      referenceInput r (Run (workspaceBitOracle f) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    change Run (bareOracle f) (compiledStep c s ++ compileCircuit c C) (referenceInput r ψ) = _
    rw [run_append]
    cases s with
    | gate U =>
      simp only [compiledStep, run_gate, run_nil, lifted_gate_reference]
      exact ih _
    | query =>
      rw [compiledStep, run_knownOneBitCircuit f r c hfr]
      exact ih _

theorem compile_queries (c : Bool) (C : Circuit (Data I W)) :
    QueryCount (compileCircuit c C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [compileCircuit, List.flatMap_cons, compiledStep,
      queryCount_append, queryCount_gate, queryCount_query, queryCount_nil,
      knownOneBitCircuit_queries] at * <;> omega

theorem compile_gates (c : Bool) (C : Circuit (Data I W)) :
    GateCount (compileCircuit c C) = GateCount C + 5 * QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [compileCircuit, List.flatMap_cons, compiledStep,
      gateCount_append, gateCount_gate, gateCount_query, gateCount_nil,
      queryCount_gate, queryCount_query, knownOneBitCircuit] at * <;> omega

theorem compile_unitary (c : Bool) (C : Circuit (Data I W)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (compileCircuit c C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    change IsUnitaryCircuit (compiledStep c s ++ compileCircuit c C)
    rw [isUnitaryCircuit_append]
    cases s with
    | gate U =>
      obtain ⟨hU, htail⟩ := (isUnitaryCircuit_gate U C).mp hC
      refine ⟨?_, ih htail⟩
      simpa only [compiledStep, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
        using tensorGate_unitary hU (Submonoid.one_mem (unitaryGroup I ℂ))
    | query => exact ⟨knownOneBitCircuit_unitary c, ih ((isUnitaryCircuit_query C).mp hC)⟩

theorem compile_readout (c : Bool) (f : I → Bool) (r : I) (hfr : f r = c)
    (C : Circuit (Data I W)) (ψ : QState (Data I W)) (S : Finset (Data I W)) :
    MeasureProb (Run (bareOracle f) (compileCircuit c C) (referenceInput r ψ))
      (S ×ˢ Finset.univ) = MeasureProb (Run (workspaceBitOracle f) C ψ) S := by
  rw [run_compileCircuit c f r hfr]
  exact measureProb_tensorState_left (normalized_ket r) _ S

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
