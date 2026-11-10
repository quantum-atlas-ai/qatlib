/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

namespace GateCompiler

def compose (c₁ c₂ : GateCompiler I) : GateCompiler I where
  compile U := compileCircuit c₂ (c₁.compile U)
  query_free U := (queryCount_compileCircuit c₂ _).trans (c₁.query_free U)
  semantics U W ψ := (run_compileCircuit c₂ W _ ψ).trans (c₁.semantics U W ψ)

@[simp] theorem compose_compile (c₁ c₂ : GateCompiler I) (U : Matrix I I ℂ) :
    (compose c₁ c₂).compile U = compileCircuit c₂ (c₁.compile U) := rfl

end GateCompiler

theorem compileCircuit_append (c : GateCompiler I) (C D : Circuit I) :
    compileCircuit c (C ++ D) = compileCircuit c C ++ compileCircuit c D := by
  induction C with
  | nil => rw [List.nil_append, compileCircuit_nil, List.nil_append]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [List.cons_append, compileCircuit_gate, ih, compileCircuit_gate, List.append_assoc]
    | query =>
      show Step.query :: compileCircuit c (C ++ D)
        = compileCircuit c (Step.query :: C) ++ compileCircuit c D
      rw [ih, compileCircuit_query, ← List.cons_append]

theorem compileCircuit_repeatCircuit (c : GateCompiler I) (C : Circuit I) (k : ℕ) :
    compileCircuit c (RepeatCircuit C k) = RepeatCircuit (compileCircuit c C) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show compileCircuit c (C ++ RepeatCircuit C k)
      = compileCircuit c C ++ RepeatCircuit (compileCircuit c C) k
    rw [compileCircuit_append, ih]

theorem GateCompiler.compileCircuit_compose (c₁ c₂ : GateCompiler I) (C : Circuit I) :
    compileCircuit (compose c₁ c₂) C = compileCircuit c₂ (compileCircuit c₁ C) := by
  induction C with
  | nil => exact compileCircuit_nil c₂
  | cons s C ih =>
    cases s with
    | gate U =>
      show (compose c₁ c₂).compile U ++ compileCircuit (compose c₁ c₂) C
        = compileCircuit c₂ (c₁.compile U ++ compileCircuit c₁ C)
      rw [compose_compile, ih, compileCircuit_append]
    | query =>
      show Step.query :: compileCircuit (compose c₁ c₂) C
        = compileCircuit c₂ (Step.query :: compileCircuit c₁ C)
      rw [ih, compileCircuit_query]

theorem compileCircuit_composition_laws (c₁ c₂ : GateCompiler I) (C D : Circuit I) (k : ℕ) :
    compileCircuit c₁ (C ++ D) = compileCircuit c₁ C ++ compileCircuit c₁ D ∧
    compileCircuit c₁ (RepeatCircuit C k) = RepeatCircuit (compileCircuit c₁ C) k ∧
    compileCircuit (GateCompiler.compose c₁ c₂) C = compileCircuit c₂ (compileCircuit c₁ C) :=
  ⟨compileCircuit_append c₁ C D, compileCircuit_repeatCircuit c₁ C k,
    GateCompiler.compileCircuit_compose c₁ c₂ C⟩

theorem GateCompiler.compose_resources (c₁ c₂ c₃ : GateCompiler I) (C : Circuit I) :
    compileCircuit (compose (compose c₁ c₂) c₃) C
        = compileCircuit (compose c₁ (compose c₂ c₃)) C ∧
      (derive (compose c₁ c₂).profile C).basicGates
        = (derive c₂.profile (compileCircuit c₁ C)).basicGates ∧
      Size (compileCircuit (compose c₁ c₂) C)
        = (derive c₂.profile (compileCircuit c₁ C)).basicGates + QueryCount C := by
  refine ⟨?_, ?_, ?_⟩
  · rw [compileCircuit_compose, compileCircuit_compose, compileCircuit_compose,
      compileCircuit_compose]
  · rw [(compose c₁ c₂).profile_basicGates_eq, compileCircuit_compose, c₂.profile_basicGates_eq]
  · rw [size_eq_gateCount_add_queryCount, queryCount_compileCircuit, compileCircuit_compose,
      ← c₂.profile_basicGates_eq]

theorem GateCompiler.compose_certified (c₁ c₂ : GateCompiler I)
    (G₁ G₂ : Set (Matrix I I ℂ)) (C : Circuit I)
    (h₁ : c₁.UsesGateSetOn G₁ C)
    (h₂ : ∀ U ∈ G₁, Circuit.UsesGateSet G₂ (c₂.compile U))
    (hG₂ : ∀ U ∈ G₂, U ∈ Matrix.unitaryGroup I ℂ)
    (W : Matrix I I ℂ) (ψ : QState I) :
    Run W (compileCircuit (compose c₁ c₂) C) ψ = Run W C ψ ∧
      Circuit.UsesGateSet G₂ (compileCircuit (compose c₁ c₂) C) ∧
      IsUnitaryCircuit (compileCircuit (compose c₁ c₂) C) ∧
      QueryCount (compileCircuit (compose c₁ c₂) C) = QueryCount C ∧
      (derive (compose c₁ c₂).profile C).basicGates
        = GateCount (compileCircuit c₂ (compileCircuit c₁ C)) := by
  have hmid : c₂.UsesGateSetOn G₂ (compileCircuit c₁ C) :=
    fun U hU => h₂ U (c₁.compile_usesGateSet G₁ C h₁ U hU)
  obtain ⟨hrun, hgates, hunit, _, hq⟩ :=
    c₂.certified_semantics_cost G₂ (compileCircuit c₁ C) hmid hG₂ W ψ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [compileCircuit_compose]
    exact hrun.trans (run_compileCircuit c₁ W C ψ)
  · rw [compileCircuit_compose]
    exact hgates
  · rw [compileCircuit_compose]
    exact hunit
  · rw [compileCircuit_compose, hq, queryCount_compileCircuit]
  · rw [(compose c₁ c₂).profile_basicGates_eq, compileCircuit_compose]

theorem gateCount_compileCircuit_le (c : GateCompiler I) (C : Circuit I) (b : ℕ)
    (h : ∀ U, Step.gate U ∈ C → GateCount (c.compile U) ≤ b) :
    GateCount (compileCircuit c C) ≤ b * GateCount C := by
  revert h
  induction C with
  | nil => intro _; simp
  | cons s C ih =>
    intro h
    cases s with
    | gate U =>
      have hU : GateCount (c.compile U) ≤ b := h U List.mem_cons_self
      have hih := ih (fun V hV => h V (List.mem_cons_of_mem _ hV))
      rw [compileCircuit_gate, gateCount_append, gateCount_gate, Nat.mul_succ]
      omega
    | query =>
      have hih := ih (fun V hV => h V (List.mem_cons_of_mem _ hV))
      rw [compileCircuit_query, gateCount_query, gateCount_query]
      exact hih

theorem gateCount_compileCircuit_compose_le (c₁ c₂ : GateCompiler I) (C : Circuit I)
    (b₁ b₂ : ℕ)
    (h₁ : ∀ U, Step.gate U ∈ C → GateCount (c₁.compile U) ≤ b₁)
    (h₂ : ∀ U, Step.gate U ∈ compileCircuit c₁ C → GateCount (c₂.compile U) ≤ b₂) :
    GateCount (compileCircuit (GateCompiler.compose c₁ c₂) C) ≤ b₂ * b₁ * GateCount C := by
  rw [GateCompiler.compileCircuit_compose]
  calc GateCount (compileCircuit c₂ (compileCircuit c₁ C))
      ≤ b₂ * GateCount (compileCircuit c₁ C) := gateCount_compileCircuit_le _ _ b₂ h₂
    _ ≤ b₂ * (b₁ * GateCount C) :=
      Nat.mul_le_mul_left b₂ (gateCount_compileCircuit_le c₁ C b₁ h₁)
    _ = b₂ * b₁ * GateCount C := (Nat.mul_assoc b₂ b₁ _).symm

end Qatlib.Concepts.QueryComplexity.DegreeMethod
