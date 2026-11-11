/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation

/-!
# Composition of exact gate compilers

This module composes `GateCompiler`s and proves that circuit compilation respects concatenation,
repetition, and successive compilation. Exact circuit semantics and query counts are preserved,
while gate counts are tracked by compiler profiles. The circuit compilation setting is described
in [NielsenChuang2010].

The certification results propagate gate-set restrictions and unitarity through two compilation
stages, and uniform expansion bounds multiply across stages.

## Main statements

* `GateCompiler.compileCircuit_compose`: a composed compiler agrees with two successive circuit
  compilations.
* `GateCompiler.compose_certified`: combines semantics, gate-set, unitarity, and resource
  guarantees.
* `gateCount_compileCircuit_compose_le`: bounds gate expansion by the product of the two stage
  bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- The gate compiler that compiles each gate with `c₁` and then compiles the resulting circuit
with `c₂`. -/
def compose (c₁ c₂ : GateCompiler I) : GateCompiler I where
  compile U := compileCircuit c₂ (c₁.compile U)
  query_free U := (queryCount_compileCircuit c₂ _).trans (c₁.query_free U)
  semantics U W ψ := (run_compileCircuit c₂ W _ ψ).trans (c₁.semantics U W ψ)

/-- Compiling one gate with the composed compiler equals compiling its first-stage circuit with
the second compiler. -/
@[simp] theorem compose_compile (c₁ c₂ : GateCompiler I) (U : Matrix I I ℂ) :
    (compose c₁ c₂).compile U = compileCircuit c₂ (c₁.compile U) := rfl

end GateCompiler

/-- Compiling a concatenation of circuits concatenates their compiled circuits. -/
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

/-- Compiling a repeated circuit equals repeating its compilation the same number of times. -/
theorem compileCircuit_repeatCircuit (c : GateCompiler I) (C : Circuit I) (k : ℕ) :
    compileCircuit c (RepeatCircuit C k) = RepeatCircuit (compileCircuit c C) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show compileCircuit c (C ++ RepeatCircuit C k)
      = compileCircuit c C ++ RepeatCircuit (compileCircuit c C) k
    rw [compileCircuit_append, ih]

/-- Circuit compilation by a composed compiler equals successive compilation by its two
constituent compilers. -/
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

/-- Circuit compilation respects concatenation, repetition, and composition of gate compilers. -/
theorem compileCircuit_composition_laws (c₁ c₂ : GateCompiler I) (C D : Circuit I) (k : ℕ) :
    compileCircuit c₁ (C ++ D) = compileCircuit c₁ C ++ compileCircuit c₁ D ∧
    compileCircuit c₁ (RepeatCircuit C k) = RepeatCircuit (compileCircuit c₁ C) k ∧
    compileCircuit (GateCompiler.compose c₁ c₂) C = compileCircuit c₂ (compileCircuit c₁ C) :=
  ⟨compileCircuit_append c₁ C D, compileCircuit_repeatCircuit c₁ C k,
    GateCompiler.compileCircuit_compose c₁ c₂ C⟩

/-- Compiler composition is associative on compiled circuits, and the composed profile agrees
with the second-stage gate count and total size accounting. -/
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

/-- Under the stated gate-set hypotheses, two-stage compilation preserves execution and query
count, produces a unitary circuit in `G₂`, and has the gate count recorded by the composed
profile. -/
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

/-- If each gate occurring in `C` compiles to at most `b` gates, the compiled circuit has at
most `b * GateCount C` gates. -/
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

/-- If the two compilation stages expand relevant gates by at most `b₁` and `b₂`, their
composition has gate count at most `b₂ * b₁ * GateCount C`. -/
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
