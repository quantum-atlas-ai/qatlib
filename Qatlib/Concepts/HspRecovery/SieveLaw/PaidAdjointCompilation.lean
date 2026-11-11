/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveLaw.PaidAdjointCompilationData
import Lean.Elab.Tactic.Omega

/-!
# Semantics and costs of paid adjoint compilation

This module verifies `paidAdjointCircuit` and `paidAdjointPipeline`: oracle instructions are
replaced by a concrete body circuit or its reverse, and fixed instructions are compiled
separately. In the circuit framework of [NielsenChuang2010], reversing a unitary body implements
its conjugate transpose.

The resulting circuits have zero oracle-query count and explicit gate costs. The main
specifications also record allowed gate sets, unitarity, reverse semantics, and end-to-end
measurement behavior.

## Main statements

* `paid_adjoint_actual_backend_cost`: compiled-word semantics, exact costs, and inverse
  execution.
* `paid_adjoint_end_to_end_cost`: the corresponding specification including setup and output
  circuits.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.HspRecovery.SieveLaw

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Reversing a unitary circuit compilation of a unitary matrix implements its conjugate
transpose under `Run 1`. -/
theorem gate_compilation_actual_reverse_semantics
    {O : Matrix I I ℂ} (body : GateCompilation O)
    (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hbody : IsUnitaryCircuit body.circuit) (ψ : QState I) :
    Run 1 (ReverseCircuit body.circuit) ψ = ApplyGate Oᴴ ψ := by
  have hOO : O * Oᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hO
  have h := run_reverseCircuit_run (1 : Matrix I I ℂ)
    (Submonoid.one_mem _) (by simp) body.circuit hbody (ApplyGate Oᴴ ψ)
  rw [body.semantics, ← applyGate_mul, hOO, applyGate_one] at h
  exact h

/-- Compiling a prepended adjoint instruction appends its compiled circuit after the compiled
remaining word. -/
private theorem paid_adj_cons
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (step : AdjointStep I) (word : List (AdjointStep I)) :
    paidAdjointCircuit body compiler (step :: word) =
      paidAdjointCircuit body compiler word ++ paidAdjointStepCircuit body compiler step := by
  simp only [paidAdjointCircuit, List.reverse_cons, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Each paid adjoint instruction compiles to a circuit with zero oracle queries. -/
theorem paid_adjoint_step_query_free
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (step : AdjointStep I) :
    QueryCount (paidAdjointStepCircuit body compiler step) = 0 := by
  cases step with
  | gate U => exact compiler.query_free U
  | forward => exact body.query_free
  | backward => exact (queryCount_reverseCircuit body.circuit).trans body.query_free

/-- Every paid adjoint word compiles to a circuit with zero oracle queries. -/
theorem paid_adjoint_compiler_query_free
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (word : List (AdjointStep I)) :
    QueryCount (paidAdjointCircuit body compiler word) = 0 := by
  induction word with
  | nil => rfl
  | cons step word ih =>
    rw [paid_adj_cons, queryCount_append, ih,
      paid_adjoint_step_query_free body compiler step, Nat.zero_add]

/-- Given a unitary oracle and unitary body compilation, a compiled paid adjoint step acts by
its instruction matrix. -/
private theorem paid_adj_step_semantics
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hbody : IsUnitaryCircuit body.circuit) (step : AdjointStep I) (ψ : QState I) :
    Run 1 (paidAdjointStepCircuit body compiler step) ψ =
      ApplyGate (instructionMatrix O step) ψ := by
  cases step with
  | gate U => exact compiler.semantics U 1 ψ
  | forward => exact body.semantics 1 ψ
  | backward => exact gate_compilation_actual_reverse_semantics body hO hbody ψ

/-- Given a unitary oracle and unitary body compilation, the compiled adjoint word acts by
`evaluate O word`. -/
theorem paid_adjoint_compiler_semantics
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hbody : IsUnitaryCircuit body.circuit) (word : List (AdjointStep I))
    (ψ : QState I) :
    Run 1 (paidAdjointCircuit body compiler word) ψ = ApplyGate (evaluate O word) ψ := by
  induction word generalizing ψ with
  | nil => simp only [paidAdjointCircuit, List.reverse_nil, List.flatMap_nil,
      run_nil, evaluate, applyGate_one]
  | cons step word ih =>
    rw [paid_adj_cons, run_append, ih, paid_adj_step_semantics body compiler hO hbody]
    rw [← applyGate_mul]
    rfl

/-- The compiled word's gate count is the fixed-gate compilation cost plus the adjoint query
count times the body circuit's gate count. -/
theorem paid_adjoint_compiler_gate_count
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (word : List (AdjointStep I)) :
    GateCount (paidAdjointCircuit body compiler word) =
      paidAdjointFixedGateCost compiler word +
        adjointQueryCount word * GateCount body.circuit := by
  induction word with
  | nil => simp [paidAdjointCircuit, paidAdjointFixedGateCost, adjointQueryCount]
  | cons step word ih =>
    rw [paid_adj_cons, gateCount_append, ih]
    cases step with
    | gate U =>
      simp only [paidAdjointStepCircuit, paidAdjointFixedGateCost,
        List.filterMap_cons, List.sum_cons, adjointQueryCount]
      omega
    | forward =>
      simp only [paidAdjointStepCircuit, paidAdjointFixedGateCost,
        List.filterMap_cons, adjointQueryCount, Nat.add_mul, Nat.one_mul]
      omega
    | backward =>
      simp only [paidAdjointStepCircuit, gateCount_reverseCircuit,
        paidAdjointFixedGateCost, List.filterMap_cons, adjointQueryCount,
        Nat.add_mul, Nat.one_mul]
      omega

omit [Fintype I] [DecidableEq I] in

/-- Reversing a circuit over `G` produces a circuit over the conjugate-transpose image of `G`. -/
theorem paid_reverse_circuit_uses_dagger
    (G : Set (Matrix I I ℂ)) (C : Circuit I) (hC : Circuit.UsesGateSet G C) :
    Circuit.UsesGateSet (paidDaggerGateSet G) (ReverseCircuit C) := by
  intro U hU
  unfold ReverseCircuit at hU
  obtain ⟨step, hstep, heq⟩ := List.mem_map.mp hU
  have hmem : step ∈ C := List.mem_reverse.mp hstep
  cases step with
  | gate V =>
    have he : Vᴴ = U := by simpa only [reverseStep, Step.gate.injEq] using heq
    exact ⟨V, hC V hmem, he⟩
  | query => cases heq

/-- If the body and the fixed-instruction compilations use `G`, the paid adjoint circuit uses `G
∪ paidDaggerGateSet G`. -/
theorem paid_adjoint_compiler_uses_gate_set
    {O : Matrix I I ℂ} (body : GateCompilation O) (compiler : GateCompiler I)
    (word : List (AdjointStep I)) (G : Set (Matrix I I ℂ))
    (hbody : Circuit.UsesGateSet G body.circuit)
    (hcompiler : paidAdjointCompilerUses compiler G word) :
    Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) (paidAdjointCircuit body compiler word) := by
  revert hcompiler
  induction word with
  | nil => intro _; exact Circuit.usesGateSet_nil _
  | cons step word ih =>
    intro hcompiler
    rw [paid_adj_cons, Circuit.usesGateSet_append]
    refine ⟨ih (fun U hU => hcompiler U (List.mem_cons_of_mem step hU)), ?_⟩
    cases step with
    | gate U =>
      intro V hV
      exact Or.inl (hcompiler U List.mem_cons_self V hV)
    | forward =>
      intro U hU
      exact Or.inl (hbody U hU)
    | backward =>
      intro U hU
      exact Or.inr (paid_reverse_circuit_uses_dagger G body.circuit hbody U hU)

/-- Adding conjugate transposes to a set of unitary matrices preserves unitarity of every
allowed gate. -/
theorem paid_backend_gate_set_unitary
    (G : Set (Matrix I I ℂ))
    (hG : ∀ U, U ∈ G → U ∈ Matrix.unitaryGroup I ℂ) :
    ∀ U, U ∈ G ∪ paidDaggerGateSet G → U ∈ Matrix.unitaryGroup I ℂ := by
  intro U hU
  rcases hU with hU | hU
  · exact hG U hU
  · obtain ⟨V, hV, rfl⟩ := hU
    exact conjTranspose_mem_unitaryGroup (hG V hV)

/-- Under the unitary gate-set and compilation hypotheses, paid adjoint compilation implements
the evaluated word with zero oracle queries and the exact stated gate cost. Its reverse
implements the conjugate transpose with the same cost and undoes the compiled circuit. -/
theorem paid_adjoint_actual_backend_cost
    (I : Type) [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (body : GateCompilation O) (compiler : GateCompiler I)
    (word : List (AdjointStep I)) (G : Set (Matrix I I ℂ))
    (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hword : WellFormedAdjointCircuit word)
    (hG : ∀ U, U ∈ G → U ∈ Matrix.unitaryGroup I ℂ)
    (hbody : Circuit.UsesGateSet G body.circuit)
    (hcompiler : paidAdjointCompilerUses compiler G word) :
    let compiled := paidAdjointCircuit body compiler word
    (∀ ψ : QState I, Run 1 compiled ψ = ApplyGate (evaluate O word) ψ) ∧
    QueryCount compiled = 0 ∧
    Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) compiled ∧
    IsUnitaryCircuit compiled ∧
    GateCount compiled = paidAdjointFixedGateCost compiler word +
      adjointQueryCount word * GateCount body.circuit ∧
    (∀ ψ : QState I, Run 1 (ReverseCircuit compiled) ψ =
      ApplyGate (Matrix.conjTranspose (evaluate O word)) ψ) ∧
    QueryCount (ReverseCircuit compiled) = 0 ∧
    GateCount (ReverseCircuit compiled) = GateCount compiled ∧
    (∀ ψ : QState I, Run 1 (ReverseCircuit compiled) (Run 1 compiled ψ) = ψ) := by
  let compiled := paidAdjointCircuit body compiler word
  have hbodyUnitary := hbody.isUnitaryCircuit hG
  have hsem (ψ : QState I) : Run 1 compiled ψ = ApplyGate (evaluate O word) ψ :=
    paid_adjoint_compiler_semantics body compiler hO hbodyUnitary word ψ
  have hquery : QueryCount compiled = 0 := paid_adjoint_compiler_query_free body compiler word
  have huses : Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) compiled :=
    paid_adjoint_compiler_uses_gate_set body compiler word G hbody hcompiler
  have hunitary : IsUnitaryCircuit compiled :=
    huses.isUnitaryCircuit (paid_backend_gate_set_unitary G hG)
  let compiledBody : GateCompilation (evaluate O word) :=
    { circuit := compiled
      query_free := hquery
      semantics := fun W ψ =>
        (run_eq_of_queryCount_eq_zero W 1 compiled hquery ψ).trans (hsem ψ) }
  refine ⟨hsem, hquery, huses, hunitary,
    paid_adjoint_compiler_gate_count body compiler word, ?_, ?_, ?_, ?_⟩
  · intro ψ
    exact gate_compilation_actual_reverse_semantics compiledBody
      (hword.evaluate_unitary hO) hunitary ψ
  · exact (queryCount_reverseCircuit compiled).trans hquery
  · exact gateCount_reverseCircuit compiled
  · intro ψ
    exact run_reverseCircuit_run (1 : Matrix I I ℂ)
      (Submonoid.one_mem _) (by simp) compiled hunitary ψ

omit [Fintype I] [DecidableEq I] in

/-- Enlarging an allowed gate set preserves a circuit's gate-set membership property. -/
private theorem usesGateSet_mono
    {G G' : Set (Matrix I I ℂ)} {C : Circuit I}
    (hss : G ⊆ G') (h : Circuit.UsesGateSet G C) :
    Circuit.UsesGateSet G' C :=
  fun U hU => hss (h U hU)

/-- With unitary allowed gates and query-free setup and output circuits, the paid pipeline
implements setup, word evaluation, and output with zero oracle queries and the stated exact
gate count. It preserves the corresponding measurement probabilities, uses the gate set
enlarged by conjugate transposes, and is undone by its reverse. -/
theorem paid_adjoint_end_to_end_cost
    (I : Type) [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (body : GateCompilation O) (compiler : GateCompiler I)
    (setup : Circuit I) (word : List (AdjointStep I)) (output : Circuit I)
    (G : Set (Matrix I I ℂ))
    (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (_hword : WellFormedAdjointCircuit word)
    (hG : ∀ U, U ∈ G → U ∈ Matrix.unitaryGroup I ℂ)
    (hbody : Circuit.UsesGateSet G body.circuit)
    (hcompiler : paidAdjointCompilerUses compiler G word)
    (hsetupQ : QueryCount setup = 0) (houtputQ : QueryCount output = 0)
    (hsetup : Circuit.UsesGateSet G setup) (houtput : Circuit.UsesGateSet G output) :
    let compiled := paidAdjointPipeline body compiler setup word output
    (∀ ψ : QState I, Run 1 compiled ψ =
      Run 1 output (ApplyGate (evaluate O word) (Run 1 setup ψ))) ∧
    QueryCount compiled = 0 ∧
    Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) compiled ∧
    IsUnitaryCircuit compiled ∧
    GateCount compiled = GateCount setup + paidAdjointFixedGateCost compiler word +
      adjointQueryCount word * GateCount body.circuit + GateCount output ∧
    (∀ (ψ : QState I) (E : Finset I),
      MeasureProb (Run 1 compiled ψ) E =
        MeasureProb (Run 1 output
          (ApplyGate (evaluate O word) (Run 1 setup ψ))) E) ∧
    (∀ ψ : QState I, Run 1 (ReverseCircuit compiled) (Run 1 compiled ψ) = ψ) := by
  let mid := paidAdjointCircuit body compiler word
  let compiled := paidAdjointPipeline body compiler setup word output
  have hmidE : compiled = setup ++ mid ++ output := rfl
  have hbodyUnitary := hbody.isUnitaryCircuit hG
  have hmidSem (ψ : QState I) : Run 1 mid ψ = ApplyGate (evaluate O word) ψ :=
    paid_adjoint_compiler_semantics body compiler hO hbodyUnitary word ψ
  have hmidQ : QueryCount mid = 0 :=
    paid_adjoint_compiler_query_free body compiler word
  have hmidUses : Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) mid :=
    paid_adjoint_compiler_uses_gate_set body compiler word G hbody hcompiler
  have hmidUnitary : IsUnitaryCircuit mid :=
    hmidUses.isUnitaryCircuit (paid_backend_gate_set_unitary G hG)
  have hmidCount : GateCount mid = paidAdjointFixedGateCost compiler word +
      adjointQueryCount word * GateCount body.circuit :=
    paid_adjoint_compiler_gate_count body compiler word
  have hsetupUses : Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) setup :=
    usesGateSet_mono Set.subset_union_left hsetup
  have houtputUses : Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) output :=
    usesGateSet_mono Set.subset_union_left houtput
  have hsetupUnitary : IsUnitaryCircuit setup := hsetup.isUnitaryCircuit hG
  have houtputUnitary : IsUnitaryCircuit output := houtput.isUnitaryCircuit hG
  have hsem (ψ : QState I) : Run 1 compiled ψ =
      Run 1 output (ApplyGate (evaluate O word) (Run 1 setup ψ)) := by
    rw [hmidE, run_append, run_append, hmidSem]
  have hquery : QueryCount compiled = 0 := by
    rw [hmidE, queryCount_append, queryCount_append, hsetupQ, hmidQ, houtputQ]
  have huses : Circuit.UsesGateSet (G ∪ paidDaggerGateSet G) compiled := by
    rw [hmidE, Circuit.usesGateSet_append, Circuit.usesGateSet_append]
    exact ⟨⟨hsetupUses, hmidUses⟩, houtputUses⟩
  have hunitary : IsUnitaryCircuit compiled := by
    rw [hmidE, isUnitaryCircuit_append, isUnitaryCircuit_append]
    exact ⟨⟨hsetupUnitary, hmidUnitary⟩, houtputUnitary⟩
  have hcount : GateCount compiled = GateCount setup + paidAdjointFixedGateCost compiler word +
      adjointQueryCount word * GateCount body.circuit + GateCount output := by
    rw [hmidE, gateCount_append, gateCount_append, hmidCount]
    omega
  refine ⟨hsem, hquery, huses, hunitary, hcount, ?_, ?_⟩
  · intro ψ E
    rw [hsem]
  · intro ψ
    exact run_reverseCircuit_run (1 : Matrix I I ℂ)
      (Submonoid.one_mem _) (by simp) compiled hunitary ψ

end Qatlib.Concepts.HspRecovery.SieveLaw
