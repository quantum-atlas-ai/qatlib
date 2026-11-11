/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.CountedHamiltonian
import Qatlib.Concepts.QspSimulation.Achievability.SimQspRefined

set_option backward.isDefEq.respectTransparency false

/-!
# The end-to-end single simulation output, with explicit counts

Source: G. H. Low and I. L. Chuang, *Optimal Hamiltonian Simulation by Quantum
Signal Processing*, arXiv:1606.02685v2 (2016-12-20), Theorem 3 (p. 4).

Theorem 3 asks for one simulation program of a `d`-sparse Hamiltonian, reported
with its qubit count, its success probability, and its *basic* gate cost and
oracle-query cost.  The repository holds these facts in two complementary
forms, which this module assembles into a single Dev-level endpoint.

* The **counted controlled-oracle circuit** of the frozen
  `hamiltonianSimulation_counted_exists` is one fixed finite gate word: it is
  well formed, block encodes `e^{-iAt}` with error `8ε`, and carries exactly
  `4n+1` controlled oracle queries and `4n+6` fixed matrix gates.
* The **computed-signal word** of the frozen `computedSignalWord` is the
  analytic (non-enumerative) program: its ledger reports the host qubit count
  `hostingQubits (card H)`, the accumulated oracle failure rate
  `queries · δ`, and the truncation error `2^{-k}`; the frozen
  `computed_signal_full_segmented_program_and_cost` gives the *explicit*
  parameterized query and gate counts
  `segments · (27 · (4·cutoff + 1))` and
  `segments · (27 · (4·cutoff + 6) + 79)`.

The new content here is the assembly and the arithmetic that the paper's
resource accounting needs: the identity `gateCount = queryCount + 5` for the
counted circuit, the explicit parameterized form of the computed-signal
ledger, and the single-output error bound with the *query count substituted*
into the failure term.  Nothing is assumed about the target beyond a
Hermitian matrix and a projected unitary encoding of it.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.HamSimQSP17.EndToEnd

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.JacobiAnger

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-! ## The counted controlled-oracle circuit -/

/-- **Theorem 3, counted-circuit form.**  For a Hermitian `A` with a projected
unitary encoding on isometric frames, every real time `t` and every `ε > 0`
admit *one* well-formed fixed-gate word that `8ε`-block-encodes the evolution
`e^{-iAt}`, with `4n+1` controlled oracle queries and `4n+6` fixed matrix
gates.  In particular the fixed-gate cost exceeds the query cost by exactly
`5`, the bookkeeping the paper charges to the two phase patterns. -/
theorem countedSingleOutput
    {A : Matrix I I ℂ} {U : Matrix H H ℂ} {F : Matrix H I ℂ}
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
      WellFormedAdjointCircuit cs ∧
      BlockEncoding (hamiltonianEvolution A t)
        (evaluate (controlOracle (parallelOracle (J := Bool) U)) cs)
        (hamiltonianFrame F) (hamiltonianFrame F) 8 ε ∧
      adjointQueryCount cs = 4 * n + 1 ∧
      adjointGateCount cs = 4 * n + 6 ∧
      adjointGateCount cs = adjointQueryCount cs + 5 := by
  obtain ⟨n, cs, hWF, hBE, hq, hg⟩ := hamiltonianSimulation_counted_exists hA h t hε
  exact ⟨n, cs, hWF, hBE, hq, hg, by omega⟩

/-! ## The computed-signal ledger with explicit counts -/

/-- **The single-output ledger carries the explicit parameterized counts.**
The host qubit count, the oracle-query count and the fixed-gate count of the
computed-signal word are the values of the analytic parameters `segments` and
`cutoff`, so the resource ledger is a function of the input data and not an
opaque constant. -/
theorem computedSignal_ledger_costs
    {A : Matrix I I ℂ} {U : Matrix H H ℂ} {F : Matrix H I ℂ} (t : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    (simQspLedger F t k 0).qubits =
      Qatlib.Concepts.QspSimulation.Achievability.hostingQubits (Fintype.card H) ∧
    (simQspLedger F t k 0).oracleQueries =
      computedSignalSegments t * (27 * (4 * computedSignalCutoff t k + 1)) ∧
    (simQspLedger F t k 0).fixedGates =
      computedSignalSegments t * (27 * (4 * computedSignalCutoff t k + 6) + 79) := by
  obtain ⟨_hWF, hq, hg, _hbound⟩ :=
    computed_signal_full_segmented_program_and_cost H I A U F t k hA h
  refine ⟨?_, ?_, ?_⟩
  · simp only [simQspLedger]
  · simpa only [simQspLedger] using hq
  · simpa only [simQspLedger] using hg

/-- **The accumulated failure rate is the query count times the oracle error.**
This unpacks the ledger's failure entry for use in the error budget below. -/
theorem simQspLedger_failure
    (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) (δ : ℝ) :
    (simQspLedger F t k δ).failureRate =
      (adjointQueryCount (computedSignalWord F t k) : ℝ) * δ := by
  simp only [simQspLedger]

/-- **The failure rate in explicit parameterized form.**  Substituting the
*explicit* query count of the computed-signal word turns the ledger's failure
rate into `segments · (27 · (4·cutoff + 1)) · δ`. -/
theorem simQspLedger_failure_explicit
    {A : Matrix I I ℂ} {U : Matrix H H ℂ} {F : Matrix H I ℂ} (t : ℚ) (k : ℕ) (δ : ℝ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    (simQspLedger F t k δ).failureRate =
      (computedSignalSegments t : ℝ) *
        (27 * (4 * (computedSignalCutoff t k : ℝ) + 1)) * δ := by
  obtain ⟨_hWF, hq, _hg, _hbound⟩ :=
    computed_signal_full_segmented_program_and_cost H I A U F t k hA h
  rw [simQspLedger_failure, hq]
  push_cast
  ring

/-! ## The single output against the evolution -/

/-- **Theorem 3, single-output error with the explicit count.**  Running the
computed-signal word against a `δ`-approximation `V` of the encoding unitary,
every input state reaches the exact evolution to within the truncation error
plus the *explicit* accumulated oracle failure
`segments · (27 · (4·cutoff + 1)) · δ`. -/
theorem computedSignal_singleOutput_bound
    {A : Matrix I I ℂ} {U V : Matrix H H ℂ} {F : Matrix H I ℂ} (t : ℚ) (k : ℕ) (δ : ℝ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) (hδ : 0 ≤ δ) (hVU : ‖V - U‖ ≤ δ)
    (ψ : QState I) :
    ‖toEuclidean_fromVec
        (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
            (controlOracle (parallelOracle (J := Bool) V))) (computedSignalWord F t k) *ᵥ
          (scaleEightFrame (hamiltonianFrame F) *ᵥ ψ) -
          scaleEightFrame (hamiltonianFrame F) *ᵥ (hamiltonianEvolution A (t : ℝ) *ᵥ ψ))‖
      ≤ ((1 / 2 : ℝ) ^ k +
          (computedSignalSegments t : ℝ) *
            (27 * (4 * (computedSignalCutoff t k : ℝ) + 1)) * δ) *
        ‖toEuclidean_fromVec ψ‖ := by
  have hbase := simQsp_single_output_error H I A U V F t k δ hA h hV hδ hVU ψ
  obtain ⟨_hq, _hf, _ho, _hfr, ht'⟩ := simQspLedger_spec (H := H) (I := I) F t k δ
  have hfr := simQspLedger_failure_explicit (A := A) (U := U) (F := F) t k δ hA h
  calc
    ‖toEuclidean_fromVec
        (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
            (controlOracle (parallelOracle (J := Bool) V))) (computedSignalWord F t k) *ᵥ
          (scaleEightFrame (hamiltonianFrame F) *ᵥ ψ) -
          scaleEightFrame (hamiltonianFrame F) *ᵥ (hamiltonianEvolution A (t : ℝ) *ᵥ ψ))‖
        ≤ ((simQspLedger F t k δ).truncationError +
            (simQspLedger F t k δ).failureRate) * ‖toEuclidean_fromVec ψ‖ := hbase
    _ = ((1 / 2 : ℝ) ^ k +
          (computedSignalSegments t : ℝ) *
            (27 * (4 * (computedSignalCutoff t k : ℝ) + 1)) * δ) *
        ‖toEuclidean_fromVec ψ‖ := by
        rw [hfr, ht']

/-! ## The assembled endpoint -/

/-- **The end-to-end endpoint of Theorem 3.**  For a Hermitian `A` with a
projected unitary encoding on isometric frames, a real time `t`, a `δ`-noisy
encoding unitary `V`, a rational read `t` and precision `k`, the repository
delivers, in one statement:

* a well-formed counted circuit `8ε`-block-encoding the evolution with
  `4n+1` queries and `4n+6` fixed gates (`countedSingleOutput`);
* the host qubit count, the explicit oracle-query and fixed-gate counts, and
  the accumulated failure rate of the computed-signal word
  (`computedSignal_ledger_costs`, `simQspLedger_failure_explicit`);
* the single-output error bound with the explicit count substituted into the
  failure term (`computedSignal_singleOutput_bound`).

This is a conjunction of independently proved facts, assembled at the same
`(A, U, F, t, k, δ)` so that the qubit, gate, query and failure bookkeeping of
Theorem 3 is available from a single reference point.  It does not assert an
asymptotic query optimum (that is the corrected selector's job), nor arbitrary
`PREPARE`/frame local-gate synthesis. -/
theorem simulationEndpoint
    {A : Matrix I I ℂ} {U V : Matrix H H ℂ} {F : Matrix H I ℂ} (t : ℚ) (k : ℕ) (δ ε : ℝ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) (hδ : 0 ≤ δ) (hVU : ‖V - U‖ ≤ δ)
    (hε : 0 < ε) :
    (∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
        WellFormedAdjointCircuit cs ∧
        BlockEncoding (hamiltonianEvolution A (t : ℝ))
          (evaluate (controlOracle (parallelOracle (J := Bool) U)) cs)
          (hamiltonianFrame F) (hamiltonianFrame F) 8 ε ∧
        adjointQueryCount cs = 4 * n + 1 ∧
        adjointGateCount cs = 4 * n + 6 ∧
        adjointGateCount cs = adjointQueryCount cs + 5) ∧
      (simQspLedger F t k 0).qubits =
      Qatlib.Concepts.QspSimulation.Achievability.hostingQubits (Fintype.card H) ∧
      (simQspLedger F t k 0).oracleQueries =
        computedSignalSegments t * (27 * (4 * computedSignalCutoff t k + 1)) ∧
      (simQspLedger F t k δ).failureRate =
        (computedSignalSegments t : ℝ) *
          (27 * (4 * (computedSignalCutoff t k : ℝ) + 1)) * δ ∧
      (∀ ψ : QState I,
        ‖toEuclidean_fromVec
            (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
                (controlOracle (parallelOracle (J := Bool) V))) (computedSignalWord F t k) *ᵥ
              (scaleEightFrame (hamiltonianFrame F) *ᵥ ψ) -
              scaleEightFrame (hamiltonianFrame F) *ᵥ (hamiltonianEvolution A (t : ℝ) *ᵥ ψ))‖
          ≤ ((1 / 2 : ℝ) ^ k +
              (computedSignalSegments t : ℝ) *
                (27 * (4 * (computedSignalCutoff t k : ℝ) + 1)) * δ) *
            ‖toEuclidean_fromVec ψ‖) := by
  refine ⟨countedSingleOutput hA h (t : ℝ) hε, ?_, ?_, ?_, ?_⟩
  · exact (computedSignal_ledger_costs (A := A) (U := U) (F := F) t k hA h).1
  · exact (computedSignal_ledger_costs (A := A) (U := U) (F := F) t k hA h).2.1
  · exact simQspLedger_failure_explicit (A := A) (U := U) (F := F) t k δ hA h
  · exact fun ψ => computedSignal_singleOutput_bound (A := A) (U := U) (V := V) (F := F)
      t k δ hA h hV hδ hVU ψ

end Qatlib.Papers.HamSimQSP17.EndToEnd
