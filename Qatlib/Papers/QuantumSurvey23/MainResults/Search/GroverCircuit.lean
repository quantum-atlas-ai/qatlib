/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c002 — Grover in the circuit model: `Õ(N^{3/2})` vs `O(N)`, and the QRAM fix

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 4.1 (arXiv source lines 3686–3694).

Source conclusion: in the circuit model, Grover's algorithm needs
`Õ(N^{3/2})` gates (the `√N` iterations each cost `N` gates to evaluate the
oracle), so it is *slower* than a linear classical scan; if the data is loaded
into a QRAM the oracle costs `O(1)` per query, restoring the quadratic speedup
of `O(√N)` queries.

Formalization notes: the cost functions are
* `groverCircuitGates N = N * ceil(√N)` (circuit model, `Õ(N^{3/2})`);
* `linearScanCost N = N` (classical scan);
* `qramGroverCost N = ceil(√N)` (query count with QRAM).

`circuit_grover_slower_than_scan` is the load-bearing (and slightly surprising)
half: the circuit-model Grover cost strictly exceeds `N`.  `grover_circuit_cubic_bound`
records the `Õ(N^{3/2})` upper bound as `gates² ≤ 4N³`, and
`qram_recovers_quadratic` records the QRAM restoration `√N ≤ N` plus
`N ≤ (√N+1)²`.

`Qatlib.Concepts.SearchStopping.KnownCount`
has `preparedGrover_knownCount_query_upper` (the `√N`-query bound) and
`queryCount_groverCircuit`; the QRAM oracle-compilation backend is
`Qatlib.Concepts.TableAccess.LookupCompile`.  Those prove the circuit
constructions; here we only record the arithmetic assessment.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Search

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Circuit-model Grover cost: `√N` iterations, each with an `N`-gate oracle. -/
def groverCircuitGates (N : ℕ) : ℕ := N * sqrtCost N

/-- Classical linear scan. -/
def linearScanCost (N : ℕ) : ℕ := N

/-- Grover query count when the oracle is a QRAM lookup (`O(1)` per query). -/
def qramGroverCost (N : ℕ) : ℕ := sqrtCost N

/-- **c002a (Section 4.1).** With a gate-level oracle the circuit-model
Grover cost exceeds the classical linear scan for every `N ≥ 2`: `N < N·√N`.
This is the survey's "circuit-model Grover is slower than classical search". -/
theorem circuit_grover_slower_than_scan (N : ℕ) (hN : 2 ≤ N) :
    linearScanCost N < groverCircuitGates N := by
  unfold linearScanCost groverCircuitGates
  have h2 : 2 ≤ sqrtCost N := by
    simp only [sqrtCost]
    have hpos : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
    omega
  have hmul : N * 2 ≤ N * sqrtCost N := Nat.mul_le_mul_left N h2
  nlinarith

/-- **c002b (Section 4.1).** The circuit-model gate count is
`Õ(N^{3/2})`: for `N ≥ 1`, `(N·√N)² = N²·(√N+1)² ≤ 4N³`. -/
theorem grover_circuit_cubic_bound (N : ℕ) (hN : 1 ≤ N) :
    (groverCircuitGates N) ^ 2 ≤ 4 * N ^ 3 := by
  unfold groverCircuitGates
  have hs1 : 1 ≤ Nat.sqrt N := by
    have hpos : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
    omega
  have hs : Nat.sqrt N + 1 ≤ 2 * Nat.sqrt N := by omega
  have hs2 : (Nat.sqrt N + 1) ^ 2 ≤ (2 * Nat.sqrt N) ^ 2 :=
    pow_le_pow_left' hs 2
  have hs3 : (2 * Nat.sqrt N) ^ 2 ≤ 4 * N := by
    have hsq : (Nat.sqrt N) ^ 2 ≤ N := Nat.sqrt_le' N
    nlinarith
  have hsum : (Nat.sqrt N + 1) ^ 2 ≤ 4 * N := le_trans hs2 hs3
  calc (N * (Nat.sqrt N + 1)) ^ 2 = N ^ 2 * (Nat.sqrt N + 1) ^ 2 := by ring
    _ ≤ N ^ 2 * (4 * N) := Nat.mul_le_mul_left _ hsum
    _ = 4 * N ^ 3 := by ring

/-- **c002c (Section 4.1).** A QRAM oracle restores the quadratic speedup:
`√N ≤ N` queries, and the `N`-element search space sits below `(√N+1)²`. -/
theorem qram_recovers_quadratic (N : ℕ) (hN : 2 ≤ N) :
    qramGroverCost N ≤ linearScanCost N ∧
    N ≤ (qramGroverCost N) ^ 2 := by
  refine ⟨sqrtCost_le N hN, ?_⟩
  exact le_of_lt (sqrtCost_sq_gt N)

/-- **c002 (Section 4.1), combined assessment.** Circuit model: strictly
worse than linear scan; QRAM model: quadratic speedup. -/
theorem circuit_vs_qram (N : ℕ) (hN : 2 ≤ N) :
    linearScanCost N < groverCircuitGates N ∧
    qramGroverCost N ≤ linearScanCost N ∧
    N ≤ (qramGroverCost N) ^ 2 := by
  refine ⟨circuit_grover_slower_than_scan N hN, ?_, ?_⟩
  · exact sqrtCost_le N hN
  · exact le_of_lt (sqrtCost_sq_gt N)

end Qatlib.Papers.QuantumSurvey23.MainResults.Search
