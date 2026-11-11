/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — sparsity, `‖H‖_max`, `τ`, and the simulation cost model

This file fixes the notation used by the paper-layer statements for
Berry–Childs–Kothari, *Hamiltonian simulation with nearly optimal dependence
on all parameters*, arXiv:1501.01715v3 (2015-12-07).

Everything here is a *definition*: the algorithmic statements of Theorems 1–3 and
Lemmas 9–12 are phrased over these objects, and the exact evolution operator is the
repository's `HamiltonianEvolution H t = e^{-iHt}` (Foundations v0.2.0 §2.2).

The paper quantifies query and gate complexity of a simulation routine: a routine is
accepted when its output unitary is within spectral-norm distance `ε` of `e^{-iHt}`
(the paper's error criterion, Section 3.3), and its `queryCost`/`gateCost` count,
respectively, calls to the sparse-Hamiltonian oracle and additional two-qubit gates.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.HamSimOptimal15.MainResults

/-- `d`-sparsity of a Hamiltonian `H` on `N` basis states (paper p.2, the standard
definition: every row and every column has at most `d` nonzero entries). -/
def IsDSparse {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) : Prop :=
  (∀ i : Fin N, (Finset.univ.filter (fun j : Fin N => H i j ≠ 0)).card ≤ d) ∧
  (∀ j : Fin N, (Finset.univ.filter (fun i : Fin N => H i j ≠ 0)).card ≤ d)

/-- `‖H‖_max`: the largest entry of `H` in absolute value (paper p.2, immediately
above Theorem 1).  For the empty matrix the supremum of the empty set is `0`. -/
noncomputable def maxEntryNorm {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sSup (Set.range (fun p : Fin N × Fin N => ‖H p.1 p.2‖))

/-- `τ := d‖H‖_max t`, the scale parameter of Theorem 1 (paper p.2, eq.(3)). -/
noncomputable def tau {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) (t : ℝ) : ℝ :=
  (d : ℝ) * maxEntryNorm H * t

/-- The iterated logarithm `log log x` that governs the near-optimal rate
(paper p.2, eq.(3)). -/
noncomputable def loglog (x : ℝ) : ℝ := Real.log (Real.log x)

/-- The rate `log y / log log y` appearing in Theorem 1 (paper p.2, eq.(3)). -/
noncomputable def logOverLoglog (y : ℝ) : ℝ := Real.log y / loglog y

/-- A candidate Hamiltonian-simulation routine on `N` basis states, recorded by its
output unitary and its two resource counters (paper §1: queries to the sparse
Hamiltonian oracle, and additional two-qubit gates). -/
structure SimProcedure (N : ℕ) where
  /-- The unitary produced by the routine. -/
  output : Matrix (Fin N) (Fin N) ℂ
  /-- Number of oracle queries used. -/
  queryCost : ℕ
  /-- Number of additional two-qubit gates used. -/
  gateCost : ℕ

/-- `p` simulates `H` for time `t` within spectral-norm error `ε`
(paper Section 3.3: the error is measured as `‖U − e^{-iHt}‖` in the spectral norm). -/
def Simulates {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (t ε : ℝ)
    (p : SimProcedure N) : Prop :=
  ‖p.output - HamiltonianEvolution H t‖ ≤ ε

/-- `f` is an upper bound on the query complexity of d-sparse Hamiltonian simulation
in the sense of Theorem 1: a single constant `C` works for every Hamiltonian, time
and error, and yields a routine whose query count is at most `C · f τ ε` while
achieving error `ε`. -/
def QueryComplexityAtMost (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : ℕ)
      (t ε : ℝ), 0 < ε → 0 < t → IsDSparse H d →
    ∃ p : SimProcedure (2 ^ n), Simulates H t ε p ∧ (p.queryCost : ℝ) ≤ C * f (tau H d t) ε

/-- `f` is an upper bound on the gate complexity of d-sparse Hamiltonian simulation
in the sense of Theorem 1, eq.(4). -/
def GateComplexityAtMost (f : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : ℕ)
      (t ε : ℝ), 0 < ε → 0 < t → IsDSparse H d →
    ∃ p : SimProcedure (2 ^ n), Simulates H t ε p ∧
      (p.gateCost : ℝ) ≤ C * f n (tau H d t) ε

/-- The lower-bound shape of Theorem 2 (paper p.3, eq.(5)): there is a constant `C`
such that for every error, time, sparsity and every fixed value of `‖H‖_max` some
`d`-sparse Hamiltonian forces every `ε`-accurate routine to spend at least
`C · (τ + log(1/ε)/log log(1/ε))` queries. -/
def QueryComplexityLowerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ε t : ℝ), 0 < ε → 0 < t → ∀ (d : ℕ), 2 ≤ d → ∀ (X : ℝ), 0 < X →
    ∃ (n : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ), IsDSparse H d ∧
      maxEntryNorm H = X ∧
      ∀ p : SimProcedure (2 ^ n), Simulates H t ε p →
        C * (tau H d t + Real.log (1 / ε) / loglog (1 / ε)) ≤ (p.queryCost : ℝ)


/-- **Theorem 1, query complexity (statement), arXiv:1501.01715v3 p.2 eq.(3)**:
a `d`-sparse Hamiltonian on `n` qubits can be simulated for time `t` within error
`ε` using `O(τ log(τ/ε)/log log(τ/ε))` queries, `τ = d‖H‖_max t`.

Registered as a proposition, not proved: the algorithm combines the Szegedy quantum
walk of [6,12] with the fractional-query / LCU decomposition, and the repository has
no end-to-end sparse simulation routine to instantiate `SimProcedure`.  The statement
is the exact asymptotic form of eq.(3) with an explicit constant, taken over all
Hamiltonians, times and errors.  The proof combines Lemma 9 (query count per segment)
with `O(tXd)` segments at `X = ‖H‖_max`, i.e. `O(τ·k)` with `k` from eq.(46).
Candidate dependencies: `QueryComplexityAtMost`,
`QuantumAlgorithm.Concepts.LcuPostselect.ScaledLCU.scaled_lcu_run_and_cost`,
`QuantumAlgorithm.Concepts.CoherentSim.CoherentOAA.coherent_oaa_compressed_error`.
Suggested follow-up: formalise the segmented simulation of Section 3.3 and plug in
`k = ⌈2 log(‖H‖t/ε) / log log(‖H‖t/ε)⌉`. -/
def theorem1_query_complexity : Prop :=
  QueryComplexityAtMost (fun τ ε => τ * logOverLoglog (τ / ε))

/-- **Theorem 1, gate complexity (statement), arXiv:1501.01715v3 p.2 eq.(4)**:
the same simulation uses `O(τ[n + log^{5/2}(τ/ε)] log(τ/ε)/log log(τ/ε))` additional
two-qubit gates.

Registered as a proposition, not proved: it is Lemma 10 with `F(m) = O(m^{5/2})`,
and the coefficient extraction inner loop contributes `n` gates per segment.
Candidate dependencies: `GateComplexityAtMost`, `theorem1_query_complexity`.
Suggested follow-up: derive it from `lemma10_gate_complexity` with `F(m) = m^{5/2}`
and `m = log(τ/ε)`. -/
def theorem1_gate_complexity : Prop :=
  GateComplexityAtMost
    (fun n τ ε => τ * ((n : ℝ) + Real.rpow (Real.log (τ / ε)) (5 / 2 : ℝ)) *
      logOverLoglog (τ / ε))

/-- **Theorem 2 (statement), arXiv:1501.01715v3 p.3 eq.(5)**: for any `ε, t > 0`,
integer `d ≥ 2` and fixed `‖H‖_max`, there is a `d`-sparse `H` for which every
`ε`-accurate simulation needs `Ω(τ + log(1/ε)/log log(1/ε))` queries.

Registered as a proposition, not proved: the proof boosts an `Ω(t)` instance by
replacing edges with `K_{d,d}` (Lemma 12) and combines it with the error-dependent
lower bound of [7] (Mochon). Candidate dependencies:
`QueryComplexityLowerBound`, `lemma12_lower_bound`. Suggested follow-up: instantiate
the model with the parity Hamiltonian of Lemma 12 and take the max of the two lower
bounds. -/
def theorem2_lower_bound : Prop :=
  QueryComplexityLowerBound

/-- **Theorem 3 (statement), arXiv:1501.01715v3 p.3 eq.(6)**: for every `α ∈ (0,1]`
a `d`-sparse Hamiltonian can be simulated for time `t` within error `ε` using
`O(τ^{1+α/2} + τ^{1−α/2} log(1/ε))` queries.

Registered as a proposition, not proved: the tradeoff algorithm uses segments with
`z ∝ −τ^α`, `k = O(z + log(1/δ))` (eq.(53)) and the Bessel absolute-sum bound of
Lemma 11 (eq.(54)); neither the segmentation nor the `k`-to-cost conversion is
formalised.  Candidate dependencies: `lemma11_bessel_sum_isBigO`,
`lemma8_bessel_tail`.  Suggested follow-up: combine eq.(53)–(54) with
`O(τ) = O(τ^{1+α/2})` segments. -/
def theorem3_tradeoff_query_complexity (α : ℝ) : Prop :=
  0 < α → α ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : ℕ)
      (t ε : ℝ), 0 < ε → 0 < t → IsDSparse H d →
      ∃ p : SimProcedure (2 ^ n), Simulates H t ε p ∧
        (p.queryCost : ℝ) ≤
          C * (Real.rpow (tau H d t) (1 + α / 2) +
            Real.rpow (tau H d t) (1 - α / 2) * Real.log (1 / ε))

/-- **Lemma 9 (statement), arXiv:1501.01715v3 p.11 eq.(44)**: a `d`-sparse `H` on `n`
qubits can be simulated for time `t` within error `ε` with query complexity
`O(τ log(‖H‖t/ε)/log log(‖H‖t/ε))`.

Registered as a proposition, not proved.  The paper's route: one segment uses `k`
from eq.(46), each segment costs `O(k)` controlled-`U`/`U†` operations, and there are
`O(tXd)` segments with `X = ‖H‖_max`.  Candidate dependencies:
`QueryComplexityAtMost`,
`QuantumAlgorithm.Concepts.LcuPostselect.ScaledLCU.lemma5_lcu_postselect_circuit`
(one query per LCU macro), `lemma4_lcu_lemma`.  Suggested follow-up: formalise the
segmented composition and the `k` bound of eq.(46). -/
def lemma9_query_complexity : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : ℕ)
    (t ε : ℝ), 0 < ε → 0 < t → IsDSparse H d →
    ∃ p : SimProcedure (2 ^ n), Simulates H t ε p ∧
      (p.queryCost : ℝ) ≤
        C * (tau H d t * (Real.log (‖H‖ * t / ε) / loglog (‖H‖ * t / ε)))

/-- **Lemma 10 (statement), arXiv:1501.01715v3 p.11 eq.(47)**: the gate complexity of
the same simulation is `O(τ[n + F(log(‖H‖t/ε))] log(‖H‖t/ε)/log log(‖H‖t/ε))`
two-qubit gates, where `F(m)` is the cost of performing elementary functions with `m`
bits.

Registered as a proposition, not proved: it is Lemma 9 times `O(n + F(log(‖H‖t/ε)))`,
the per-query cost of the coefficient-extraction step (eq.(48) onward).  Candidate
dependencies: `GateComplexityAtMost`, `lemma9_query_complexity`.  Suggested
follow-up: multiply the query count by the per-query gate cost and absorb
constants. -/
def lemma10_gate_complexity (F : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : ℕ)
    (t ε : ℝ), 0 < ε → 0 < t → IsDSparse H d →
    ∃ p : SimProcedure (2 ^ n), Simulates H t ε p ∧
      (p.gateCost : ℝ) ≤
        C * (tau H d t *
          ((n : ℝ) + F (Real.log (‖H‖ * t / ε))) *
          (Real.log (‖H‖ * t / ε) / loglog (‖H‖ * t / ε)))

/-- **Lemma 12 (statement), arXiv:1501.01715v3 p.14**: for every positive integer `d`
and every `t > 0` there is a `2d`-sparse Hamiltonian `H` with bounded largest entry
(`‖H‖_max ≤ 2`, i.e. `Θ(1)`) such that simulating `H` for time `t` at any constant
precision `ε₀` requires `Ω(td)` queries.

Registered as a proposition, not proved.  The paper's construction uses the path
Hamiltonian `H₁` of eq.(56) simulating `|0⟩ ↦ |N⟩` in time `π/2`, and the two-path
Hamiltonian `H₂` of eq.(57) that computes the parity of `x`, together with the
`N/2`-query parity lower bound of [4,18].  The repository has no parity-query lower
bound.  Candidate dependencies: none in Dev/Frozen.  Suggested follow-up: import the
adversary-method lower bound for parity and instantiate the graph models of
eq.(56)–(57). -/
def lemma12_lower_bound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (t : ℝ), 0 < t → ∀ (ε₀ : ℝ), 0 < ε₀ →
    ∃ (n : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (X : ℝ),
      0 < X ∧ X ≤ 2 ∧ IsDSparse H (2 * d) ∧ maxEntryNorm H = X ∧
      ∀ p : SimProcedure (2 ^ n), Simulates H t ε₀ p → c * (t * d) ≤ (p.queryCost : ℝ)

end Qatlib.Papers.HamSimOptimal15.MainResults
