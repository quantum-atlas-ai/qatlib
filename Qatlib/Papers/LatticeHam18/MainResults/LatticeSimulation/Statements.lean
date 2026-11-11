/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeHam18.MainResults.Model.LatticeModel

set_option backward.isDefEq.respectTransparency false

/-!
# Statements of Theorems 1--3, arXiv:1801.03922v4 pp.4--5

Fixed paper version: arXiv:1801.03922v4 (Haah--Hastings--Kothari--Low).

This module only *states* the three main results of the paper; the proofs (all
reduced to documented `sorry`s, with the exact Lean gaps recorded) live in
`Theorem1.lean`, `Theorem2.lean`, `Theorem3.lean`, and the summary
corresponding to the `link:` claim is in `Summary.lean`.

* Theorem 1 (p.4): for any time-dependent geometrically local Hamiltonian on
  `n` qubits on a `D`-dimensional lattice satisfying the paper's hypotheses,
  there is a circuit using `O(T n polylog(T n / ε))` two-qubit local gates at
  depth `O(T polylog(T n / ε))` that simulates time `T` to spectral error `ε`.
  (The paper's uniformity/efficient-compilability clause is not represented in
  this algebraic model; see the note in `Theorem1.lean`.)
* Theorem 2 (p.5): there is a bounded piecewise-constant nearest-neighbour
  Hamiltonian on a line of `n` qubits such that every circuit (any gate set,
  unlimited ancillas, non-local gates) simulating time `T ≤ 4^n` to constant
  error needs `Ω̃(T n)` two-qubit gates.
* Theorem 3 (p.5): the analogous lower bound when the error is only required
  for local observables; for `1 ≤ n ≤ T ≤ 2^n` it is `Ω̃(T n)`, and for
  `T ≤ n` it strengthens to `Ω̃(T²)`.

The one-dimensional piecewise-constant Hamiltonian model used by Theorems 2--3
(and by Lemma 7) is also defined here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LatticeHam18.MainResults.LatticeSimulation

open Qatlib.Papers.LatticeHam18.MainResults.Model

/-! ## One-dimensional piecewise-constant Hamiltonians -/

/-- One nearest-neighbour Hermitian term on a line of `n` qubits: a matrix
`gate` acting on the two adjacent qubits `i`, `i+1`. -/
structure OneDTerm (n : ℕ) where
  /-- Left qubit of the edge. -/
  i : Fin n
  /-- Right qubit of the edge. -/
  j : Fin n
  /-- The edge is between adjacent qubits: `j = i + 1`. -/
  adj : j.val = i.val + 1
  /-- The Hermitian local term. -/
  gate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  /-- The term is Hermitian. -/
  herm : gate.IsHermitian

/-- Forget the adjacency proof, keeping the data consumed by `layerMatrix`. -/
def OneDTerm.toTriple {n : ℕ} (g : OneDTerm n) :
    Fin n × Fin n × Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (g.i, g.j, g.gate)

/-- A bounded piecewise-constant nearest-neighbour Hamiltonian on a line of `n`
qubits with `T` unit time slices (paper p.5, proof of Theorem 2).  On the slice
`[τ, τ+1)` the Hamiltonian is the sum of the bounded Hermitian
nearest-neighbour terms of `layers τ`. -/
def IsPiecewiseConstant1D (n T : ℕ)
    (H : ℝ → Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : Prop :=
  ∃ (layers : Fin T → List (OneDTerm n)) (K : ℝ),
    0 < K ∧
    (∀ τ : Fin T, ∀ t ∈ Set.Ico (τ : ℝ) ((τ : ℝ) + 1),
      H t = layerMatrix n ((layers τ).map OneDTerm.toTriple)) ∧
    (∀ τ : Fin T, ∀ g ∈ layers τ, ‖g.gate‖ ≤ K)

/-! ## Theorem statements -/

/-- Theorem 1 (paper p.4), as a proposition.

For every finite lattice `Site` with metric `d`, every number of qubits `n`,
every time `T ≥ 0` and error `ε > 0`, and every time-dependent geometrically
local Hamiltonian `H` satisfying the paper's hypotheses
(`h_X(t) = 0` if `diam X > 1`, `‖h_X(t)‖ ≤ 1`, `O(1)` qubits per unit ball,
entrywise piecewise-slow variation), there is a circuit on the `n` qubits plus
an arbitrary finite ancilla register whose unitary is within spectral distance
`ε` of the time-ordered evolution `U_T`, using `O(T n polylog(T n / ε))`
two-qubit gates at depth `O(T polylog(T n / ε))`.

The existential constants `C₀, k` and `D₀, k₂` stand for the paper's
`O(· polylog(·))` bounds; they are allowed to depend on the lattice dimension
and the ball size (the paper's `D` and `𝔠`). -/
def Theorem1Statement : Prop :=
  ∀ (Site : Type) [Fintype Site] [DecidableEq Site]
    (d : SiteMetric (Site := Site)) (n : ℕ) (T ε : ℝ),
    0 ≤ T → 0 < ε → ∀ H : TimeDependentLocalHam Site (Fin n → Bool) d T,
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (C : GateCircuit (WithAncilla n A)),
      ApproximatesWithAncillas
          (Model.evolution (fun t => Model.totalHam d T H t) T) ε C ∧
        (∃ (C₀ : ℝ) (k : ℕ), 0 < C₀ ∧
          (C.gates : ℝ) ≤ C₀ * T * (n : ℝ) *
            (max 1 (Real.log (T * (n : ℝ) / ε))) ^ k) ∧
        (∃ (D₀ : ℝ) (k₂ : ℕ), 0 < D₀ ∧
          (C.depth : ℝ) ≤ D₀ * T *
            (max 1 (Real.log (T * (n : ℝ) / ε))) ^ k₂)

/-- Theorem 2 (paper p.5), as a proposition.

For `0 < n` and `0 < T ≤ 4^n` there is a bounded piecewise-constant
nearest-neighbour (1D) Hamiltonian `H` on `n` qubits such that every circuit
that simulates the evolution `U_T` to constant error `ε ≤ 1/10` — with any gate
set, unlimited ancillas and non-local two-qubit gates — must use at least
`c · T n / polylog(T n)` two-qubit gates for a constant `c > 0` depending only
on the fixed construction. -/
def Theorem2Statement : Prop :=
  ∀ (n T : ℕ), 0 < n → 0 < T → T ≤ 4 ^ n →
    ∃ (H : ℝ → Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
      IsPiecewiseConstant1D n T H ∧
        ∃ (c : ℝ) (k : ℕ), 0 < c ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A]
            (C : GateCircuit (WithAncilla n A)) (ε : ℝ),
            ε ≤ 1 / 10 →
            ApproximatesWithAncillas (Model.evolution H (T : ℝ)) ε C →
            c * (T : ℝ) * (n : ℝ) /
                (max 1 (Real.log ((T : ℝ) * (n : ℝ) + 2))) ^ k ≤ (C.gates : ℝ)

/-- Theorem 3 (paper p.5), as a proposition.

For `1 ≤ n ≤ T ≤ 2^n` there is a bounded piecewise-constant nearest-neighbour
Hamiltonian `H` on `n` qubits such that every circuit reproducing all
computational-basis measurements of all output qubits of `U_T` to error
`ε ≤ 1/10` needs `Ω̃(T n)` two-qubit gates; if moreover `T ≤ n`, every such
circuit needs `Ω̃(T²)` gates.  Ancillas and non-local gates are allowed, and the
gate set is arbitrary. -/
def Theorem3Statement : Prop :=
  ∀ (n T : ℕ), 1 ≤ n → n ≤ T → T ≤ 2 ^ n →
    ∃ (H : ℝ → Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
      IsPiecewiseConstant1D n T H ∧
        (∃ (c : ℝ) (k : ℕ), 0 < c ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A)
            (C : GateCircuit (WithAncilla n A)) (ε : ℝ),
            ε ≤ 1 / 10 →
            ApproximatesLocalFirstQubit (Model.evolution H (T : ℝ)) ε a₀ C →
            c * (T : ℝ) * (n : ℝ) /
                (max 1 (Real.log ((T : ℝ) * (n : ℝ) + 2))) ^ k ≤ (C.gates : ℝ)) ∧
        (T ≤ n → ∃ (c₂ : ℝ) (k₂ : ℕ), 0 < c₂ ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A)
            (C : GateCircuit (WithAncilla n A)) (ε : ℝ),
            ε ≤ 1 / 10 →
            ApproximatesLocalFirstQubit (Model.evolution H (T : ℝ)) ε a₀ C →
            c₂ * (T : ℝ) ^ 2 /
                (max 1 (Real.log ((T : ℝ) ^ 2 + 2))) ^ k₂ ≤ (C.gates : ℝ))

/-- The `link:` claim c014: the conjunction of the paper's simulation upper
bound (Theorem 1, specialised to the paper's setting) and the one-dimensional
gate-count lower bound with local-observable error (Theorem 3).  No claim about
lattices of dimension `≥ 2` is made. -/
def Theorems1And3Statement : Prop :=
  Theorem1Statement ∧ Theorem3Statement

end Qatlib.Papers.LatticeHam18.MainResults.LatticeSimulation
