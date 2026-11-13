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

**Statement only — not proved in Qatlib.** This checkout contains propositions
for the main simulation bounds, not proofs of Theorems 1--3. Each specification
is relative to an explicit elementary gate library and a predicate describing
valid parallel layers. These must supply the intended two-qubit locality and
scheduling restrictions. `GateCircuit.Realized` ties matrix, gate count and depth
to one common list of layers. The legacy matrix record alone is insufficient.
The formulas below retain the original pointwise constants and Hamiltonian
hypotheses; uniform asymptotic bounds and a full paper equivalence are not proved.

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
      H t = ((layers τ).map (fun g => localEmbedding n g.i g.j g.gate)).sum) ∧
    (∀ τ : Fin T, ∀ g ∈ layers τ, ‖g.gate‖ ≤ K)

/-! ## Theorem statements -/

/-- **Statement only — not proved in Qatlib.** Resource specification relative to
explicit elementary gates and admissible parallel layers. This is not a proof of
the corresponding paper theorem or its uniform asymptotic constants. -/
def Theorem1Statement
    (elementary : ∀ (W : Type) [Fintype W] [DecidableEq W], Matrix W W ℂ → Prop)
    (parallel : ∀ (W : Type) [Fintype W] [DecidableEq W], List (Matrix W W ℂ) → Prop) : Prop :=
  ∀ (Site : Type) [Fintype Site] [DecidableEq Site]
    (d : SiteMetric (Site := Site)) (n : ℕ) (T ε : ℝ),
    0 ≤ T → 0 < ε → ∀ H : TimeDependentLocalHam Site (Fin n → Bool) d T,
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (C : GateCircuit (WithAncilla n A)),
      C.Realized (elementary _) (parallel _) ∧
      ApproximatesWithAncillas
          (Model.evolution (fun t => Model.totalHam d T H t) T) ε C ∧
        (∃ (C₀ : ℝ) (k : ℕ), 0 < C₀ ∧
          (C.gates : ℝ) ≤ C₀ * T * (n : ℝ) *
            (max 1 (Real.log (T * (n : ℝ) / ε))) ^ k) ∧
        (∃ (D₀ : ℝ) (k₂ : ℕ), 0 < D₀ ∧
          (C.depth : ℝ) ≤ D₀ * T *
            (max 1 (Real.log (T * (n : ℝ) / ε))) ^ k₂)

/-- **Statement only — not proved in Qatlib.** Resource specification relative to
explicit elementary gates and admissible parallel layers. This is not a proof of
the corresponding paper theorem or its uniform asymptotic constants. -/
def Theorem2Statement
    (elementary : ∀ (W : Type) [Fintype W] [DecidableEq W], Matrix W W ℂ → Prop)
    (parallel : ∀ (W : Type) [Fintype W] [DecidableEq W], List (Matrix W W ℂ) → Prop) : Prop :=
  ∀ (n T : ℕ), 0 < n → 0 < T → T ≤ 4 ^ n →
    ∃ (H : ℝ → Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
      IsPiecewiseConstant1D n T H ∧
        ∃ (c : ℝ) (k : ℕ), 0 < c ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A]
            (C : GateCircuit (WithAncilla n A)) (ε : ℝ),
            C.Realized (elementary _) (parallel _) →
            ε ≤ 1 / 10 →
            ApproximatesWithAncillas (Model.evolution H (T : ℝ)) ε C →
            c * (T : ℝ) * (n : ℝ) /
                (max 1 (Real.log ((T : ℝ) * (n : ℝ) + 2))) ^ k ≤ (C.gates : ℝ)

/-- **Statement only — not proved in Qatlib.** Resource specification relative to
explicit elementary gates and admissible parallel layers. This is not a proof of
the corresponding paper theorem or its uniform asymptotic constants. -/
def Theorem3Statement
    (elementary : ∀ (W : Type) [Fintype W] [DecidableEq W], Matrix W W ℂ → Prop)
    (parallel : ∀ (W : Type) [Fintype W] [DecidableEq W], List (Matrix W W ℂ) → Prop) : Prop :=
  ∀ (n T : ℕ), 1 ≤ n → n ≤ T → T ≤ 2 ^ n →
    ∃ (H : ℝ → Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
      IsPiecewiseConstant1D n T H ∧
        (∃ (c : ℝ) (k : ℕ), 0 < c ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A)
            (C : GateCircuit (WithAncilla n A)) (ε : ℝ),
            C.Realized (elementary _) (parallel _) →
            ε ≤ 1 / 10 →
            ApproximatesLocalFirstQubit (Model.evolution H (T : ℝ)) ε a₀ C →
            c * (T : ℝ) * (n : ℝ) /
                (max 1 (Real.log ((T : ℝ) * (n : ℝ) + 2))) ^ k ≤ (C.gates : ℝ)) ∧
        (T ≤ n → ∃ (c₂ : ℝ) (k₂ : ℕ), 0 < c₂ ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A)
            (C : GateCircuit (WithAncilla n A)) (ε : ℝ),
            C.Realized (elementary _) (parallel _) →
            ε ≤ 1 / 10 →
            ApproximatesLocalFirstQubit (Model.evolution H (T : ℝ)) ε a₀ C →
            c₂ * (T : ℝ) ^ 2 /
                (max 1 (Real.log ((T : ℝ) ^ 2 + 2))) ^ k₂ ≤ (C.gates : ℝ))

/-- **Statement only — not proved in Qatlib.** The `link:` claim c014: the conjunction of the paper's simulation upper
bound (Theorem 1, specialised to the paper's setting) and the one-dimensional
gate-count lower bound with local-observable error (Theorem 3).  No claim about
lattices of dimension `≥ 2` is made. -/
def Theorems1And3Statement
    (elementary : ∀ (W : Type) [Fintype W] [DecidableEq W], Matrix W W ℂ → Prop)
    (parallel : ∀ (W : Type) [Fintype W] [DecidableEq W], List (Matrix W W ℂ) → Prop) : Prop :=
  Theorem1Statement elementary parallel ∧ Theorem3Statement elementary parallel

end Qatlib.Papers.LatticeHam18.MainResults.LatticeSimulation
