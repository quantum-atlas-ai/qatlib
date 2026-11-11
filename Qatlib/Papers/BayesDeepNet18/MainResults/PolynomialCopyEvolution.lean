/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Bayesian Deep Learning on a Quantum Computer (arXiv:1806.11463), Theorem 1.

Paper statement (arXiv:1806.11463, Theorem 1, p.5): "Given O(N²t²/ε) copies of
the d-dimensional qubit density matrix ρ, and the order-N polynomial of Hadamard
and diagonal outer products, P^N_{(⊙,⊘)}(ρ) = Σ_{r} c_r ρ^{(⊙,⊘)r}, there exists
a quantum algorithm to implement the unitary e^{-i P^N_{(⊙,⊘)}(ρ) t} on a
d-dimensional qubit input state σ for a time t to accuracy ε in operator norm."

Paper version read: arXiv:1806.11463 (PDF pages 4-6). Proof route (Eqs. (16)-(18),
pp.5-6): build the recursive source operator S̃ from the S₁/S₂ building blocks of
Lemmas 1-2 so that conjugating by e^{-i δ S̃} and tracing out the source registers
implements e^{-i δ P^N(ρ)} on σ up to O(δ²) per round; a Lie product formula over
the N monomials plus O(N²t²/ε) rounds yields the claimed accuracy and copy count.
-/
import Qatlib.Papers.BayesDeepNet18.MainResults.CopyEvolutionModel
import Qatlib.Papers.BayesDeepNet18.MainResults.HadamardCopyEvolution
import Qatlib.Papers.BayesDeepNet18.MainResults.DiagOuterCopyEvolution

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.BayesDeepNet18.MainResults

/-- The two elementwise products available to the polynomial
`P^N_{(⊙,⊘)}` of arXiv:1806.11463, Theorem 1. -/
inductive ElementwiseOp where
  /-- The Hadamard (entrywise) product `⊙`. -/
  | hadamard : ElementwiseOp
  /-- The outer product `⊘` of the diagonal entries. -/
  | diagOuter : ElementwiseOp

/-- Apply one elementwise product to a pair of operators
(arXiv:1806.11463, Theorem 1, p.5). -/
def applyOp {d : ℕ} (op : ElementwiseOp) (ρ₁ ρ₂ : Operator d) : Operator d :=
  match op with
  | ElementwiseOp.hadamard => hadamardProduct ρ₁ ρ₂
  | ElementwiseOp.diagOuter => diagOuterProduct ρ₁ ρ₂

/-- The iterated elementwise product `ρ^{(⊙,⊘)r}` attached to a word of
elementwise operations, built right-to-left from `ρ`
(arXiv:1806.11463, Theorem 1: `ρ^{(⊙,⊘)r}`). -/
def wordPower {d : ℕ} (ρ : Operator d) : List ElementwiseOp → Operator d
  | [] => ρ
  | op :: rest => applyOp op (wordPower ρ rest) ρ

/-- The order-`N` polynomial of Hadamard and diagonal outer products
`P^N_{(⊙,⊘)}(ρ) = Σ_{r≤N} c_r ρ^{(⊙,⊘)r}` of arXiv:1806.11463, Theorem 1 (p.5);
`coeff r` is `c_r` and `word r` selects the elementwise word of the `r`-th term. -/
def polynomialOperator {d : ℕ} (N : ℕ) (coeff : ℕ → ℂ) (word : ℕ → List ElementwiseOp)
    (ρ : Operator d) : Operator d :=
  ∑ r ∈ Finset.range (N + 1), coeff r • wordPower ρ (word r)

/-- Apply one elementwise step with time step `δ` to the input `σ`, routing to
the Lemma 1 step (`⊙`) or the Lemma 2 step (`⊘`) according to `op`. -/
def elementwiseStep {d : ℕ} (ρ : Operator d) (δ : ℝ) :
    List ElementwiseOp → Operator d → Operator d
  | [], σ => σ
  | op :: rest, σ =>
      elementwiseStep ρ δ rest
        ((match op with
          | ElementwiseOp.hadamard => hadamardEvolutionStep ρ ρ δ
          | ElementwiseOp.diagOuter => diagOuterEvolutionStep ρ ρ δ) σ)

/-- One round of the Theorem 1 algorithm: apply, for each monomial `r ≤ N`, the
elementwise step scaled by the coefficient `c_r` (arXiv:1806.11463, Eqs. (16)-(18)). -/
def polynomialEvolutionStep {d : ℕ} (N : ℕ) (coeff : ℕ → ℝ)
    (word : ℕ → List ElementwiseOp) (ρ : Operator d) (δ : ℝ) (σ : Operator d) : Operator d :=
  (List.range (N + 1)).foldl (fun σ r => elementwiseStep ρ (coeff r * δ) (word r) σ) σ

end Qatlib.Papers.BayesDeepNet18.MainResults
