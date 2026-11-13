/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenerativeAdv25.MainResults.Model.FiniteLaws
import Qatlib.Papers.GenerativeAdv25.MainResults.Model.ParameterizedSwap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# GenerativeAdv25 — classical vs. quantum sampling interfaces

Fixed paper version: arXiv:2509.09033v1, Sections 1–5 (Theorems 1–3, 13–14 and
Proposition 4), Appendix H (Definitions 13–17).

The paper's generative-advantage theorems compare two *classes of samplers*:

* **classical samplers** — deterministic functions of polynomially many uniformly random
  bits (`uniformPushLaw f`),
* **quantum samplers** — unitaries acting on polynomially many ancilla qubits followed by a
  computational-basis measurement (`bornLaw`), which can produce output laws that are not
  pushforwards of uniform bits.

`QuantumSampleableWith s ν` says that `ν` is the law of measuring the last `m` of `s + m`
qubits after applying a unitary to `|0…0⟩`.  This makes quantum sampleability a genuinely
larger class than classical pushforward sampling, so `QuantumlyEasy` and `ClassicallyHard`
are not complementary by construction.

These notions are the interface on which Theorems 1–2, 12–14 and Proposition 4 are stated.
The repo does not formalize BQP/BPP/the polynomial hierarchy or the IDQNN architecture of
Definition 17; those statements are therefore recorded at this interface level in
`Source/GenerativeAdvantage.lean`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.GenerativeAdv25.MainResults

/-- The all-zero bit string. -/
def zeroBits (n : ℕ) : Bit n := fun _ => false

/-- Unitarily of a square matrix: both left and right inverse of `Uᴴ` is `U`. -/
def IsUnitary {X : Type*} [Fintype X] [DecidableEq X] (U : QOp X) : Prop :=
  Matrix.conjTranspose U * U = 1 ∧ U * Matrix.conjTranspose U = 1

/-- The Born-rule measurement law of a unitary applied to `|0…0⟩` and measured in the
computational basis: `prob y = ‖U y 0‖²`.  Column normalisation follows from unitarity of
`U` (`Matrix.conjTranspose U * U = 1`). -/
def bornLaw {n : ℕ} (U : QOp (Bit n))
    (hU : Matrix.conjTranspose U * U = 1) : FinDist (Bit n) where
  prob y := Complex.normSq (U y (zeroBits n))
  nonneg y := Complex.normSq_nonneg _
  sum_one := by
    have h := congrFun (congrFun hU (zeroBits n)) (zeroBits n)
    rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at h
    have hε : ((∑ x, Complex.normSq (U x (zeroBits n)) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      simp only [Complex.normSq_eq_conj_mul_self]
      exact h
    exact Complex.ofReal_injective hε

/-- `ν` is sampleable by a polynomial-ancilla quantum circuit of size `s`: it is the law of
measuring the last `m` qubits of a `(s + m)`-qubit unitary applied to `|0…0⟩`. -/
def QuantumSampleableWith (s : ℕ) {m : ℕ} (ν : FinDist (Bit m)) : Prop :=
  ∃ (U : QOp (Bit (s + m)))
    (hU : Matrix.conjTranspose U * U = 1),
    ν = pushForward (bornLaw U hU) (fun z (i : Fin m) => z (Fin.natAdd s i))

/-- `ν` is sampleable by a classical circuit of `s` uniform random bits. -/
def ClassicallySampleableWith (s : ℕ) {m : ℕ} (ν : FinDist (Bit m)) : Prop :=
  ∃ f : Bit s → Bit m, uniformPushLaw f = ν

/-- A size function is polynomially bounded: `s n ≤ c (n+1)^k` for some `c, k`. -/
def PolyBounded (s : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, s n ≤ c * (n + 1) ^ k

/-- A conditional-law family is quantumly easy: a polynomial-size quantum sampler generates
every conditional output law. -/
def QuantumlyEasy {m : ℕ} (p : ∀ n, CondLaw n m) : Prop :=
  ∃ s : ℕ → ℕ, PolyBounded s ∧ ∀ n x, QuantumSampleableWith (s n) (p n x)

/-- A conditional-law family is classically easy: a polynomial-size classical sampler
generates every conditional output law. -/
def ClassicallyEasy {m : ℕ} (p : ∀ n, CondLaw n m) : Prop :=
  ∃ s : ℕ → ℕ, PolyBounded s ∧ ∀ n x, ClassicallySampleableWith (s n) (p n x)

/-- A conditional-law family is classically hard: no polynomial-size classical sampler
generates it. -/
def ClassicallyHard {m : ℕ} (p : ∀ n, CondLaw n m) : Prop :=
  ¬ ClassicallyEasy p

/-- **Open conjecture / complexity hypothesis — not proved in Qatlib.** **Conjecture 1** (arXiv:2509.09033v1, Section 5, stated before Theorem 13): there is a
family of conditional distributions that a quantum computer generates efficiently but no
classical computer can.  The paper instantiates this family with instantaneously-deep QNN
laws (Definition 17); the Lean statement only records the separation, because the IDQNN
architecture is not modelled in this repository. -/
def Conjecture1 : Prop :=
  ∃ (m : ℕ) (p : ∀ n, CondLaw n m), QuantumlyEasy p ∧ ClassicallyHard p

/-- A law is exactly classically sampleable with polynomially many bits. -/
def ClassicallyEfficient (m : ℕ) (ν : FinDist (Bit m)) : Prop :=
  ∃ s : ℕ, ∃ _ : PolyBounded (fun _ => s), ClassicallySampleableWith s ν

/-- A conditional law is *samplable* (the paper's generative-QNN output class): it is exactly
a pushforward of a uniform law on some ancilla register.  Proposition 3 shows every
conditional distribution is approximable in TVD by such laws. -/
def SamplableLaw {m : ℕ} (ν : FinDist (Bit m)) : Prop :=
  ∃ (r : ℕ) (f : Bit r → Bit m), uniformPushLaw f = ν

end Qatlib.Papers.GenerativeAdv25.MainResults
