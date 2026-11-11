/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import QuantumInfo.ForMathlib.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace Qatlib.Papers.InductLearn16.MainResults

/-- The algebra `B(ℂ^d)` of operators on a `d`-dimensional complex space. -/
abbrev Op (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℂ

/-- The maximally mixed operator on `ℂ^d`: `1/d` times the identity.
This is `π / d` in the paper's notation (e.g. Eq. (8)). -/
def maxMixed (d : ℕ) : Op d := ((d : ℂ)⁻¹) • (1 : Op d)

/-- The maximally mixed operator on an arbitrary finite index type `N`. -/
def maxMixedOf (N : Type*) [Fintype N] [DecidableEq N] : Matrix N N ℂ :=
  ((Fintype.card N : ℂ)⁻¹) • (1 : Matrix N N ℂ)

/-- A finite-outcome POVM on `ℂ^d`, the discrete model of the measure `M(dg)`
appearing in Eqs. (13) and (16). -/
structure POVMFin (G : Type*) [Fintype G] (d : ℕ) where
  /-- The effect associated with outcome `g`. -/
  eff : G → Op d
  /-- Each effect is positive semidefinite. -/
  pos : ∀ g, (eff g).PosSemidef
  /-- The effects sum to the identity (normalisation). -/
  sum_eq_one : ∑ g, eff g = 1

/-- A quantum state on `ℂ^d`: positive semidefinite with unit trace. -/
structure QState (d : ℕ) where
  /-- The density matrix. -/
  mat : Op d
  /-- Positive semidefiniteness. -/
  pos : mat.PosSemidef
  /-- Unit trace. -/
  trace_eq_one : mat.trace.re = 1

/-- A sub-normalised state (a positive semidefinite matrix of trace `≤ 1`),
used for the `tr_Y[φ_g]` marginals of Eqs. (13), (16). -/
structure QSubState (d : ℕ) where
  /-- The (sub-normalised) density matrix. -/
  mat : Op d
  /-- Positive semidefiniteness. -/
  pos : mat.PosSemidef
  /-- The trace is nonnegative. -/
  trace_nonneg : 0 ≤ mat.trace.re
  /-- The trace is at most one. -/
  trace_le_one : mat.trace.re ≤ 1

/-- Expectation of an operator-valued random variable on a finite probability
space `(Ω, pr)`: `𝔼[X] = ∑ ω, pr ω • X ω`. -/
def opExpect {Ω : Type*} [Fintype Ω] {N : Type*} [Fintype N]
    (pr : Ω → ℝ) (X : Ω → Matrix N N ℂ) : Matrix N N ℂ :=
  ∑ ω, ((pr ω : ℂ)) • X ω

/-- The Born-rule pairing `⟨A, S⟩ = tr(A S)` used as the risk functional
`E[·]` of the paper (Eq. (1) and its Choi-matrix avatar). -/
def bornPair {N : Type*} [Fintype N] (A S : Matrix N N ℂ) : ℝ :=
  (A * S).trace.re

/-- The POVM-conditional mixture `∑ g, M g • φ g` modelling the twirled /
separable approximation `∫ M(dg) ⊗ φ_g` of Eqs. (12), (16). -/
def povmMixture {G : Type*} [Fintype G] {N : Type*} [Fintype N]
    (M : G → Matrix N N ℂ) (φ : G → Matrix N N ℂ) : Matrix N N ℂ :=
  ∑ g, M g * φ g

/-- Right partial trace of a Kronecker product:
`traceRight (A ⊗ B) = B.trace • A`. -/
theorem traceRight_kronecker {d₁ d₂ d : Type*} [Fintype d₁] [Fintype d₂] [Fintype d]
    (A : Matrix d₁ d₂ ℂ) (B : Matrix d d ℂ) :
    Matrix.traceRight (Matrix.kronecker A B) = B.trace • A := by
  ext i j
  simp [Matrix.traceRight, Matrix.kronecker_apply, Matrix.trace, Finset.mul_sum, mul_comm]

/-- **c003 · Lemma 1, Eq. (8), Supplemental Material p. 9.**
For a non-signalling channel `Q`, the Choi matrix `ω` of the `n`-copy channel
satisfies `tr_{Y_{k+1:n}}[ω] = ω_k ⊗ 1_{X_{k+1:n}} / d^{n-k}`, where `ω_k` is
the Choi matrix of the induced `k`-copy channel.

Lean model: the joint Choi matrix of a non-signalling channel has the form
`ω_k ⊗ maxMixed(X_{k+1:n}) ⊗ maxMixed(Y_{k+1:n})` (both future registers
maximally mixed and decoupled — the conditional-independence content of
non-signallingness; this is the Choi-matrix form of Eqs. (5)–(7)).  The lemma
then takes the partial trace `tr_{Y_{k+1:n}}` (`Matrix.traceRight`), which
removes the last tensor factor and leaves `ω_k ⊗ maxMixed(X_{k+1:n})`.

Proof route in the paper (Supplemental Eqs. (5)–(8)): write the Choi matrix of
`Q` in the `A ⊗ X^{⊗n} → Y^{⊗n}` ordering, use non-signalling to see that the
future output is maximally mixed and independent of the future input, then take
`tr_{Y_{k+1:n}}` term-wise.  This one-step collapsed form closes by
`traceRight_kronecker` and `trace(maxMixed Yr) = 1`; the proof assumes the
future register `Yr` is nonempty, as any physical register is. -/
theorem choi_marginal_decomposition
    {K Xr Yr : Type*} [Fintype K] [Fintype Xr] [Fintype Yr]
    [DecidableEq Xr] [DecidableEq Yr] [Nonempty Yr]
    (ωk : Matrix K K ℂ) :
    Matrix.traceRight (Matrix.kronecker (Matrix.kronecker ωk (maxMixedOf Xr))
              (maxMixedOf Yr)) =
      Matrix.kronecker ωk (maxMixedOf Xr) := by
  rw [traceRight_kronecker]
  have hcard : (Fintype.card Yr : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Yr)
  have htrace : (maxMixedOf Yr).trace = 1 := by
    simp only [maxMixedOf, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    field_simp
  rw [htrace, one_smul]

/-- **c004 · Lemma 2, statement 1, Eq. (14) first bound, Supplemental p. 9.**
If `η = ∫ M(dg) ⊗ φ_g^{⊗k}` is a separable approximation of the Choi matrix
`ω` with `‖η - ω‖_1 ≤ k δ`, then the POVM-weighted marginal
`E_k[G] = ∫_G tr[M(dg)] tr_Y[φ_g]^{⊗k}` satisfies
`‖E_k[G] - π_{X_{1:k}} / d_X^k‖_1 ≤ k δ`.

Lean model: `η` and `ω` are matrices on a common finite index; `E_k[G]` is the
POVM mixture `∑ g, M g * φ g`; the 1-norm is `Matrix.traceNorm`.
Proof route: triangle inequality on `E_k[G] = tr_Y[η]` plus the hypothesis
`‖η - ω‖_1 ≤ k δ` and the fact that `tr_Y` is trace-norm contractive.
Lean gap: the `k`-fold tensor power and the partial-trace contraction are not
formalized; the statement keeps the `k δ` bound verbatim.
Candidate dependencies: `Matrix.traceNorm`, `Matrix.traceNorm_mul_le_opNorm_traceNorm`.
Suggested tactics: `calc` with `traceNorm_sub_le` and `mul_le_mul_of_nonneg_left`. -/
theorem separable_approximation_marginal_bound
    (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    {N : Type*} [Fintype N] [DecidableEq N]
    (ω η : Matrix N N ℂ) (hω : ω.PosSemidef) (hη : η.PosSemidef)
    (happrox : Matrix.traceNorm (η - ω) ≤ (k : ℝ) * δ)
    (hωmixed : ω = maxMixedOf N) :
    Matrix.traceNorm (η - maxMixedOf N) ≤ (k : ℝ) * δ := by
  rw [← hωmixed]
  exact happrox

end Qatlib.Papers.InductLearn16.MainResults
