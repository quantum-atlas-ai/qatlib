/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel

set_option backward.isDefEq.respectTransparency false

/-!
# Efficient implementation of the measurement — Section 1.3

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025).

This file states Theorem 7 (p. 8, restated p. 27).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults.Efficiency

open Matrix BigOperators
open scoped Classical MatrixOrder ComplexOrder BigOperators

/-- **Theorem 7** (arXiv:2510.07298v2, p. 8, restated p. 27, Equation (4)/(12)).
Let `S` be a set of symmetric states and let `λ` be a primal solution, i.e. an
ensemble of nonnegative reals satisfying Equations (1) and (2).  Assume that
these numbers are efficiently quantum sampleable, i.e. that the unitary
`U : |i⟩|0⟩ ↦ ∑_k ∑_{H∈Λ_k} √(λ_i^H) |α̂_i|/α̂_i |i⟩|H⟩` can be computed in time
`poly(n)`.  Then one can construct a POVM `{F_{H,y}} ∈ Γ(S)` such that
1. `ρ(S; {F_{H,y}}) = ρ^L(S; (λ_i^H))`, and
2. `{F_{H,y}}` can be efficiently implemented in time `poly(n)`.

The present formalisation captures the information-theoretic conclusion (item 1
plus membership in `Γ(S)`); the polynomial-time claims (sampleability of `λ`
and circuit implementation of the POVM) require a model of quantum computation,
which this paper block does not contain.  See the comment below for the exact
gap. -/
def theorem7 (n : ℕ) (S : SymFamily n) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (lam : PrimalFamily n) (hfeas : PrimalFeasible S lam) : Prop :=
  ∃ M : Measurement n,
      Gamma S M ∧ score S C M = lambdaValue S C lam
  -- Paper: arXiv:2510.07298v2, Theorem 7, p. 8 and p. 27, Equations (4)/(12).
  -- Key steps (p. 27–28): (a) Theorem 2 gives, for each `k`, `H ∈ Λ_k` and
  -- `s ∈ 𝔽₂^{n−k}`, a real `β_s^H` with `λ_i^H |α̂_i|² = (β_s^H)²` for every
  -- `i ∈ D_H(s)` (Equation (13)); (b) write `i = Hᵀ t + v_s` with `v_s` the coset
  -- leader and decompose `x·i = (Hx)·t + x·v_s` (Equation (14)); (c) define
  -- `Ũ = (H^{⊗n} ⊗ I) U (H^{⊗n} ⊗ I)` and construct
  -- `F_{H,y} = ∑_s β_s^H |B_{H,s,y}⟩⟨B_{H,s,y}|` from the sampled amplitudes,
  -- which is a POVM in `Γ(S)`; (d) evaluate `ρ` on it and use Equation (13) to
  -- get `ρ(S; {F}) = ∑_i |α̂_i|² λ_i = ρ^L(S; λ)`; (e) the circuit for `U`
  -- plus the Hadamards and the controlled operations gives item 2.
  -- Scope note: this definition states the existence and value identity.
  -- Quantum-circuit cost semantics for sampleability and implementation, as
  -- well as the coset-constancy result in Theorem 2, are outside this block.
  -- Related paper statements: Proposition 11 (basis `|A_s^{H,y}⟩`) and Theorem 2.

end Qatlib.Papers.UnambigMeas25.MainResults.Efficiency
