/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# GWSpeedupYuan25 — Pauli `ℓ1` norm under Kronecker products (Proposition 26)

Fixed arXiv:2510.08292v1 (9 Oct 2025).

Paper statement (Proposition 26, §VI, PDF line 1209):
if `C = C₁ ⊗ C₂` is a Kronecker product of two Pauli-sparse operators with Pauli
expansions `c₁, c₂`, then
`‖C‖_{P,ℓ1} = ‖C₁‖_{P,ℓ1} · ‖C₂‖_{P,ℓ1}`; consequently sampling from the
Kronecker graph can be done in `O(2^k m)` time.

The multiplicativity is proved here by the finite double-sum factorisation: the
Pauli coefficients of a Kronecker product are the pairwise products
`c₁(p₁) · c₂(p₂)`, so the `ℓ1` norm factorises. The `O(2^k m)` sampling cost is
an algorithmic corollary and is not separately formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults.PauliSparse

open Matrix Qatlib.Papers.GWSpeedupYuan25.MainResults
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Proposition 26 (arXiv:2510.08292v1, §VI, PDF line 1209): the Pauli `ℓ1` norm
is multiplicative under Kronecker products. The index `PauliIndex n × PauliIndex m`
is the Pauli label of the product system `n + m` (via the standard identification
`PauliIndex (n+m) ≃ PauliIndex n × PauliIndex m`), with coefficient
`c₁(p₁) · c₂(p₂)`. -/
theorem prop26_pauliL1_kronecker {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c₁ : ι → ℝ) (c₂ : κ → ℝ) :
    pauliL1 (fun p : ι × κ => c₁ p.1 * c₂ p.2) = pauliL1 c₁ * pauliL1 c₂ := by
  simp only [pauliL1, abs_mul, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

end Qatlib.Papers.GWSpeedupYuan25.MainResults.PauliSparse
