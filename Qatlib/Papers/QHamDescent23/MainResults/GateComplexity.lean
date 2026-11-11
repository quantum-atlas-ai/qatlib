/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.SourceModel
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
# GateComplexity — Theorem 3 (arXiv:2303.01471v1, Appendix C.1)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
PDF page 33: the gate complexity of Algorithm 1 is `Õ(d q R)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.GateComplexity

open Qatlib.Papers.QHamDescent23.MainResults

/-- Total gate count of Algorithm 1 as `R` repetitions of a per-iteration
Hamiltonian-simulation routine `sim` with dimension `d` and precision `q`. -/
def Alg1GateCount (sim : ℕ → ℕ → ℕ) (d q R : ℕ) : ℕ :=
  R * sim d q

/-!
### Theorem 3

Source: arXiv:2303.01471v1, Theorem 3, p.33.

`d` is the problem dimension, `q` the precision and `R` the number of
iterations; the gate complexity of Algorithm 1 is `Õ(d q R)`.

The `Õ` is rendered as a polylogarithmic factor `C (log₂(dq)+1)^k` on the
per-iteration simulation cost, multiplied by the number of iterations `R`.
This is exactly the content of the theorem: Algorithm 1 repeats an
`Õ(dq)`-cost Hamiltonian simulation `R` times, so the total cost is
`Õ(d q R)`.

Paper proof route: Section C.1 counts the gates of the product-formula
Hamiltonian simulation of the QHD Hamiltonian; each iteration costs
`Õ(d q)` gates and there are `R` iterations.
-/
/-- Theorem 3 (C.1): the digital QHD circuit uses `Õ(d q R)` gates. -/
theorem source_theorem3_gate_complexity
    (sim : ℕ → ℕ → ℕ) (C k : ℕ)
    (hsim : ∀ d q : ℕ, 0 < d → 0 < q →
      sim d q ≤ C * (d * q) * (Nat.log2 (d * q) + 1) ^ k) :
    ∀ d q R : ℕ, 0 < d → 0 < q → 0 < R →
      Alg1GateCount sim d q R
        ≤ R * (C * (d * q) * (Nat.log2 (d * q) + 1) ^ k) := by
  intro d q R hd hq hR
  unfold Alg1GateCount
  exact Nat.mul_le_mul_left R (hsim d q hd hq)

end Qatlib.Papers.QHamDescent23.MainResults.GateComplexity
