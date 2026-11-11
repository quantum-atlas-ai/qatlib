/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# DigitalCost — Proposition 8 (arXiv:2303.01471v1, Appendix G)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
PDF page 63: with `R` iterations the digital implementation has T-count
`2 ((c_add + c_mult)(s + 2) + c_aqft) d R`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.DigitalCost

/-- T-count of one iteration of the digital implementation: for each of the `d`
variables, `s + 2` adder/multiplier blocks plus one approximate QFT. -/
def perIterationTCount (cadd cmult caqft s d : ℕ) : ℕ :=
  ((cadd + cmult) * (s + 2) + caqft) * d

/-- T-count of the full digital implementation with `R` iterations (the factor
`2` is the two controlled executions per iteration in Algorithm 3). -/
def digitalTCount (cadd cmult caqft s d R : ℕ) : ℕ :=
  2 * R * perIterationTCount cadd cmult caqft s d

/-!
### Proposition 8

Source: arXiv:2303.01471v1, Proposition 8, p.63, Appendix G.

Consider a `d`-dimensional quadratic program whose matrix has at most `s`
non-zero entries in each row/column. With `R` iterations, the digital
implementation has T-count `2 ((c_add + c_mult)(s + 2) + c_aqft) d R`, where
`c_add`, `c_mult`, `c_aqft` are the T-counts of the adder, multiplier, and
approximate QFT.

Paper proof route: expand the per-iteration cost of Algorithm 3, which uses
`s + 2` adder/multiplier blocks per variable, and multiply by `d` variables,
`R` iterations and the factor `2`.
-/
/-- Proposition 8 (G): T-count `2((c_add+c_mult)(s+2)+c_aqft)dR` of the digital
QHD implementation. -/
theorem source_proposition8_tcount (cadd cmult caqft s d R : ℕ) :
    digitalTCount cadd cmult caqft s d R
      = 2 * ((cadd + cmult) * (s + 2) + caqft) * d * R := by
  unfold digitalTCount perIterationTCount
  ring

end Qatlib.Papers.QHamDescent23.MainResults.DigitalCost
