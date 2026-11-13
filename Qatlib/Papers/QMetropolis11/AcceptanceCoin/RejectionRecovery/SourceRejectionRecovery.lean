/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Rejection recovery failure bound (Temme et al. 2011, Sec. 3.1, Eqs. (4)-(7))

Fixed source: arXiv:0911.3635v2, Section 3.1, printed pages 7-8.  The paper
repeats the binary measurements `P` (fail = outcome `0`) and `Q` and shows
that the failure probability after `n ≥ 2` rounds obeys

`p_fail(n) ≤ d*(1-d*)(d*² + (1-d*)²)^n`,                        (6)
`p_fail(n) ≤ 1/(2(n+1)) (1/(1+1/n))^n ≈ 1/(2e(n+1))`.            (7)

The formal contract `RejectionFailureBound` formalises the actual finite
Kraus-word recursion `Σ_s ‖W_s ξ‖²` with `W_s = P₀ Q_s P₀` and proves the
strict universal bound `≤ 1/(2(n+1))`.  It records in its docstring why the
middle expression, not `1/(2e(n+1))`, is the exact finite-`n` maximum of
`d(1-d)(d²+(1-d)²)^n`; the `e`-constant is asymptotic.

Reused FQNs:
`Qatlib.Concepts.MixedInstrument.RewindAlgebra.rejectionFailureBound`
and `rejectFailProb` (same namespace).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin.RejectionRecovery

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedInstrument.RewindAlgebra

variable {D : ℕ}

/-- **c005, Eq. (7), strict form.**  For orthogonal projectors `P Q`, a
normalized `P`-eigenstate `ψ` (the paper's crucial initial-state condition,
"the initially prepared state is an eigenstate of `P₁`"), and every round
count `n ≥ 1`, the actual finite-word failure probability obeys
`p_fail(n) ≤ 1/(2(n+1))`.  Reused FQN:
`...RewindAlgebra.rejectionFailureBound`. -/
theorem source_rejection_failure_le (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P * P = P) (hQs : Q.IsHermitian) (hQi : Q * Q = Q)
    (ψ : QState (Fin D)) (hnorm : Inner ψ ψ = 1) (hψ : P *ᵥ ψ = ψ)
    (n : ℕ) (hn : 1 ≤ n) :
    rejectFailProb P Q ψ n ≤ 1 / (2 * (n + 1)) :=
  rejectionFailureBound D P Q hPs hPi hQs hQi ψ hnorm hψ n hn

/-- **c005, full claim.**  The `RejectionFailureBound` contract in one
line.  Reused FQN:
`...RewindAlgebra.rejectionFailureBound`. -/
theorem source_rejectionFailureBound : RejectionFailureBound :=
  rejectionFailureBound

/-- **c005, Eq. (6) scalar form.**  The exact per-branch failure weight
`d*(1-d*)(d*² + (1-d*)²)^n` (the paper's `d* ∈ [0,1]`) is bounded by
`1/(2(n+1))`, uniformly over `d*`.  This is the literal exponential-in-`n`
expression of Eq. (6) before the `≈ 1/(2e(n+1))` replacement.  Reused FQN:
`...RewindAlgebra.rejection_scalar_bound`. -/
theorem source_scalar_failure_decay (t : ℝ) (ht : t ∈ Set.Icc 0 1) (n : ℕ) :
    t * (1 - t) * (t ^ 2 + (1 - t) ^ 2) ^ n ≤ 1 / (2 * (n + 1)) :=
  rejection_scalar_bound t ht n

end Qatlib.Papers.QMetropolis11.AcceptanceCoin.RejectionRecovery
