/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
# CircCompLiu24 `MainResults`: finite objects of the parameter-generating ansatz

Fixed source: arXiv:2410.09846v2, §3.1, Eq. (1) and the parameter-counting
paragraph immediately following it (v2 markdown lines 265--270).

The target classical model has `m` parameters. The paper chooses
`N = ceil(log_2 m)` qubits so that the `N`-qubit computational basis has
`2^N >= m` states, and uses an `L`-layer `R_Y + CNOT` ansatz in which every
layer carries exactly one trainable `R_Y` angle per qubit; the CNOTs of the
same layer are fixed. This module records those finite objects and the
register-level bridge to the `Reg`/`BornProb` vocabulary shared with
`Foundations.TensorRegisters.RegisterModel`. The counting and growth theorems
live in `ParameterCompression`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CircCompLiu24.MainResults

open Qatlib.Foundations.PureStateMath

/-- Number of qubits `N = ceil(log_2 m)` used to generate `m` target parameters,
as fixed by Eq. (1) of the paper. -/
def qubitCount (m : ℕ) : ℕ := Nat.clog 2 m

/-- Number of computational-basis states, hence of Born outcomes, of an
`N`-qubit register: `2^N`. -/
def basisStateCount (N : ℕ) : ℕ := 2 ^ N

/-- Trainable parameters of the `L`-layer ansatz of Eq. (1): one `R_Y` angle
per qubit per layer. The CNOT gates in the same layer have no trainable
parameters. -/
def ansatzParameterCount (N L : ℕ) : ℕ := N * L

/-- An `L = O(N^k)` layer budget `L <= C * N^k`, the polynomial-layer
assumption used by the paper's `O(polylog m)` parameter claim. -/
def PolynomialLayerBudget (k C N L : ℕ) : Prop := L ≤ C * N ^ k

/-- The `N`-qubit computational basis `Reg N` has exactly `2^N` states. -/
theorem card_reg_eq_basisStateCount (N : ℕ) :
    Fintype.card (Reg N) = basisStateCount N :=
  card_reg N

/-- With `N = ceil(log_2 m)` qubits there are at least `m` computational-basis
states, hence at least `m` Born probabilities to read out. -/
theorem card_reg_qubitCount_ge (m : ℕ) :
    m ≤ Fintype.card (Reg (qubitCount m)) := by
  rw [card_reg_eq_basisStateCount, basisStateCount, qubitCount]
  exact Nat.le_pow_clog (by decide) m

/-- The Born probabilities of a normalized state on the `N`-qubit register sum
to one, so the `2^N` basis slots really carry a probability distribution. -/
theorem sum_bornProb_reg {N : ℕ} {ψ : QState (Reg N)} (hψ : Normalized ψ) :
    ∑ x : Reg N, BornProb ψ x = 1 := by
  simpa [Normalized, BornProb] using hψ

/-- `ceil(log_2 m)` never exceeds `floor(log_2 m) + 1`. -/
theorem qubitCount_le_log2_succ (m : ℕ) :
    qubitCount m ≤ Nat.log2 m + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_log2_self (n := m)).le

end Qatlib.Papers.CircCompLiu24.MainResults
