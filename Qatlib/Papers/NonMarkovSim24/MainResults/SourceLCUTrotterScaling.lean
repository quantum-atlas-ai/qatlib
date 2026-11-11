/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonMarkovSim24.MainResults.DQMEModel
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# c005 — LCU-Trotter simulation: linear qubit-count and depth scaling

Paper: arXiv:2401.17255v4, Sec. IV p. 7 (LCU-Trotter algorithm), Appendix C.

Claim (c005): after Trotter-decomposing the LCU propagators `U_0(δt)` and
`U_±^ϵ(δt)` into elementary gates, both the number of qubits and the circuit
depth of the LCU-Trotter algorithm grow linearly with the number of dissipaton
degrees of freedom `K`, in contrast with classical HEOM costs that grow
exponentially.

The encoding (Eq. (27) and Eq. (30)) stores the RDT in a register of dimension
`d_S² · N^K`, where `d_S = dim H_S` and `N` is the number of levels kept per
dissipaton mode.  A register of dimension `D` needs `clog₂ D` qubits, so the
qubit count obeys

`nQubits(K) ≤ clog₂(d_S²) + K · clog₂(N)`,

a linear function of `K` (`qubit_count_linear`).  If every Trottter step costs a
fixed overhead plus a per-mode cost, the total depth over `steps` steps is
`steps · (base + K · perMode)`, which is also linear in `K`
(`lcu_trotter_linear_scaling`).

Appendix C refines the depth to a polynomial `O(λ^{3/2} t³ Err^{-2} K^{5/2})`
once the error budget and amplitude amplification are included; the main-text
linear statement formalized here is the scaling in the dissipaton degrees of
freedom at fixed Trotter step count and fixed error-control constants.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonMarkovSim24.MainResults

/-- Number of qubits needed to encode an RDT register of dimension
`d_S² · N^K` (Eq. (27)/(30): `d_S²` for the vectorized system density matrix
and `N` levels for each of the `K` dissipaton modes). -/
def encodedQubits (dS N K : ℕ) : ℕ := Nat.clog 2 (dS * dS * N ^ K)

/-- **Qubit count is linear in the dissipaton DOF.**  For `N ≥ 2` levels per
dissipaton mode, the encoding of Eq. (27)/(30) uses at most
`clog₂(d_S²) + K · clog₂(N)` qubits, i.e. a linear function of the number `K`
of dissipaton modes. -/
theorem qubit_count_linear (dS N K : ℕ) (hN : 1 < N) :
    encodedQubits dS N K ≤ Nat.clog 2 (dS * dS) + K * Nat.clog 2 N := by
  unfold encodedQubits
  apply Nat.clog_le_of_le_pow
  have h1 : dS * dS ≤ 2 ^ Nat.clog 2 (dS * dS) :=
    Nat.le_pow_clog (b := 2) (by norm_num) (dS * dS)
  have h2 : N ≤ 2 ^ Nat.clog 2 N :=
    Nat.le_pow_clog (b := 2) (by norm_num) N
  calc dS * dS * N ^ K
      ≤ 2 ^ Nat.clog 2 (dS * dS) * (2 ^ Nat.clog 2 N) ^ K :=
        Nat.mul_le_mul h1 (pow_le_pow_left' h2 K)
    _ = 2 ^ Nat.clog 2 (dS * dS) * 2 ^ (Nat.clog 2 N * K) := by rw [pow_mul]
    _ = 2 ^ (Nat.clog 2 (dS * dS) + Nat.clog 2 N * K) := by rw [← pow_add]
    _ = 2 ^ (Nat.clog 2 (dS * dS) + K * Nat.clog 2 N) := by
        rw [Nat.mul_comm (Nat.clog 2 N) K]

/-- Circuit depth of the LCU-Trotter algorithm: `steps` Trotter steps, each
costing a fixed overhead `base` plus `perMode` gates per dissipaton mode. -/
def trotterDepth (steps base perMode K : ℕ) : ℕ := steps * (base + K * perMode)

/-- One additional dissipaton mode adds exactly `steps * perMode` layers of
circuit depth. -/
theorem trotter_depth_linear (steps base perMode K : ℕ) :
    trotterDepth steps base perMode (K + 1)
      = trotterDepth steps base perMode K + steps * perMode := by
  unfold trotterDepth
  ring

/-- **c005: LCU-Trotter linear scaling.**  Both resources of the LCU-Trotter
implementation of the DQME-SQ grow linearly in the number of dissipaton modes
`K`:

* the qubit count is at most `clog₂(d_S²) + K · clog₂(N)`;
* the circuit depth is `trotterDepth(0) + K · steps · perMode`.

This is the main-text scalability statement of Sec. IV p. 7 ("both the number
of qubits and the circuit depth grow linearly with the increase in the degrees
of freedom of the dissipatons"). -/
theorem lcu_trotter_linear_scaling (dS N steps base perMode : ℕ) (hN : 1 < N) :
    (∀ K, encodedQubits dS N K ≤ Nat.clog 2 (dS * dS) + K * Nat.clog 2 N)
      ∧ (∀ K, trotterDepth steps base perMode K
          = trotterDepth steps base perMode 0 + K * (steps * perMode)) := by
  refine ⟨fun K => qubit_count_linear dS N K hN, ?_⟩
  intro K
  induction K with
  | zero => simp [trotterDepth]
  | succ K ih =>
      rw [trotter_depth_linear, ih]
      ring

end Qatlib.Papers.NonMarkovSim24.MainResults
