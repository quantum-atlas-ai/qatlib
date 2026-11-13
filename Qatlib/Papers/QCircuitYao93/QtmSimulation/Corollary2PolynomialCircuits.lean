/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.Theorem2QtmCircuitSimulationQuan

/-!
# Polynomial-time window simulation by circuits

`corollary2_polynomial_size_circuit` specializes finite-window QTM simulation to the time bound
`c * (n + 1) ^ k`. For positive parameters, it produces a unitary circuit with no queries, a
quadratic gate bound in the simulation time, and exact agreement on encoded states and basis
probabilities. See [Yao1993].

## Main statements

* `corollary2_polynomial_size_circuit`: constructs a circuit of at most twice the square of the
  time bound.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Corollary2PolynomialCircuits

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath

/-- For positive `n`, `c`, and `k`, the time-`c * (n + 1) ^ k` window evolution is simulated
exactly by a unitary circuit with no queries and at most `2 * (c * (n + 1) ^ k) ^ 2` gates,
preserving encoded basis probabilities. This is the polynomial-time specialization
associated with the corollary after Theorem 2 of [Yao1993]. -/
theorem corollary2_polynomial_size_circuit {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (n c k : ℕ) (hn : 0 < n)
    (hc : 0 < c) (hk : 0 < k) :
    ∃ C : Circuit (WReg (c * (n + 1) ^ k) Q A),
      IsUnitaryCircuit C ∧ QueryCount C = 0 ∧
        GateCount C ≤ 2 * (c * (n + 1) ^ k) ^ 2 ∧
        ∀ x : Fin n → A, ∀ w : WindowCfg (c * (n + 1) ^ k) Q A,
          Run (1 : Matrix (WReg (c * (n + 1) ^ k) Q A) (WReg (c * (n + 1) ^ k) Q A) ℂ) C
              (Ket (windowEncode (initWindowCfg M n x)))
            = windowEmbed ((windowStep M) ^ (c * (n + 1) ^ k) *ᵥ
                Ket (initWindowCfg M n x)) ∧
          BornProb (Run (1 : Matrix (WReg (c * (n + 1) ^ k) Q A) (WReg (c * (n + 1) ^ k) Q A) ℂ) C
              (Ket (windowEncode (initWindowCfg M n x)))) (windowEncode w)
            = BornProb ((windowStep M) ^ (c * (n + 1) ^ k) *ᵥ
                Ket (initWindowCfg M n x)) w := by
  have hnk : n < (n + 1) ^ k := by
    calc n < n + 1 := by omega
      _ = (n + 1) ^ 1 := by ring
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) hk
  have hnt : n ≤ c * (n + 1) ^ k := by
    calc n ≤ (n + 1) ^ k := le_of_lt hnk
      _ ≤ c * (n + 1) ^ k := Nat.le_mul_of_pos_left _ hc
  have ht : 0 < c * (n + 1) ^ k := Nat.mul_pos hc (pow_pos (by omega) k)
  obtain ⟨C, hCu, hCq, hCg, hCsem⟩ :=
    theorem2QtmCircuitSimulation Q A M n (c * (n + 1) ^ k) hn ht hnt
  exact ⟨C, hCu, hCq, hCg.trans_eq (by ring), hCsem⟩

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Corollary2PolynomialCircuits
