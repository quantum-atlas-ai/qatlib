/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulationQuan

/-!
# Elementary compilation of polynomial-time simulations

The module bounds the elementary-gate ledger for a finite-window simulation by a quadratic
function of its time. `corollary2_elementary_polynomial_circuit` produces a list of `Phi3Gate`
gates that exactly simulates the polynomial-time window evolution on encoded inputs, preserving
normalization and basis probabilities. See [Yao1993].

## Main statements

* `phi3_ledger_le_quadratic`: bounds the local compilation ledger by a constant times t².
* `corollary2_elementary_polynomial_circuit`: constructs the elementary gate list with exact
  simulation guarantees.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.PolynomialPhi3
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.CircuitImpl.Phi3Universal

/-- For positive `t`, the displayed elementary compilation ledger is at most `3 *
(phi3PaddingBudget (3 * b) + phi3PaddingBudget b) * t ^ 2`. -/
theorem phi3_ledger_le_quadratic (t b : ℕ) (ht : 0 < t) :
    t * ((2*t-1) * phi3PaddingBudget (3*b) + (2*t+1) * phi3PaddingBudget b) ≤
      3 * (phi3PaddingBudget (3*b) + phi3PaddingBudget b) * t^2 := by
  calc
    _ ≤ t * ((3*t) * phi3PaddingBudget (3*b) + (3*t) * phi3PaddingBudget b) := by
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right _ (by omega : 2*t-1 ≤ 3*t)
      · exact Nat.mul_le_mul_right _ (by omega : 2*t+1 ≤ 3*t)
    _ = _ := by ring

/-- For the stated positive parameters and cell-code capacity bound, there is a unitary
elementary circuit with no queries, the displayed quadratic-in-time length bound, and exact
encoded state and basis-probability agreement with the window evolution. This gives an
elementary-gate form of the corollary after Theorem 2 of [Yao1993]. -/
theorem corollary2_elementary_polynomial_circuit
    {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (M : LocalQTM Q A) (b n c k : ℕ)
    (hb : Fintype.card (CellState Q A) ≤ 2^b) (hn : 0 < n)
    (hc : 0 < c) (hk : 0 < k) :
    let t := c * (n+1)^k
    let e := finiteBasisCode (CellState Q A) b hb
    ∃ gs : List (Phi3Gate ((2*t+1)*b+3)),
      IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
      GateCount (phi3Compile gs) = gs.length ∧
      gs.length ≤ 3 * (phi3PaddingBudget (3*b) + phi3PaddingBudget b) * t^2 ∧
      ∀ (x : Fin n → A) (w : WindowCfg t Q A),
        Normalized (qtmPhi3State t b e (Ket (windowEncode (initWindowCfg M n x)))) ∧
        Normalized (Run (1 : Matrix (Reg ((2*t+1)*b+3)) (Reg ((2*t+1)*b+3)) ℂ)
          (phi3Compile gs)
          (qtmPhi3State t b e (Ket (windowEncode (initWindowCfg M n x))))) ∧
        Run (1 : Matrix (Reg ((2*t+1)*b+3)) (Reg ((2*t+1)*b+3)) ℂ)
          (phi3Compile gs) (qtmPhi3State t b e (Ket (windowEncode (initWindowCfg M n x)))) =
          qtmPhi3State t b e (windowEmbed ((windowStep M)^t *ᵥ Ket (initWindowCfg M n x))) ∧
        BornProb (Run (1 : Matrix (Reg ((2*t+1)*b+3)) (Reg ((2*t+1)*b+3)) ℂ)
          (phi3Compile gs) (qtmPhi3State t b e (Ket (windowEncode (initWindowCfg M n x)))))
          (qtmPhi3Basis t b e (windowEncode w)) =
          BornProb ((windowStep M)^t *ᵥ Ket (initWindowCfg M n x)) w := by
  (try dsimp only)
  let t := c * (n+1)^k
  have hnk : n < (n+1)^k := by
    calc
      n < n+1 := by omega
      _ = (n+1)^1 := by simp
      _ ≤ (n+1)^k := Nat.pow_le_pow_right (by omega) hk
  have ht : 0 < t := Nat.mul_pos hc (pow_pos (by omega) k)
  have hnt : n ≤ t := (le_of_lt hnk).trans (Nat.le_mul_of_pos_left _ hc)
  obtain ⟨gs,hu,hq,hcount,hlen,hsem⟩ := qtmPhi3WindowSimulation Q A M b n t hb hn ht hnt
  exact ⟨gs,hu,hq,hcount,hlen.trans (phi3_ledger_le_quadratic t b ht),hsem⟩

end Qatlib.Papers.QCircuitYao93.QtmSimulation.PolynomialPhi3
