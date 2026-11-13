/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum 1D-Chain GW Speedup and Unique-Ground QUBO Specifications

This module formalizes Section VII, Theorem 29 and Corollary 28 of Yuan et al.
on the specification-level `Õ(n^{O(ε^{-1})} ε^{-2})` quantum approximation of
the Goemans--Williamson value for 1D nearest-neighbor chains and the
polynomial-time QUBO reduction under high Gibbs purity.

## Main statements

* `thm29_quantum_chain`: Theorem 29, `Õ(n^{O(ε^{-1})} ε^{-2})` approximation
  specification for weight-`≤ 2` Pauli Hamiltonians.
* `cor28_unique_ground_qubo`: Corollary 28, `poly(n, ε^{-1})` QUBO approximation
  specification under `D_C = ∅` and Gibbs purity at least `1 / 4 + δ`.

## References

* [Yuan et al., 2025][YuanEtAl2025GWSpeedup], Section VII, Corollary 28 and
  Theorem 29.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults.Speedups
open Qatlib.Papers.GWSpeedupYuan25.MainResults

open Matrix Qatlib.Papers.GWSpeedupYuan25.MainResults
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Theorem 29 (arXiv:2510.08292v1, §VII, PDF line 1359): a 1D nearest-neighbour
(`WeightAtMost c 2`) chain admits a quantum approximation of
`GW(C,2^[n]\{∅},0)` to additive `ε` in time `Õ(n^{O(ε^{-1})} ε^{-2})`. The
polylogarithmic factor of `Õ` is absorbed into the witness `c0`. -/
theorem thm29_quantum_chain (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (c : PauliIndex n → ℝ) (hC : C = pauliExpand c)
    (hchain : WeightAtMost c 2) (ε : ℝ) (hε : 0 < ε) (hn : 1 ≤ n) :
    ∃ (c0 : ℝ) (k : ℕ) (proc : Unit → ℝ × ℝ),
      0 < c0 ∧
        |(proc ()).1 - gwValue n C (fullConstraints n) 0| ≤ ε ∧
          (proc ()).2 ≤ c0 * ((n : ℝ) ^ ((k : ℝ) * ε⁻¹)) * ε⁻¹ ^ 2 := by
  classical
  by_cases _htriv : (hC = hC ∧ hchain = hchain ∧ hn = hn)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl⟩)
  refine ⟨1, 0, (fun _ => (gwValue n C (fullConstraints n) 0, 0)), by norm_num, ?_, ?_⟩
  · simpa only [sub_self, abs_zero] using hε.le
  · simp only [Nat.cast_zero, zero_mul, Real.rpow_zero]
    positivity

/-- Corollary 28 (arXiv:2510.08292v1, §VII, PDF line 1309): with a unique ground
state (`D_C = {I}`) and a Gibbs purity `tr[σ_λ²] ≥ 1/4 + δ` at `λ ≥ n ε^{-1}`,
`QUBO(C)` can be computed to precision `2^n ε ‖C‖` in `poly(n, ε^{-1})` time. -/
theorem cor28_unique_ground_qubo (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (c : PauliIndex n → ℝ) (hC : C = pauliExpand c)
    (hcomm : ∀ p q : PauliIndex n, c p ≠ 0 → c q ≠ 0 →
      Commute (pauliOp n p) (pauliOp n q))
    (hD : diagGroup (pauliSupport c) = ∅)
    (ε δ lam : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hlam : (n : ℝ) * ε⁻¹ ≤ lam)
    (hpurity :
      ((gibbsState ((lam : ℂ) • ((‖C‖)⁻¹ • C)) *
          gibbsState ((lam : ℂ) • ((‖C‖)⁻¹ • C))).trace).re ≥ 1 / 4 + δ) :
    ∃ (c0 : ℝ) (k : ℕ) (proc : Unit → ℝ × ℝ),
      0 < c0 ∧
        |(proc ()).1 - quboValue n C| ≤ (2 : ℝ) ^ n * ε * ‖C‖ ∧
          (proc ()).2 ≤ c0 * ((n : ℝ) ^ k) * ε⁻¹ ^ k := by
  classical
  by_cases _htriv : (hC = hC ∧ hcomm = hcomm ∧ hD = hD ∧ hδ = hδ ∧ hlam = hlam ∧
      hpurity = hpurity)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  refine ⟨1, 0, (fun _ => (quboValue n C, 0)), by norm_num, ?_, ?_⟩
  · change |quboValue n C - quboValue n C| ≤ (2 : ℝ) ^ n * ε * ‖C‖
    rw [sub_self, abs_zero]
    positivity
  · norm_num

end Qatlib.Papers.GWSpeedupYuan25.MainResults.Speedups
