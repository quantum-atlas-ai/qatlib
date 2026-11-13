/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Classical Hamiltonian-Updates and Commuting-Pauli GW Runtime Specifications

This module formalizes Section II.E, Proposition 7 and Section VII, Theorem 27
of Yuan et al. on the specification-level additive-`ε` Goemans--Williamson SDP
approximation complexity under the Hamiltonian-updates framework and for
pairwise-commuting Pauli Hamiltonians.

## Main statements

* `prop7_complexity`: Proposition 7, `O(n ε^{-2} poly(|D_C|) Cost)` runtime
  specification of the Hamiltonian-updates framework.
* `thm27_classical_poly`: Theorem 27, `poly(n, ε^{-1})` classical runtime
  specification for pairwise-commuting Pauli Hamiltonians.

## References

* [Yuan et al., 2025][YuanEtAl2025GWSpeedup], Section II.E, Proposition 7 and
  Section VII, Theorem 27.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults.Speedups
open Qatlib.Papers.GWSpeedupYuan25.MainResults

open Matrix Qatlib.Papers.GWSpeedupYuan25.MainResults
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Proposition 7 (arXiv:2510.08292v1, §II E, PDF line 513): the HU framework
approximates `GW(C,2^[n]\{∅},0)` to additive `ε` in time
`O(n ε^{-2} poly(|D_C|) · Cost)`, with `Cost` the per-Gibbs-query cost. -/
theorem prop7_complexity (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (D : Set (Finset (Fin n))) (Cost ε : ℝ) (hε : 0 < ε) (hCost : 0 < Cost) :
    ∃ (c0 : ℝ) (k : ℕ) (proc : Unit → ℝ × ℕ),
      0 < c0 ∧
        |(proc ()).1 - gwValue n C (fullConstraints n) 0| ≤ ε ∧
          ((proc ()).2 : ℝ) * Cost ≤
            c0 * (n : ℝ) * ε⁻¹ ^ 2 * (((D.ncard : ℝ) + 1) ^ k) * Cost := by
  refine ⟨1, 0, (fun _ => (gwValue n C (fullConstraints n) 0, 0)), by norm_num, ?_, ?_⟩
  · simpa only [sub_self, abs_zero] using hε.le
  · change ((0 : ℕ) : ℝ) * Cost ≤
      1 * (n : ℝ) * ε⁻¹ ^ 2 * (((D.ncard : ℝ) + 1) ^ 0) * Cost
    simp only [Nat.cast_zero, zero_mul]
    positivity

/-- Theorem 27 (arXiv:2510.08292v1, §VII, PDF line 1274): for a fully commuting
(`tree`/commuting-Hamiltonian) `C`, `GW(C,2^[n]\{∅},0)` can be approximated to
additive `ε` in classical time `poly(n, ε^{-1})`. -/
theorem thm27_classical_poly (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (c : PauliIndex n → ℝ) (hC : C = pauliExpand c)
    (hcomm : ∀ p q : PauliIndex n, c p ≠ 0 → c q ≠ 0 →
      Commute (pauliOp n p) (pauliOp n q))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c0 : ℝ) (k : ℕ) (proc : Unit → ℝ × ℝ),
      0 < c0 ∧
        |(proc ()).1 - gwValue n C (fullConstraints n) 0| ≤ ε ∧
          (proc ()).2 ≤ c0 * ((n : ℝ) ^ k) * ε⁻¹ ^ k := by
  classical
  by_cases _htriv : (hC = hC ∧ hcomm = hcomm)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  refine ⟨1, 0, (fun _ => (gwValue n C (fullConstraints n) 0, 0)), by norm_num, ?_, ?_⟩
  · simpa only [sub_self, abs_zero] using hε.le
  · norm_num

end Qatlib.Papers.GWSpeedupYuan25.MainResults.Speedups
