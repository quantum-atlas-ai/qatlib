/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeSVP13.MainResults.SieveQuantum.Lemma4QuantumSieve

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1: quantum sieving time and space

Laarhoven--Mosca--van de Pol, fixed arXiv:1301.6176v1 (25 Jan 2013), Theorem 1, p. 7,
and Appendix A, p. 16.

> **Theorem 1.** On a quantum computer, assuming that Heuristic 1 holds, Algorithm 1
> will return a shortest vector of a lattice in time `2 ^ (0.312 n + o(n))` and space
> `2 ^ (0.208 n + o(n))`.

This is Lemma 4 (`lemma4_quantum_sieve`) specialised to the optimal geometric factor
`γ → 1`.  At `γ = 1` the exponent of Equation (1) is `c_h(1) = ½ log₂(4/3)`, and the
paper's numerical bounds are `(3/2) c_h(1) ≤ 0.312` and `c_h(1) ≤ 0.208`; both are
proved here from the Taylor lower bound `log₂(4/3) ≤ 0.416` in `ExponentCore`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LatticeSVP13.MainResults.SieveQuantum

open Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore

/-- At the optimal geometric factor `γ = 1`, Equation (1) becomes `c_h(1) = ½ log₂(4/3)`:
`log₂ 1 = 0` and `1 - 1²/4 = (4/3)⁻¹`, so `log₂(4/3)⁻¹ = -log₂(4/3)`. -/
theorem cH_one_eq : cH 1 = (1 / 2) * Real.logb 2 (4 / 3) := by
  unfold cH
  have harg : (1 : ℝ) - 1 ^ 2 / 4 = (4 / 3)⁻¹ := by norm_num
  rw [harg, Real.logb_inv]
  rw [show Real.logb 2 (1 : ℝ) = 0 from Real.logb_one]
  ring

/-- **Theorem 1** (arXiv:1301.6176v1, p. 7).  With the sieve lists of Lemma 4 evaluated
at `γ = 1`, the quantum time cost is `2 ^ (0.312 n + o(n))` and the space cost is
`2 ^ (0.208 n + o(n))`.

The `return a shortest vector` clause is Heuristic 1 of the paper (imported from [41,
Lemma 1]); the theorem here proves the concrete exponents `0.312` and `0.208`. -/
theorem theorem1_heuristic_quantum
    (S C T : ℕ → ℝ)
    (hS : HasLog2Exponent (fun n => Real.logb 2 (S n)) (cH 1))
    (hC : HasLog2Exponent (fun n => Real.logb 2 (C n)) (cH 1))
    (hSp : ∀ n, 0 < S n) (hCp : ∀ n, 0 < C n)
    (hT : ∀ n, T n = S n * Real.sqrt (C n)) :
    HasLog2Exponent (fun n => Real.logb 2 (T n)) 0.312 ∧
    HasLog2Exponent (fun n => Real.logb 2 (S n + C n)) 0.208 := by
  have h4 := lemma4_quantum_sieve S C T 1 hS hC hSp hCp hT
  have hspace : cH 1 ≤ 0.208 := by
    rw [cH_one_eq]
    linarith [logb_two_four_thirds_le]
  have htime : (3 / 2) * cH 1 ≤ 0.312 := by
    rw [cH_one_eq]
    linarith [logb_two_four_thirds_le]
  exact ⟨h4.1.mono_coeff htime, h4.2.mono_coeff hspace⟩

end Qatlib.Papers.LatticeSVP13.MainResults.SieveQuantum
