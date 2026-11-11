/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.CostModel

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — ENA algorithms via the Laplacian system (Theorems 2--4, Corollaries 1--2)

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

* **Theorem 2** (§3.2, p.15) — ENA-V (voltage) costs `O(cd³/(λ³ε²)·poly log(cd/(λε)))`;
  proof reduces Lemma 5's cost with `g = 1/(2cd)`, `κ_f = 2cd/λ` (Eq. (67)).
* **Theorem 3** (§3.2, p.17) — ENA-C (current) costs `O(c^{1.5}d^{1.5}/(λ^{1.5}ε²)·…)`;
  proof reduces Lemma 4's cost with the separated system's `g`, `κ_f`, `ε' = ε/√c`
  (Eq. (81)).
* **Corollary 1** (§3.2, p.18) — identical cost for adjacent `s,t` via Ohm's law.
* **Theorem 4** (§3.2, p.18) — ENA-P (power) costs `O(cd²/(λε)·…)`; proof reduces Lemma 3's
  cost with `κ_f = √(2cd/λ)` (Eq. (83)).
* **Corollary 2** (§3.2, p.18) — effective resistance has the same cost as Theorem 4.

The algorithmic existence is **not built**; the arithmetic reductions of the proofs are
proved (`theorem2_cost_reduction`, `theorem4_cost_reduction`), and the cost functions'
positivity / definitional equalities are proved below.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.NetworkProblems

open Qatlib.Papers.SparseNetwork13.MainResults.Model

/-- **Theorem 2 (arXiv:1311.1851v10, §3.2, p.15).**  ENA-V is solvable with
`O(cd³/(λ³ε²)·poly log(cd/(λε)))` uses of `P_v, P_e, P_i`.  Built: the reduction Eq. (67)
`d·(d g² κ_f³/ε²) = 2 c d³/(λ³ε²)` and positivity of `costTheorem2`.  Not built: the
gate-efficient ENA-V algorithm and its success-probability analysis. -/
theorem theorem2_ena_voltage_cost (c d lam eps : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlam : 0 < lam) (heps : 0 < eps) :
    costTheorem2Proof c d lam eps = 2 * costTheorem2 c d lam eps ∧
      0 < costTheorem2 c d lam eps := by
  refine ⟨theorem2_cost_reduction c d lam eps hc hd hlam heps, ?_⟩
  unfold costTheorem2
  positivity

/-- **Theorem 3 (arXiv:1311.1851v10, §3.2, p.17).**  ENA-C is solvable with
`O(c^{1.5}d^{1.5}/(λ^{1.5}ε²)·poly log(cd/(λε)))` uses of `P_v, P_e, P_i`.  Built: the
leading cost function `costTheorem3` and positivity.  Not built: the algorithm (uses
Lemma 6's separated system `A = [[0,C_G],[C_Gᵀ,0]]` and Lemma 4). -/
theorem theorem3_ena_current_cost (c d lam eps : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlam : 0 < lam) (heps : 0 < eps) :
    0 < costTheorem3 c d lam eps := by
  unfold costTheorem3
  positivity

/-- **Corollary 1 (arXiv:1311.1851v10, §3.2, p.18).**  For adjacent `s, t`, ENA-V costs the
same as ENA-C (Theorem 3): by Ohm's law `|v(s)−v(t)| = |i(e)|/w_e`, converting a current
estimate to a voltage estimate costs nothing extra.  Built: the cost equality
`costCorollary1 = costTheorem3` and positivity.  Not built: the algorithm. -/
theorem corollary1_adjacent_voltage_cost (c d lam eps : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlam : 0 < lam) (heps : 0 < eps) :
    costCorollary1 c d lam eps = costTheorem3 c d lam eps ∧
      0 < costCorollary1 c d lam eps := by
  refine ⟨rfl, ?_⟩
  unfold costCorollary1
  exact theorem3_ena_current_cost c d lam eps hc hd hlam heps

/-- **Theorem 4 (arXiv:1311.1851v10, §3.2, p.18).**  ENA-P is solvable with
`O(cd²/(λε)·poly log(cd/(λε)))` uses of `P_v, P_e, P_i`.  Built: the reduction Eq. (83)
`d·κ_f²/ε = 2cd²/(λε)` and positivity of `costTheorem4`.  Not built: the algorithm (uses
Lemma 3 on the separated system, since `‖x` = `E(i)`). -/
theorem theorem4_ena_power_cost (c d lam eps : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlam : 0 < lam) (heps : 0 < eps) :
    costTheorem4Proof c d lam eps = costTheorem4 c d lam eps ∧
      0 < costTheorem4 c d lam eps := by
  refine ⟨theorem4_cost_reduction c d lam eps hc hd hlam heps, ?_⟩
  unfold costTheorem4
  positivity

/-- **Corollary 2 (arXiv:1311.1851v10, §3.2, p.18).**  ENA-ER (effective resistance) costs the
same as ENA-P (Theorem 4); the proof's extra factor `2` (from `E(i) = 2E(i/√2)`) is a
downstream multiplicative constant on the output.  Built: the cost equality
`costCorollary2 = costTheorem4` and positivity.  Not built: the algorithm. -/
theorem corollary2_effective_resistance_cost (c d lam eps : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hlam : 0 < lam) (heps : 0 < eps) :
    costCorollary2 c d lam eps = costTheorem4 c d lam eps ∧
      0 < costCorollary2 c d lam eps := by
  refine ⟨rfl, ?_⟩
  unfold costCorollary2
  exact (theorem4_ena_power_cost c d lam eps hc hd hlam heps).2

end Qatlib.Papers.SparseNetwork13.MainResults.NetworkProblems
