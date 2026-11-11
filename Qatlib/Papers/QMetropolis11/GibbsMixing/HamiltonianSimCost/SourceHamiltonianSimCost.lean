/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Hamiltonian-simulation gate count (Temme et al. 2011, Sec. 5, Eq. (63))

Fixed source: arXiv:0911.3635v2, Section 5, printed page 20, Eq. (63).

The paper quotes (restates) the simulation cost of Berry et al. [19] and
Childs [31]: to simulate `e^{-iHt}` for a `k`-particle Hamiltonian written as
a sum of `s` terms, to error `ε_H` and time `t ≤ t₀`, a circuit of length

`T_H = c · s² · t₀ · N · (log₂*(N))² · 9^{√(log₂*(s t₀ / ε_H))}`        (63)

suffices, where `N` is the dimension and `log₂*` the iterated base-2
logarithm.  This is explicitly a citation, not a contribution of the present
paper: the mathematical content (the algorithm and its cost analysis) belongs
to the Hamiltonian-simulation line of the library.

We therefore do not restate the algorithm.  We define the right-hand side of
(63) as `hamiltonianSimGateCount` (taking the log-star value `L` as an
explicit parameter, since the iterated logarithm is not formalised here), and
prove that the cost is positive and factors as `(c s² t₀) · (N L² 9^{√L})`,
which is the "linear in `t₀`, polynomial in `s`, almost-linear in `N`"
reading the paper extracts from (63).  The existence of a circuit achieving
this count is the imported [19]/[31] result and is recorded in the docstring,
not asserted.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.HamiltonianSimCost

/-- The gate count `T_H` of Eq. (63), with the log-star value supplied as the
parameter `L = log₂*(s t₀ / ε_H)`. -/
noncomputable def hamiltonianSimGateCount (c s t0 N L : ℝ) : ℝ :=
  c * s ^ 2 * t0 * N * L ^ 2 * (9 : ℝ) ^ Real.sqrt L

/-- **c011, Eq. (63).**  For positive constants and `L ≥ 1`, the circuit
length (63) is strictly positive.  This is the well-definedness part of the
quoted simulation cost. -/
theorem source_hamiltonian_simulation_cost (c s t0 N L εH : ℝ)
    (hc : 0 < c) (hs : 0 < s) (ht0 : 0 < t0) (hN : 0 < N) (_hεH : 0 < εH)
    (hL : 1 ≤ L) :
    ∃ T_H : ℝ, T_H = hamiltonianSimGateCount c s t0 N L ∧ 0 < T_H := by
  refine ⟨hamiltonianSimGateCount c s t0 N L, rfl, ?_⟩
  unfold hamiltonianSimGateCount
  have h9 : (0 : ℝ) < (9 : ℝ) ^ Real.sqrt L :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hL2 : 0 < L ^ 2 := by positivity
  positivity

/-- **c011, Eq. (63), cost decomposition.**  The gate count factors into the
system-independent prefactor `c s² t₀` and the size/precision factor
`N L² 9^{√L}`.  This is the form used in the paper's discussion: linear in
`t₀`, quadratic in `s`, and almost linear in `N`. -/
theorem source_hamiltonian_simulation_cost_factor (c s t0 N L : ℝ) :
    hamiltonianSimGateCount c s t0 N L =
      (c * s ^ 2 * t0) * (N * L ^ 2 * (9 : ℝ) ^ Real.sqrt L) := by
  unfold hamiltonianSimGateCount
  ring

end Qatlib.Papers.QMetropolis11.GibbsMixing.HamiltonianSimCost
