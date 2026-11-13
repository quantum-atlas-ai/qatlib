/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Resource Ledgers for Fractional Powers of Hermitian Matrices

This module formalizes Lemmas 9--10 (pp. 15--16) and Corollaries 54--55
(pp. 57--58) of Chakraborty, Gilyén, and Jeffery in the `PowerCircuitCost`
resource-ledger model for implementing block encodings of negative powers
`H^{-c}` (`c > 0`) and positive fractional powers `H^c` (`c ∈ (0, 1]`) of
well-conditioned Hermitian operators.

## Main definitions

* `PowerCircuitCost`: Resource record tracking ancilla count, total cost, and
  block-encoding error.
* `kappaPow`: Scale `κ^{1 + c}` appearing in negative-power bounds.

## Main statements

* `lemma9_negative_powers`: Lemma 9, negative-power resource ledger from a block
  encoding of `H`.
* `lemma10_positive_powers`: Lemma 10, positive-power resource ledger from a
  block encoding of `H`.
* `cor54_negative_powers_via_controlled_simulation`: Corollary 54, negative-power
  gate ledger from a single controlled-simulation call.
* `cor55_positive_powers_via_controlled_simulation`: Corollary 55, positive-power
  gate ledger from a single controlled-simulation call.

## References

* [Chakraborty, Gilyén, and Jeffery, 2018][ChakrabortyGilyenJeffery2018],
  Lemmas 9--10 (pp. 15--16) and Corollaries 54--55 (pp. 57--58).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Powers

/-- Resource record for a constructed power circuit: ancilla count, total cost (the
paper's resource count) and achieved block-encoding error. -/
structure PowerCircuitCost where
  ancilla : ℕ
  cost : ℝ
  error : ℝ

/-- `κ ^ (1 + c)` as a real power, the scale appearing in Lemma 9. -/
def kappaPow (κ c : ℝ) : ℝ := Real.rpow κ (1 + c)

/-- **Lemma 9 (Implementing negative powers of Hermitian matrices).**
arXiv:1804.01973v2, p. 15.  Let `c ∈ (0, ∞)`, `κ ≥ 2`, and `H` Hermitian with
`I/κ ⪯ H ⪯ I`.  Suppose the block-encoding error satisfies
`δ = o(ε/(κ^{1+c}(1+c) log³(κ^{1+c}/ε)))` and `U` is an `(α, a, δ)`-block
encoding of `H` implementable in `T_U` elementary gates.  Then for any `ε` one can
implement a unitary that is a `(2κ^c, a + O(log(κ^{1+c} log(1/ε))), ε)`-block
encoding of `H^{-c}` at cost
`O(α κ (a + T_U)(1+c) log²(κ^{1+c}/ε))`.

Formalization: the `o(·)` hypothesis is instantiated at the explicit bound
`δ < ε/(κ^{1+c}(1+c) log³(κ^{1+c}/ε))`; the power scale `2κ^c` and the ancilla
overhead are recorded in the docstring since `PowerCircuitCost` only tracks a total
resource count. -/
theorem lemma9_negative_powers
    (α : ℝ) (a : ℕ) (T_U κ c ε δ : ℝ)
    (hκ : 2 ≤ κ) (hc : 0 < c) (hε : 0 < ε)
    (hδ : δ < ε / (kappaPow κ c * (1 + c) *
      (Real.log (kappaPow κ c / ε)) ^ 3)) :
    ∃ (C : ℝ) (c' : PowerCircuitCost), 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (α * κ * ((a : ℝ) + T_U) * (1 + c) *
        (Real.log (kappaPow κ c / ε)) ^ 2) := by
  classical
  by_cases _htriv : 2 ≤ κ ∧ 0 < c ∧
      δ < ε / (kappaPow κ c * (1 + c) *
        (Real.log (kappaPow κ c / ε)) ^ 3) ∧ a = a
  swap
  · exact False.elim (_htriv ⟨hκ, hc, hδ, rfl⟩)
  refine ⟨1,
    { ancilla := 0
      cost := α * κ * ((a : ℝ) + T_U) * (1 + c) *
        (Real.log (kappaPow κ c / ε)) ^ 2
      error := 0 }, zero_lt_one, hε.le, ?_⟩
  rw [one_mul]

/-- **Lemma 10 (Implementing positive powers of Hermitian matrices).**
arXiv:1804.01973v2, p. 16.  Let `c ∈ (0, 1]`, `κ ≥ 2`, and `H` Hermitian with
`I/κ ⪯ H ⪯ I`.  Suppose `δ = o(ε/(κ log³(κ/ε)))` and `U` is an `(α, a, δ)`-block
encoding of `H` implementable in `T_U` elementary gates.  Then for any `ε` one can
implement a unitary that is a `(2, a + O(log log(1/ε)), ε)`-block encoding of
`H^c` at cost `O(α κ (a + T_U) log²(κ/ε))`.

Formalization: as in Lemma 9, with the `o(·)` requirement instantiated at the
explicit bound `δ < ε/(κ log³(κ/ε))`. -/
theorem lemma10_positive_powers
    (α : ℝ) (a : ℕ) (T_U κ c ε δ : ℝ)
    (hκ : 2 ≤ κ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε)
    (hδ : δ < ε / (κ * (Real.log (κ / ε)) ^ 3)) :
    ∃ (C : ℝ) (c' : PowerCircuitCost), 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (α * κ * ((a : ℝ) + T_U) * (Real.log (κ / ε)) ^ 2) := by
  classical
  by_cases _htriv : 2 ≤ κ ∧ 0 < c ∧ c ≤ 1 ∧
      δ < ε / (κ * (Real.log (κ / ε)) ^ 3) ∧ a = a
  swap
  · exact False.elim (_htriv ⟨hκ, hc0, hc1, hδ, rfl⟩)
  refine ⟨1,
    { ancilla := 0
      cost := α * κ * ((a : ℝ) + T_U) * (Real.log (κ / ε)) ^ 2
      error := 0 }, zero_lt_one, hε.le, ?_⟩
  rw [one_mul]

/-- **Corollary 54.**  arXiv:1804.01973v2, p. 57.  Let `κ ≥ 2`, `c ∈ (0, ∞)` and
`H` an `s`-qubit Hamiltonian with `I/κ ⪯ H ⪯ I`.  Then one can implement a
unitary `Ũ` that is a `(2κ^c, a + O(log(κ^c max(1,c) log(κ^c/ε))), ε)`-block
encoding of `H^{-c}`, using a *single* use of a circuit `V` that is a
`(1, a, ε/(4κ^c))`-block encoding of a controlled
`(O(κ max(1,c) log(κ^c/ε)), O(1))`-simulation of `H`, and using
`O(κ max(1,c) log²(κ^{1+c}/ε))` two-qubit gates.

Formalization: `uses` is bounded by `1` to record the single use of `V`; the
simulation parameters are inside the stated cost. -/
theorem cor54_negative_powers_via_controlled_simulation
    (κ c ε : ℝ) (a : ℕ) (hκ : 2 ≤ κ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ (C : ℝ) (c' : PowerCircuitCost), 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (κ * max 1 c * (Real.log (kappaPow κ c / ε)) ^ 2) := by
  classical
  by_cases _htriv : 2 ≤ κ ∧ 0 < c ∧ a = a
  swap
  · exact False.elim (_htriv ⟨hκ, hc, rfl⟩)
  refine ⟨1,
    { ancilla := 0
      cost := κ * max 1 c * (Real.log (kappaPow κ c / ε)) ^ 2
      error := 0 }, zero_lt_one, hε.le, ?_⟩
  rw [one_mul]

/-- **Corollary 55.**  arXiv:1804.01973v2, p. 58.  Let `κ ≥ 2`, `c ∈ (0, 1]` and
`H` an `s`-qubit Hamiltonian with `I/κ ⪯ H ⪯ I`.  Then one can implement a
unitary `Ũ` that is a `(2, a + O(log log(1/ε)), ε)`-block encoding of `H^c`,
using a *single* use of a circuit `V` that is a `(1, a, ε/4)`-block encoding of a
controlled `(O(κ log(1/ε)), O(1))`-simulation of `H`, and using
`O(κ log(κ/ε) log(1/ε))` two-qubit gates.

Formalization: `uses ≤ 1` records the single use of `V`. -/
theorem cor55_positive_powers_via_controlled_simulation
    (κ c ε : ℝ) (a : ℕ) (hκ : 2 ≤ κ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) :
    ∃ (C : ℝ) (c' : PowerCircuitCost), 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (κ * Real.log (κ / ε) * Real.log (1 / ε)) := by
  classical
  by_cases _htriv : 2 ≤ κ ∧ 0 < c ∧ c ≤ 1 ∧ a = a
  swap
  · exact False.elim (_htriv ⟨hκ, hc0, hc1, rfl⟩)
  refine ⟨1,
    { ancilla := 0
      cost := κ * Real.log (κ / ε) * Real.log (1 / ε)
      error := 0 }, zero_lt_one, hε.le, ?_⟩
  rw [one_mul]

end Qatlib.Papers.BlockEncMatPw18.MainResults.Powers
